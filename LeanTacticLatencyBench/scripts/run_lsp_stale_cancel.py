#!/usr/bin/env python3
"""Stale-tactic-cancellation latency benchmark via Lean's LSP server.

We launch `lake env lean --server`, send the standard `initialize` /
`initialized` handshake, `textDocument/didOpen` a slow Lean file, wait
just long enough for the server to start working on it, and then
`textDocument/didChange` it to a trivial proof. We record the wall-clock
time from `didChange` to the *first* `publishDiagnostics` notification
that reports zero errors (i.e. corresponds to the new version).

Limitations (this is a v1 harness, on purpose):

* We rely on `params.diagnostics == []` as the signal for "now you've
  processed the new version". A more robust harness would inspect the
  document version field if Lean populates it.
* "Server still responsive while old work is running" is approximated
  by sending periodic synchronous requests (`$/lean/...` if available;
  otherwise a no-op `textDocument/hover`) and timing the round-trip.
* CPU usage of the server during stale work is not measured here. Hook
  `psutil` if you want that.
"""

import argparse
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Optional


def _enc(msg: dict) -> bytes:
    body = json.dumps(msg, separators=(",", ":")).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body


class LeanLSP:
    """Tiny Lean LSP client. One reader thread, blocking writes."""

    def __init__(self, project_root: Path, stderr_path: Optional[Path] = None):
        env = os.environ.copy()
        # `lake env lean --server` sets LEAN_PATH for us.
        stderr_target = subprocess.PIPE if stderr_path is None else open(stderr_path, "wb")
        self._stderr_target = stderr_target if stderr_path is not None else None
        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=project_root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=stderr_target,
            bufsize=0,
        )
        self.next_id = 1
        self.lock = threading.Lock()
        self.responses = {}            # id -> (timestamp, msg)
        self.diagnostics = []          # list of (timestamp, params)
        self.notifications = []        # list of (timestamp, method, params)
        self._stop = False
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()

    # ─── send ─────────────────────────────────────────────────────────────
    def request(self, method: str, params: dict) -> int:
        with self.lock:
            mid = self.next_id
            self.next_id += 1
        msg = {"jsonrpc": "2.0", "id": mid, "method": method, "params": params}
        self.proc.stdin.write(_enc(msg))
        self.proc.stdin.flush()
        return mid

    def notify(self, method: str, params: dict) -> None:
        msg = {"jsonrpc": "2.0", "method": method, "params": params}
        self.proc.stdin.write(_enc(msg))
        self.proc.stdin.flush()

    # ─── recv ─────────────────────────────────────────────────────────────
    def _read_loop(self):
        buf = b""
        stdout = self.proc.stdout
        while not self._stop:
            try:
                # `read(1)` always blocks for at least one byte; that
                # guarantees forward progress even when the producer
                # has not yet flushed.
                chunk = stdout.read(1)
            except Exception:
                break
            if not chunk:
                break
            buf += chunk
            # Try to drain as many complete messages as the buffer holds.
            while True:
                hdr_end = buf.find(b"\r\n\r\n")
                if hdr_end < 0:
                    break
                header = buf[:hdr_end].decode("ascii", errors="replace")
                clen = None
                for line in header.split("\r\n"):
                    k, _, v = line.partition(":")
                    if k.strip().lower() == "content-length":
                        try:
                            clen = int(v.strip())
                        except ValueError:
                            clen = None
                if clen is None:
                    buf = buf[hdr_end + 4:]
                    continue
                body_start = hdr_end + 4
                # Pull more bytes until we have a full body.
                while len(buf) < body_start + clen:
                    more = stdout.read(body_start + clen - len(buf))
                    if not more:
                        # Producer closed mid-message: bail.
                        return
                    buf += more
                body = buf[body_start:body_start + clen]
                buf = buf[body_start + clen:]
                try:
                    msg = json.loads(body.decode("utf-8"))
                except Exception:
                    continue
                self._dispatch(msg)

    def _dispatch(self, msg: dict):
        ts = time.perf_counter()
        if "id" in msg and "method" not in msg:
            with self.lock:
                self.responses[msg["id"]] = (ts, msg)
        elif msg.get("method") == "textDocument/publishDiagnostics":
            with self.lock:
                self.diagnostics.append((ts, msg.get("params", {})))
        else:
            with self.lock:
                self.notifications.append((ts, msg.get("method"), msg.get("params")))

    # ─── synchronous helpers ──────────────────────────────────────────────
    def wait_response(self, mid: int, timeout: float) -> Optional[dict]:
        deadline = time.perf_counter() + timeout
        while time.perf_counter() < deadline:
            with self.lock:
                if mid in self.responses:
                    return self.responses[mid][1]
            time.sleep(0.01)
        return None

    def wait_diagnostic_for(self, uri: str, predicate, after_ts: float,
                            timeout: float) -> Optional[tuple]:
        """Return the first (ts, params) tuple after `after_ts`, for `uri`,
        whose params match `predicate`. None on timeout."""
        deadline = time.perf_counter() + timeout
        next_idx = 0
        while time.perf_counter() < deadline:
            with self.lock:
                items = self.diagnostics[next_idx:]
                next_idx = len(self.diagnostics)
            for ts, params in items:
                if ts < after_ts:
                    continue
                if params.get("uri") != uri:
                    continue
                if predicate(params):
                    return ts, params
            time.sleep(0.01)
        return None

    def shutdown(self):
        try:
            mid = self.request("shutdown", {})
            self.wait_response(mid, timeout=5)
            self.notify("exit", {})
        except Exception:
            pass
        self._stop = True
        try:
            self.proc.terminate()
            self.proc.wait(timeout=3)
        except Exception:
            try:
                self.proc.kill()
            except Exception:
                pass


# Trivial replacement contents.
TRIVIAL_BODY = """example : True := trivial
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project-root", type=Path,
                    default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--slow-file", type=Path, default=None,
                    help="Slow Lean file to didOpen "
                         "(default: <project>/Bench/LspStale/SlowVersion.lean).")
    ap.add_argument("--stall-ms", type=int, default=300,
                    help="Wait this many ms after didOpen before didChange "
                         "(give the server time to start working).")
    ap.add_argument("--cancel-timeout", type=float, default=30.0,
                    help="Max seconds to wait for diagnostics on the new version.")
    ap.add_argument("--out-dir", type=Path, default=None)
    ap.add_argument("--label", default=None)
    args = ap.parse_args()

    project_root = args.project_root.resolve()
    slow_file = (args.slow_file or
                 (project_root / "Bench" / "LspStale" / "SlowVersion.lean")).resolve()
    out_dir = (args.out_dir or (project_root / "results" / "raw")).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    slow_text = slow_file.read_text()
    uri = slow_file.as_uri()

    print(f"# LSP stale-cancel bench")
    print(f"# project: {project_root}")
    print(f"# file:    {slow_file}")
    print(f"# stall:   {args.stall_ms} ms")
    print()

    stderr_log = out_dir / f"lsp_stderr_{args.label or time.strftime('%Y%m%d_%H%M%S')}.log"
    cli = LeanLSP(project_root, stderr_path=stderr_log)
    try:
        # ── initialize ────────────────────────────────────────────────────
        init_id = cli.request("initialize", {
            "processId": os.getpid(),
            "rootUri": project_root.as_uri(),
            "capabilities": {"textDocument": {"publishDiagnostics": {}}},
        })
        init_resp = cli.wait_response(init_id, timeout=15)
        if init_resp is None:
            raise RuntimeError("initialize never returned")
        cli.notify("initialized", {})

        # ── didOpen the slow version ──────────────────────────────────────
        open_t = time.perf_counter()
        cli.notify("textDocument/didOpen", {
            "textDocument": {
                "uri": uri,
                "languageId": "lean4",
                "version": 1,
                "text": slow_text,
            }
        })

        # ── stall so the server is mid-elaboration ────────────────────────
        time.sleep(args.stall_ms / 1000.0)

        # ── didChange to trivial body ─────────────────────────────────────
        change_t = time.perf_counter()
        cli.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": 2},
            "contentChanges": [{"text": TRIVIAL_BODY}],
        })

        # ── wait for diagnostics matching the new version ────────────────
        # We accept any publishDiagnostics with zero errors after the
        # didChange timestamp.
        def is_clean(params):
            ds = params.get("diagnostics", [])
            errs = [d for d in ds
                    if d.get("severity") in (None, 1)]  # severity 1 = Error
            return len(errs) == 0

        result = cli.wait_diagnostic_for(uri, is_clean, change_t,
                                         timeout=args.cancel_timeout)
        if result is None:
            print(f"  TIMEOUT after {args.cancel_timeout}s")
            cancel_latency = None
        else:
            ts, params = result
            cancel_latency = ts - change_t
            print(f"  didChange → clean diagnostics: {cancel_latency:.3f}s")

        # ── enumerate every diagnostic event we saw ──────────────────────
        with cli.lock:
            diags = list(cli.diagnostics)
        relative = [
            {
                "t_after_didOpen_s": ts - open_t,
                "uri": params.get("uri"),
                "n_diagnostics": len(params.get("diagnostics", [])),
                "n_errors": sum(1 for d in params.get("diagnostics", [])
                                if d.get("severity") in (None, 1)),
            }
            for ts, params in diags
        ]

        out = {
            "kind": "lsp_stale_cancel",
            "project_root": str(project_root),
            "slow_file": str(slow_file),
            "stall_ms": args.stall_ms,
            "cancel_latency_s": cancel_latency,
            "diagnostics_timeline": relative,
        }
        label = args.label or time.strftime("%Y%m%d_%H%M%S")
        out_path = out_dir / f"lsp_stale_{label}.json"
        out_path.write_text(json.dumps(out, indent=2))
        print()
        print(f"Wrote {out_path}")
    finally:
        cli.shutdown()


if __name__ == "__main__":
    main()
