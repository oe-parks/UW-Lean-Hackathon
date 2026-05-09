#!/usr/bin/env bash
# Serve the blossom visualizer locally via Python's built-in HTTP server.
#
# Usage:
#   ./serve.sh                   # http://127.0.0.1:8000  (local only)
#   ./serve.sh -p 8080           # custom port
#   ./serve.sh --public          # bind 0.0.0.0 (LAN / public)
#   ./serve.sh --public -p 8080  # both
#   ./serve.sh -h                # help

set -euo pipefail

PORT=8000
BIND=127.0.0.1
OPEN_BROWSER=1

usage() {
  sed -n '2,9p' "$0" | sed 's/^# \?//'
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -p|--port)    PORT="$2"; shift 2 ;;
    --public)     BIND=0.0.0.0; shift ;;
    --no-open)    OPEN_BROWSER=0; shift ;;
    -h|--help)    usage; exit 0 ;;
    *)            echo "unknown arg: $1" >&2; usage >&2; exit 2 ;;
  esac
done

# Pick a Python.
if command -v python3 >/dev/null 2>&1; then
  PY=python3
elif command -v python >/dev/null 2>&1; then
  PY=python
else
  echo "error: python3 not found. Install Python 3 or use any other static server." >&2
  exit 1
fi

# Resolve the script's own directory so it works no matter where it's invoked from.
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$SCRIPT_DIR"

URL="http://${BIND}:${PORT}/"
DISPLAY_URL="$URL"
if [[ "$BIND" == "0.0.0.0" ]]; then
  DISPLAY_URL="http://localhost:${PORT}/  (or your machine's LAN/public IP)"
fi

echo "Serving $SCRIPT_DIR"
echo "→ $DISPLAY_URL"
echo "Press Ctrl-C to stop."
echo

# Try to open a browser unless suppressed or binding non-local.
if [[ $OPEN_BROWSER -eq 1 && "$BIND" == "127.0.0.1" ]]; then
  ( sleep 0.5
    if command -v xdg-open >/dev/null 2>&1;     then xdg-open  "$URL" >/dev/null 2>&1 || true
    elif command -v open >/dev/null 2>&1;       then open      "$URL" >/dev/null 2>&1 || true
    elif command -v start >/dev/null 2>&1;      then start     "$URL" >/dev/null 2>&1 || true
    fi
  ) &
fi

exec "$PY" -m http.server "$PORT" --bind "$BIND"
