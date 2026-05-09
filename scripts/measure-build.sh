#!/usr/bin/env bash
# Compile the project, time the build, and report errors and `sorry` counts.
#
# Outputs a human-readable summary on stdout and a machine-readable
# `build-report.json` in the repo root. Intended as the build-time signal
# for the autoresearch loop.
#
# Usage: scripts/measure-build.sh [--clean] [--quiet]
#   --clean   wipe the project's own build artifacts (.lake/build) before
#             building, so the project is recompiled from scratch. Mathlib's
#             cached oleans (under .lake/packages/.../.lake/build) are
#             preserved.
#   --quiet   suppress the streamed lake build output; only print the summary.
#
# Exit code: forwards lake build's exit status (0 on success).

set -uo pipefail

clean=false
quiet=false
for arg in "$@"; do
  case "$arg" in
    --clean) clean=true ;;
    --quiet) quiet=true ;;
    -h|--help)
      sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) echo "unknown arg: $arg" >&2; exit 2 ;;
  esac
done

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

if ! command -v lake >/dev/null 2>&1; then
  echo "error: 'lake' not found on PATH. Install elan and run 'elan default leanprover/lean4:v4.29.1'." >&2
  exit 127
fi

if $clean; then
  echo "[measure-build] cleaning .lake/build (Mathlib cache preserved)"
  rm -rf .lake/build
fi

log_file="$(mktemp -t lake-build.XXXXXX.log)"
trap 'rm -f "$log_file"' EXIT

echo "[measure-build] running 'lake build' (log: $log_file)"
start_ns=$(date +%s%N)
if $quiet; then
  lake build >"$log_file" 2>&1
  status=$?
else
  set -o pipefail
  lake build 2>&1 | tee "$log_file"
  status=${PIPESTATUS[0]}
fi
end_ns=$(date +%s%N)

elapsed_s=$(awk "BEGIN { printf \"%.3f\", ($end_ns - $start_ns) / 1e9 }")

# Parse build log
# - Lean error lines start with "error:". This includes the umbrella
#   "error: Lean exited with code 1" and "error: build failed", so the raw
#   count overcounts vs. distinct source-level errors. We surface both.
errors_raw=$(grep -c '^error:' "$log_file" 2>/dev/null || true)
errors_source=$(grep -cE '^error: [^[:space:]].*\.lean:' "$log_file" 2>/dev/null || true)
sorry_warnings=$(grep -c "declaration uses .sorry." "$log_file" 2>/dev/null || true)

# Source-level sorry count (informational; includes `sorry` tokens in comments).
mapfile -t lean_files < <(find Hackathon -name '*.lean' -type f | sort)
total_src_sorry=0
declare -a per_file_lines=()
for f in "${lean_files[@]}"; do
  c=$(grep -c '\bsorry\b' "$f" 2>/dev/null || true)
  total_src_sorry=$((total_src_sorry + c))
  per_file_lines+=("$f"$'\t'"$c")
done

# Build JSON via python (handles escaping correctly).
python3 - "$status" "$elapsed_s" "$errors_raw" "$errors_source" \
                    "$sorry_warnings" "$total_src_sorry" "$clean" \
                    "${per_file_lines[@]}" <<'PY' > build-report.json
import json, sys, datetime
status, elapsed, errors_raw, errors_source, sorry_warns, src_sorry, clean = sys.argv[1:8]
per_file = {}
for entry in sys.argv[8:]:
    path, count = entry.split("\t")
    per_file[path] = int(count)
print(json.dumps({
    "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
    "clean_build": clean == "true",
    "exit_status": int(status),
    "success": int(status) == 0,
    "elapsed_seconds": float(elapsed),
    "errors_raw": int(errors_raw),
    "errors_source": int(errors_source),
    "sorry_warnings": int(sorry_warns),
    "sorry_in_source_total": int(src_sorry),
    "sorry_per_file": per_file,
}, indent=2))
PY

# Human-readable summary
status_label=$([ "$status" -eq 0 ] && echo "OK" || echo "FAIL")
echo
echo "============================================"
echo "  Build report"
echo "============================================"
printf "  Exit status        : %s (%s)\n" "$status" "$status_label"
printf "  Clean build        : %s\n" "$clean"
printf "  Elapsed time       : %s s\n" "$elapsed_s"
printf "  Source errors      : %s\n" "$errors_source"
printf "  Total error lines  : %s   (includes 'build failed' umbrella)\n" "$errors_raw"
printf "  Sorry warnings     : %s   (from build output)\n" "$sorry_warnings"
printf "  Sorry in source    : %s   (raw token count, informational)\n" "$total_src_sorry"
echo "--------------------------------------------"
echo "  Per-file sorry counts:"
for line in "${per_file_lines[@]}"; do
  IFS=$'\t' read -r path count <<<"$line"
  if [ "$count" -gt 0 ]; then
    printf "    %4d  %s\n" "$count" "$path"
  fi
done
echo "--------------------------------------------"
echo "  Full build log:  $log_file"
echo "  JSON report:     build-report.json"
echo "============================================"

exit "$status"
