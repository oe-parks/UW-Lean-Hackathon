#!/usr/bin/env bash
# Start the LeanTacticLatencyBench web UI on 0.0.0.0:8000.
#
# Usage:
#   ./web/serve.sh               # foreground, bound 0.0.0.0:8000
#   ./web/serve.sh --port 9000   # custom port
#   ./web/serve.sh --bg          # detach (writes ./web/server.log + ./web/server.pid)
#
# Env vars honored:
#   ALLOW_LLM_AGENTS=0       — disable llm_* agents (default: enabled).

set -euo pipefail
cd "$(dirname "$0")/.."

BG=0
ARGS=()
for arg in "$@"; do
  case "$arg" in
    --bg) BG=1 ;;
    *) ARGS+=("$arg") ;;
  esac
done

if [[ $BG -eq 1 ]]; then
  nohup python3 web/server.py "${ARGS[@]}" >web/server.log 2>&1 &
  echo $! >web/server.pid
  sleep 0.3
  echo "Started (pid $(cat web/server.pid)) — log: web/server.log"
else
  exec python3 web/server.py "${ARGS[@]}"
fi
