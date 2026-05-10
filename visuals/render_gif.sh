#!/usr/bin/env bash
# Render augmenting.py as a GIF suitable for embedding in README.md.
# Output: visuals/augmenting_path_manim.gif
#
# Usage: bash visuals/render_gif.sh [--low | --high]
#   --low   480p 15fps (faster render, smaller file)
#   --high  1080p 30fps (slower render, larger file)
#   default: 720p 20fps

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
MANIM="$SCRIPT_DIR/../manim-env/bin/manim"
OUTPUT_GIF="$SCRIPT_DIR/augmenting_path_manim.gif"

quality="-ql"   # 480p
fps=20

case "${1:-}" in
  --low)  quality="-ql"; fps=15 ;;
  --high) quality="-qh"; fps=30 ;;
  "")     quality="-qm"; fps=20 ;;
esac

echo "[render] quality=$quality fps=$fps"
echo "[render] source: $SCRIPT_DIR/augmenting.py"

"$MANIM" render \
  --format gif \
  --frame_rate "$fps" \
  "$quality" \
  --output_file augmenting_path_manim \
  "$SCRIPT_DIR/augmenting.py" \
  AugmentingPath

# Manim drops the GIF into media/videos/.../; find and move it here.
GENERATED=$(find "$SCRIPT_DIR/media/videos" -name "augmenting_path_manim*.gif" \
  -newer "$SCRIPT_DIR/augmenting.py" 2>/dev/null | sort | tail -1)

if [ -n "$GENERATED" ]; then
  mv "$GENERATED" "$OUTPUT_GIF"
  echo "[render] saved → $OUTPUT_GIF  ($(du -sh "$OUTPUT_GIF" | cut -f1))"
else
  echo "[render] GIF already in place or manim wrote it directly."
fi
