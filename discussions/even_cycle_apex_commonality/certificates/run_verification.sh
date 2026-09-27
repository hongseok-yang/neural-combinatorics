#!/bin/sh
# Exact arithmetic replays for files extracted from the standalone source.
# This does not run Lean and makes no claim of Lean proof compilation.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PYTHON=${PYTHON:-python3}
cd "$ROOT"
"$PYTHON" verify_six_vertex.py
"$PYTHON" verify_algebra.py
"$PYTHON" independent_audit.py --certificates "$ROOT"
printf '%s\n' 'PASS: standalone arithmetic replays. No Lean proof was compiled.'
