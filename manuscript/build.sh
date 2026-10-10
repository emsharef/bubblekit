#!/usr/bin/env bash
# Build the manuscript from its LaTeX sources and existing research results.
set -euo pipefail
manuscript_dir="$(cd "$(dirname "$0")" && pwd)"
repo_dir="$(dirname "$manuscript_dir")"
python_bin="${MANUSCRIPT_PYTHON:-$repo_dir/.venv/bin/python}"
if [[ ! -x "$python_bin" ]]; then python_bin=python3; fi
cd "$manuscript_dir"
mkdir -p build generated
"$python_bin" prepare.py
tectonic --keep-logs --keep-intermediates --outdir build main.tex > build/tectonic.log 2>&1 || {
  tail -60 build/tectonic.log
  exit 1
}
"$python_bin" check.py
echo "Built $manuscript_dir/build/main.pdf"
