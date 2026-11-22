#!/usr/bin/env bash
set -euo pipefail
export OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")"
python verify_v6.py
python static_star_v6.py
python compare_invariants_v6.py
python vacuum_series_v6.py
python audit_v6.py
