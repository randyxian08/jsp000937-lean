#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export PATH="$HOME/.elan/bin:$PATH"
lake env lean --version
lake exe cache get
lake build Erdos1153.JSPInterpolation.Logarithmic Erdos1153.JSPInterpolation.Regression Erdos1153.JSPInterpolation.JSP958
lake env lean Audit937.lean
lake env lean AuditFull.lean 2>&1 | tee verification-axioms.log
python3 tools/check_axioms.py verification-axioms.log
if grep -R -n -E --include='*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit|sorryAx|native_decide|implemented_by)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe|opaque)[[:space:]]' \
  Erdos1153 Erdos1153.lean Audit937.lean AuditFull.lean; then
  echo 'Source trust scan failed' >&2
  exit 1
fi
echo 'FULL TARGET937 (CLASSIFICATION AND LOGARITHMIC BOUND) PASSED.'
