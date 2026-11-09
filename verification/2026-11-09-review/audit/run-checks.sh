#!/bin/sh
set -eu
cd /project
# Run only after successful clean build of the unmodified pinned source.
cp /audit/Specification.lean.txt Erdos1153/Review937Specification.lean
cp /audit/Review937.lean.txt Erdos1153/Review937.lean
/opt/lean/bin/lake build +Erdos1153.Review937
python3 /tool/scripts/audit.py preflight /audit/targets.json --out /audit/preflight-01
python3 /tool/scripts/audit.py run /audit/targets.json --out /audit/check-01 --lake /opt/lean/bin/lake --timeout 300
/opt/lean/bin/lake env lean Audit937.lean > /logs/audit937.log 2>&1
/opt/lean/bin/lake env lean AuditFull.lean > /logs/audit-full.log 2>&1
python3 tools/check_axioms.py /logs/audit-full.log
/opt/lean/bin/lake env leanchecker Erdos1153.JSPInterpolation.Logarithmic > /logs/leanchecker.log 2>&1
printf '\nADDITIONAL_CHECKS_EXIT=0\n'
