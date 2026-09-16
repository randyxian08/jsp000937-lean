import re, sys
from pathlib import Path
text = Path(sys.argv[1]).read_text()
expected = {'JSPFreeNodes.jsp_000936', 'JSPFreeNodes.jsp_000937',
 'JSPFreeNodes.jsp_000937_logarithmic', 'JSPInterpolation.jsp_000958',
 'JSPInterpolation.jsp_000958_maximum', 'JSPFreeNodes.canonical_allMinPeak_eq_one'}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
seen = {n: {a.strip() for a in axes.split(',') if a.strip()}
 for n, axes in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S)}
for n in re.findall(r"'([^']+)' does not depend on any axioms", text):
 seen[n] = set()
if expected - seen.keys(): raise SystemExit('Missing theorem reports: ' + str(expected - seen.keys()))
if any(axes - allowed for axes in seen.values()): raise SystemExit('Unexpected axiom dependencies')
print('All expected theorem axiom reports passed.')
