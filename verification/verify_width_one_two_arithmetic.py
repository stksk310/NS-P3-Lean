"""Finite arithmetic checks for width_one_two_compact.tex (stdlib only)."""

from contextlib import redirect_stdout
from io import StringIO
from math import comb
from pathlib import Path
import json
import runpy

with redirect_stdout(StringIO()):
    helpers = runpy.run_path(str(Path(__file__).with_name('verify_width_three_arithmetic.py')))
resource = helpers['resource']
weighted = helpers['weighted']
defect = helpers['defect']

for g in ((2, 1, 2), (2, 2, 1)):
    assert resource(3, 3, 2, g, True) >= 26

for r in range(2, 31):
    for s in range(2, r + 1):
        delta = r - s
        n = comb(r, 2) + comb(s, 2)
        assert 4*(4*r+3+n)-(r+s+3)**2 == delta**2+8*delta+3
        for k in (r, r+1, r+7):
            assert (4*(n+4*k+r+3)-(r+s+4)**2
                    == delta**2+10*delta+16*(k-r)-4)
        for w in (1, 2, 3, 5):
            for extra in (0, 1):
                assert (4*(1+5*r+n+w+extra)-(r+s+4)**2
                        == delta**2+10*delta-12+4*(w+extra))
    assert weighted(r, 1, 1) >= (1 if r == 2 else 2 if r == 3 else 3)
    baseline = (1 + (r+1) + r + r
                + (comb(r, 2)+1) + (comb(r, 2)+1) + 2 + (r-1) + (r-2))
    assert baseline == (r+1)*(r+3)

for r in range(3, 31):
    for a in range(2, r+3):
        for other in range(2, r+3):
            if a+other < r+1:
                continue
            assert other*(a+1) >= 2*r
            if (r, a, other) != (3, 2, 2):
                assert other*(a+1)+defect(r, a, 1, True) >= 2*r+3

print(json.dumps({'status': 'PASS', 'exceptional_resource_checks': 2,
                  'algebra_grid': '2 <= s <= r <= 30',
                  'balanced_product_bound_grid': '3 <= r <= 30; 2 <= A,N <= r+2',
                  'source_integrity': 'Checked centrally by verify_revision.py without fixed lemma numbering',
                  'scope': 'finite arithmetic and source-integrity checks, not theorem certification'}, indent=2))
