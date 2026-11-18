"""Check finite numerical tables in width_three_compact.tex (stdlib only)."""

from itertools import product
from math import comb
import json


def rectangle(n, a, b):
    return sum(x + y > n for x in range(1, a + 1) for y in range(1, b + 1))


def weighted(n, a, b):
    return sum(min(a * (n - i), b * i) for i in range(a, n - b + 1))


def rank_cut(n, a, b):
    return min(
        (n - l) * max(a - l, 0) + l * max(b + l - n, 0)
        + max(a - l, 0) * max(b + l - n, 0)
        for l in range(n + 1)
    )


def defect(n, a, b, full=False):
    values = [1, rectangle(n, a, b), weighted(n, a, b)]
    if full:
        values.append(rank_cut(n, a, b))
    return max(values)


def H(r, s, t, g):
    a, b, c = g
    core = {
        (x, y, z)
        for x, y, z in product(range(1, r + 1), range(1, t + 1), range(1, t + 1))
        if x + y <= r and x + z <= s and y + z <= t
        and not (x >= a and y >= b and z >= c)
    }
    box = set(product(range(1, a + 1), range(1, b + 1), range(1, c + 1))) - {g}
    return len(core | box)


def resource(r, s, t, g, full=False):
    a, b, c = g
    ls = [max(r, u) for u in g]
    hs = [max(r + a + b - ls[0] - ls[1], 0),
          max(s + a + c - ls[0] - ls[2], 0),
          max(t + b + c - ls[1] - ls[2], 0)]
    joint = max(*hs, (sum(hs) + 1) // 2) if full else 0
    return (1 + sum(ls) + joint + H(r, s, t, g)
            + comb(r, 2) + comb(s, 2) + comb(t, 2)
            + defect(r, a, b, full) + defect(s, a, c, full)
            + defect(t, b, c, full))


nonunit_rows = [
    ((2, 2, 2), (38, 44)), ((2, 2, 3), (46, 47)),
    ((2, 3, 2), (41, 47)), ((3, 2, 2), (41, 42)),
    ((3, 2, 3), (52, 52)), ((3, 3, 2), (51, 52)),
]
for (a, b, c), values in nonunit_rows:
    for s, expected in zip((3, 4), values):
        actual = (comb(4, 2) + comb(s, 2) + 12 + (a + 1) * b * c
                  + defect(4, a, b) + defect(s, a, c))
        assert actual == expected, (s, (a, b, c), actual, expected)

one_unit_rows = [
    (4, 3, (2, 3, 1), 35, 37, 36),
    (4, 4, (3, 2, 1), 41, 43, 43),
    (5, 5, (4, 2, 1), 56, 58, 57),
    (4, 4, (2, 3, 1), 42, 44, 43),
    (3, 3, (2, 2, 1), 28, 30, 31),
]
for r, s, g, bw, bf, target in one_unit_rows:
    assert resource(r, s, 3, g) == bw, (r, s, g, "BW")
    assert resource(r, s, 3, g, True) >= bf, (r, s, g, "BF")
    assert ((r + s + 5)**2 + 3) // 4 == target

for b, c in ((2, 3), (3, 2)):
    assert resource(3, 3, 3, (1, b, c)) == 31
    assert resource(4, 4, 3, (1, b, c)) == 47
assert resource(3, 3, 3, (1, 2, 2)) == 28
assert resource(3, 3, 3, (1, 2, 2), True) >= 30

# Verify the exact displayed algebraic identities at a finite integer grid;
# these are algebraic cross-checks, not finite proof of the unbounded theorem.
for r in range(3, 25):
    for s in range(3, r + 1):
        n, q, square = comb(r, 2) + comb(s, 2), r - s, (r + s + 5)**2
        assert 4 * (n + 7*r + 3*s - 10) - square == q*q + 16*r - 65
        assert 4 * (n + 6*r + s + 1) - square == q*q + 12*q + 4*s - 21
        for h in (r, r + 1, r + 5):
            assert (4 * (n + r + s + 4*h + 4) - square
                    == (q - 1)*(q + 9) + 16*(h - r))

print(json.dumps({"status": "PASS", "nonunit_table_rows": len(nonunit_rows),
                  "one_unit_table_rows": len(one_unit_rows),
                  "additional_resource_checks": 6,
                  "algebra_grid": "3 <= s <= r <= 24; h=r,r+1,r+5",
                  "scope": "finite table and algebra checks, not theorem certification"}, indent=2))
