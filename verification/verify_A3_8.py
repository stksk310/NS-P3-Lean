"""Exhaustive finite arithmetic verification of compressed Lemma A3.8.

Python 3, standard library only.  This is a finite endpoint check, not a
verification of the unbounded capacity theorem or of a Lean development.
Run: python verify_A3_8.py
"""

from itertools import product
import json


def support(q):
    return sum(coordinate > 0 for coordinate in q)


# The common standard-point set: axes through 3, positive plane triangles.
K = {
    q for q in product(range(4), repeat=3)
    if support(q) <= 1 or (support(q) == 2 and sum(q) <= 3)
}
P = K | {(2, 2, 0), (1, 1, 1), (1, 1, 2), (1, 2, 1), (2, 1, 1)}
T = K | {
    (1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2), (3, 1, 0), (3, 0, 1)
}
assert len(K) == 19 and len(P) == 24 and len(T) == 25


def verify(name, points, alpha, beta, modulus, expected, maximizer):
    """Check every a,b, including nongenerators and low-order weights."""
    maximum = -1
    first_maximizer = None
    for a in range(modulus):
        for b in range(modulus):
            residues = [
                ((x - alpha * z) * a + (y - beta * z) * b) % modulus
                for x, y, z in sorted(points)
            ]
            image_size = len(set(residues))
            # A second collision test uses sorted adjacent values, not sets.
            ordered = sorted(residues)
            has_collision = any(x == y for x, y in zip(ordered, ordered[1:]))
            assert has_collision and image_size < len(points), (name, modulus, a, b)
            if image_size > maximum:
                maximum = image_size
                first_maximizer = (a, b)
    assert maximum == expected, (name, modulus, maximum)
    assert first_maximizer == maximizer, (name, modulus, first_maximizer)
    return {
        "set": name, "modulus": modulus, "point_count": len(points),
        "weight_pairs_checked": modulus**2,
        "maximum_image_size": maximum,
        "first_maximizer": first_maximizer,
    }


rows = [
    verify("P", P, 2, 2, 30, 23, (1, 25)),
    verify("T", T, 3, 1, 27, 23, (3, 4)),
    verify("T", T, 3, 1, 28, 24, (4, 3)),
    verify("T", T, 3, 1, 29, 23, (1, 8)),
    verify("T", T, 3, 1, 30, 23, (2, 5)),
]
assert sum(row["weight_pairs_checked"] for row in rows) == 4154
print(json.dumps({"status": "PASS", "rows": rows, "total_weight_pairs": 4154}, indent=2))
