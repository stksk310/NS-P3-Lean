"""Exact stdlib verification of the V03 eight-profile BF/H table.

This checks only the displayed finite arithmetic, not the geometric lemmas,
unbounded parameter reductions, main extremal theorem, or Lean development.
Helper module used by verify_revision.py; no external dependencies.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import re
import sys
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


@lru_cache(maxsize=None)
def Q(r, a, b):
    formula = sum(min(b, max(x + b - r, 0)) for x in range(1, a + 1))
    direct = sum(x + y > r for x in range(1, a + 1) for y in range(1, b + 1))
    require(formula == direct, f"Q formula/direct mismatch {(r,a,b)}")
    return formula


@lru_cache(maxsize=None)
def W(r, a, b):
    return sum(min(a * (r - i), b * i)
               for i in range(a, max(r - b, 0) + 1))


@lru_cache(maxsize=None)
def Phi(r, a, b):
    return min((r - ell) * max(a - ell, 0)
               + ell * max(b + ell - r, 0)
               + max(a - ell, 0) * max(b + ell - r, 0)
               for ell in range(r + 1))


@lru_cache(maxsize=None)
def F(r, a, b):
    return max(1, Q(r, a, b), W(r, a, b), Phi(r, a, b))


def pressure(r, a, b):
    return max(1, (r - a - b + 1) * a * b if a + b <= r else a + b - r)


def core_count(r, s, t):
    direct = sum(x + y <= r and x + z <= s and y + z <= t
                 for x in range(1, max(r, s) + 1)
                 for y in range(1, max(r, t) + 1)
                 for z in range(1, max(s, t) + 1))
    strips = sum(max(min(r - y, s - z), 0)
                 for y in range(1, t) for z in range(1, t - y + 1))
    require(direct == strips, f"Core direct/strip mismatch {(r,s,t)}")
    return direct


def section(text, first_label, next_label):
    first = text.index(r"\label{" + first_label + "}")
    last = text.index(r"\label{" + next_label + "}", first)
    return text[first:last]


def numeric_matrix(body):
    result = []
    for row in re.split(r"\\\\", body):
        if row.strip():
            cells = row.split("&")
            require(all(re.fullmatch(r"\s*-?\d+\s*", cell) for cell in cells),
                    f"Unexpected matrix content: {row!r}")
            result.append([int(cell) for cell in cells])
    return result


def longtable_bodies(text):
    return re.findall(r"\\midrule\\endhead(.*?)\\end\{longtable\}", text, re.S)


def table_rows(body):
    return [row.strip() for row in re.split(r"\\\\", body) if row.strip()]


def verify_capacity(text):
    """Recompute the V03 eight-row table using exact BF/H on all 1,497 cases."""
    begin = "% CAPACITY_V03_EIGHT_PROFILE_TABLE_BEGIN"
    end = "% CAPACITY_V03_EIGHT_PROFILE_TABLE_END"
    require(text.count(begin) == text.count(end) == 1,
            "Expected one marked eight-profile capacity table")
    body = text.split(begin, 1)[1].split(end, 1)[0]
    pattern = (r"\$\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)\$\s*&\s*"
               r"(\d+)\s*&\s*(\d+)\s*&\s*(\d+)\s*&\s*(-?\d+)")
    displayed_rows = [[int(n) for n in row] for row in re.findall(pattern, body)]
    expected_profiles = [(4,4,4), (5,4,4), (6,4,4), (7,4,4),
                         (5,5,4), (6,5,4), (6,6,4), (5,5,5)]
    require([tuple(row[:3]) for row in displayed_rows] == expected_profiles,
            "Eight-profile table has missing, reordered, or unexpected profiles")
    profiles, all_cases = [], []
    total_cases = 0
    for row in displayed_rows:
        r, s, t, shown_core, shown_K, shown_count, shown_minimum = row
        core = {(x, y, z)
                for x in range(1, r + 1)
                for y in range(1, t + 1)
                for z in range(1, t + 1)
                if x + y <= r and x + z <= s and y + z <= t}
        require(len(core) == core_count(r, s, t) == shown_core,
                f"Core count mismatch {(r,s,t)}")
        M = 1 + 3*r + math.comb(r,2) + math.comb(s,2) + math.comb(t,2)
        target = ((r+s+t+2)**2 + 3) // 4
        K, L = target - M, len(core) - 1
        require(K == shown_K, f"Target excess mismatch {(r,s,t)}")
        require(K+r+s <= L+17, f"Long-coordinate bound mismatch {(r,s,t)}")
        values = []
        for a in range(1, 7):
            for b in range(1, 7):
                for c in range(1, 7):
                    if a+b+c < r+2:
                        continue
                    g = (a,b,c)
                    box = {(x,y,z) for x in range(1,a+1)
                           for y in range(1,b+1) for z in range(1,c+1)} - {g}
                    punctured = {q for q in core
                                 if not all(qi >= gi for qi,gi in zip(q,g))}
                    h_union = len(box | punctured)
                    incomparable = sum(
                        not all(qi >= gi for qi,gi in zip(q,g))
                        and not all(qi <= gi for qi,gi in zip(q,g)) for q in core)
                    h = a*b*c-1 + incomparable
                    require(h == h_union, f"H formula/union mismatch {(r,s,t,g)}")
                    ls = [max(r, coordinate) for coordinate in g]
                    hs = [max(r+a+b-ls[0]-ls[1], 0),
                          max(s+a+c-ls[0]-ls[2], 0),
                          max(t+b+c-ls[1]-ls[2], 0)]
                    joint = max(*hs, (sum(hs)+1)//2)
                    BF = (1+sum(ls)+joint+h
                          +math.comb(r,2)+math.comb(s,2)+math.comb(t,2)
                          +F(r,a,b)+F(s,a,c)+F(t,b,c))
                    values.append((BF-target, a,b,c))
                    all_cases.append([r,s,t,a,b,c,h,BF,target])
        require(len(values) == shown_count, f"Omega count mismatch {(r,s,t)}")
        minimum = min(value[0] for value in values)
        require(minimum == shown_minimum and minimum >= 0,
                f"Exact BF minimum mismatch {(r,s,t)}: {minimum} != {shown_minimum}")
        total_cases += len(values)
        profiles.append({"profile": [r,s,t], "core": len(core), "K": K,
                         "eligible_triples": len(values), "minimum_excess": minimum,
                         "minimizers": [list(value[1:]) for value in values if value[0] == minimum]})
    require(total_cases == 1497, f"Expected 1497 exact cases, got {total_cases}")
    cases_payload = json.dumps(all_cases, separators=(",", ":")).encode("utf-8")
    return {"status": "PASS", "profile_count": len(profiles),
            "displayed_numeric_entries": 4*len(profiles),
            "exact_cases_checked": total_cases, "H_formula_union_agreements": total_cases,
            "profiles": profiles, "cases_sha256": hashlib.sha256(cases_payload).hexdigest(),
            "scope": "Exact finite BF/H arithmetic; not a proof of the unbounded capacity theorem."}


def expansion(n, degree):
    require(n >= 0 and degree >= 1, "Bad Macaulay input")
    original = n
    result = []
    for lower in range(degree, 0, -1):
        if n == 0:
            break
        top = lower
        while math.comb(top + 1, lower) <= n:
            top += 1
        result.append((top, lower))
        n -= math.comb(top, lower)
    require(n == 0, "Macaulay remainder did not vanish")
    require(sum(math.comb(a, i) for a, i in result) == original, "Bad reconstruction")
    require(all(result[j][0] > result[j + 1][0] for j in range(len(result) - 1)),
            "Macaulay tops do not descend strictly")
    return result


def raised(n, degree):
    return sum(math.comb(a + 1, i + 1) for a, i in expansion(n, degree))


def macaulay(m):
    r = 1
    while math.comb(r + 3, 3) <= m:
        r += 1
    s = m - math.comb(r + 2, 3)
    require(0 <= s < math.comb(r + 2, 2), "Bad Macaulay interval")
    return math.comb(r + 2, 2) + raised(s, r) - s, r, s


def verify_macaulay(text):
    d4 = section(text, "res:D.4", "res:D.5")
    bodies = longtable_bodies(d4)
    require(len(bodies) == 2, "Expected two D.4 tables")
    expansions_checked = 0
    for row in table_rows(bodies[0]):
        cells = [cell.strip() for cell in row.split("&")]
        require(len(cells) == 5, "Bad D.4 expansion row")
        s = int(cells[0])
        for degree, tops_cell, value_cell in ((2, cells[1], cells[2]),
                                             (3, cells[3], cells[4])):
            if tops_cell == "not needed":
                require(degree == 2 and s >= 6 and value_cell == "not needed",
                        "Unexpected omitted canonical expansion")
                continue
            tops = [] if tops_cell == "empty" else [int(a) for a in re.findall(r"\d+", tops_cell)]
            computed = expansion(s, degree)
            require(tops == [a for a, _ in computed], f"D.4 top list {(s,degree)}")
            require(int(value_cell) == raised(s, degree), f"D.4 raised value {(s,degree)}")
            expansions_checked += 1
    comparison_rows = []
    for row in table_rows(bodies[1]):
        m, displayed_T, displayed_C = [int(cell.strip()) for cell in row.split("&")]
        C, r, s = macaulay(m)
        T = 2 + math.isqrt(4 * m)
        require((T, C) == (displayed_T, displayed_C), f"D.4 comparison at m={m}")
        comparison_rows.append({"m": m, "T": T, "C": C, "degree": r, "remainder": s})
    require([row["m"] for row in comparison_rows] == list(range(4, 20)),
            "D.4 comparison domain differs")
    equalities, strict_count, smallest_positive_gap, largest_degree = [], 0, None, 0
    range_values = []
    for m in range(4, 1001):
        C, r, s = macaulay(m)
        T = 2 + math.isqrt(4 * m)
        require(C >= T, f"Macaulay below T at m={m}")
        require((C == T) == (m <= 9), f"Unexpected equality at m={m}")
        require(raised(s, r) >= s, "Raising decreased the remainder")
        if C == T:
            equalities.append(m)
        else:
            strict_count += 1
            gap = C - T
            smallest_positive_gap = gap if smallest_positive_gap is None else min(gap, smallest_positive_gap)
        largest_degree = max(largest_degree, r)
        range_values.append([m, T, C, r, s])
    return {"status": "PASS", "canonical_expansions_checked": expansions_checked,
            "canonical_top_and_raise_entries": 2 * expansions_checked,
            "displayed_comparison_rows": len(comparison_rows),
            "displayed_comparison_numeric_entries": 2 * len(comparison_rows),
            "range": [4, 1000], "multiplicities_checked": len(range_values),
            "equality_multiplicities": equalities, "strict_comparisons": strict_count,
            "smallest_positive_gap": smallest_positive_gap,
            "largest_degree": largest_degree, "displayed_comparisons": comparison_rows,
            "range_values_sha256": hashlib.sha256(json.dumps(range_values, separators=(",", ":")).encode()).hexdigest()}

