#!/usr/bin/env python3
"""Independent exact regression checks for the Lean cyclic-quotient code.

This script is intentionally not a translation of the Lean proof. It compares
its closed formula with direct enumeration of every coordinate-kernel element,
then reproduces the larger primary sweep. All arithmetic is exact integer
arithmetic from Python's standard library.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


def primary(r: int, a: int, b: int) -> bool:
    """Closed cyclic CST formula."""
    return math.gcd(r // math.gcd(r, a), r // math.gcd(r, b)) == 1


def enumerated(r: int, a: int, b: int) -> bool:
    """Directly enumerate coordinate-kernel exponents and their generated subgroup."""
    generator_gcd = r
    for k in range(r):
        if (a * k) % r == 0 or (b * k) % r == 0:
            generator_gcd = math.gcd(generator_gcd, k)
    return generator_gcd == 1


def compare_through(bound: int) -> tuple[int, str]:
    checked = 0
    digest = hashlib.sha256()
    for r in range(2, bound + 1):
        for a in range(r):
            for b in range(r):
                p = primary(r, a, b)
                e = enumerated(r, a, b)
                if p != e:
                    raise AssertionError(
                        f"implementation disagreement at r={r}, a={a}, b={b}: "
                        f"primary={p}, enumerated={e}"
                    )
                digest.update(bytes((r & 0xFF, a & 0xFF, b & 0xFF, int(p))))
                checked += 1
    return checked, digest.hexdigest()


def primary_sweep(bound: int) -> tuple[int, int, str]:
    checked = 0
    smooth = 0
    digest = hashlib.sha256()
    for r in range(2, bound + 1):
        for a in range(r):
            qa = r // math.gcd(r, a)
            for b in range(r):
                value = math.gcd(qa, r // math.gcd(r, b)) == 1
                smooth += int(value)
                checked += 1
                digest.update(bytes((r & 0xFF, a & 0xFF, b & 0xFF, int(value))))
    return checked, smooth, digest.hexdigest()


def main() -> None:
    edge_cases = {
        "mu6_2_3": primary(6, 2, 3),
        "mu5_1_1": primary(5, 1, 1),
        "mu5_0_1": primary(5, 0, 1),
        "mu2_1_1": primary(2, 1, 1),
        "trivial_mu7": primary(7, 0, 0),
    }
    assert edge_cases == {
        "mu6_2_3": True,
        "mu5_1_1": False,
        "mu5_0_1": True,
        "mu2_1_1": False,
        "trivial_mu7": True,
    }

    independent_checked, independent_digest = compare_through(48)
    assert independent_checked == 38_023

    primary_checked, primary_smooth, primary_digest = primary_sweep(256)
    assert primary_checked == 5_625_215
    assert primary_smooth == 116_075

    result = {
        "edge_cases": edge_cases,
        "independent": {
            "max_order": 48,
            "representations": independent_checked,
            "agreement": True,
            "sha256": independent_digest,
        },
        "primary": {
            "max_order": 256,
            "representations": primary_checked,
            "smooth": primary_smooth,
            "singular": primary_checked - primary_smooth,
            "sha256": primary_digest,
        },
    }

    output = Path("regression-certificate.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
