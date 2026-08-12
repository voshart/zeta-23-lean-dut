#!/usr/bin/env python3
"""
Rigorous external verifier for the DUT six-point certificate at

    lambda = 999999999 / 1000000000.

It verifies the scale-free inequality

    eta * (g1+...+g5)
      + 2 * sum_{0 <= i < j <= 5} k_lambda(x_j-x_i)^2
      >= eta * R_verifier

for all nonnegative gaps g1,...,g5 with total span <= R_verifier, where

    eta        = 27/20000,
    R_verifier = 189/20,

and x_0 = 0, x_j = g1+...+gj.

Equivalently,

    2 * sum_{i<j} k_lambda(x_j-x_i)^2
      >= eta * max(R_verifier - (x_5-x_0), 0).

This is the dimensionless finite inequality intended to discharge the
`DUTSharpVerifierCertificate` seam after the Lean scale-free kernel bridge
is checked.

The interval-search architecture is adapted from the MIT-licensed verifier:
    https://github.com/ainta/zeta-simple-zeros
in particular its Arb kernel-cell enclosures, sparse range minima,
outward-rounded binary64 lower arithmetic, and convex-tangent pruning.

This program is an *external* rigorous verifier.  Running it does not by
itself create a Lean theorem; the remaining Lean task is to prove that the
sharp kernel in DUTSharpCertificateSeam is exactly this scale-free kernel.

Requires:
    python-flint >= 0.6, < 1

Usage:
    python verify_dut_six.py --progress-every 100000
    python verify_dut_six.py --output dut-six-certificate.json
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import struct
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

from flint import arb, ctx, fmpq


# ---------------------------------------------------------------------------
# Exact problem constants
# ---------------------------------------------------------------------------

LAM_NUM = 999_999_999
LAM_DEN = 1_000_000_000

ETA_NUM = 27
ETA_DEN = 20_000

R_NUM = 189
R_DEN = 20

TARGET_NUM = ETA_NUM * R_NUM       # 5103
TARGET_DEN = ETA_DEN * R_DEN       # 400000

GRID = 4_000
PRECISION_BITS = 128

# R * GRID = 9.45 * 4000 = 37800 exactly.
PRESSURE_CUTOFF_CELLS = R_NUM * GRID // R_DEN

# The tangent/Hessian machinery is used only safely away from the removable
# sinc point.  The one-body pruning leaves gaps above about 0.97, so 0.95 is
# conservative.
SECOND_DERIVATIVE_START = 3_800


# ---------------------------------------------------------------------------
# Outward-rounded binary64 helpers
# (same pattern as ainta/zeta-simple-zeros)
# ---------------------------------------------------------------------------

def down_ratio(numerator: int, denominator: int) -> float:
    if numerator < 0 or denominator <= 0:
        raise ValueError("down_ratio expects numerator >= 0 and denominator > 0")
    if numerator == 0:
        return 0.0
    return math.nextafter(numerator / denominator, -math.inf)


def up_ratio(numerator: int, denominator: int) -> float:
    if numerator < 0 or denominator <= 0:
        raise ValueError("up_ratio expects numerator >= 0 and denominator > 0")
    if numerator == 0:
        return 0.0
    return math.nextafter(numerator / denominator, math.inf)


def down_mul(left: float, right: float) -> float:
    if left < 0.0 or right < 0.0:
        raise ValueError("down_mul expects nonnegative inputs")
    if left == 0.0 or right == 0.0:
        return 0.0
    return max(0.0, math.nextafter(left * right, -math.inf))


def down_add(left: float, right: float) -> float:
    if left < 0.0 or right < 0.0:
        raise ValueError("down_add expects nonnegative inputs")
    if left == 0.0 and right == 0.0:
        return 0.0
    return max(0.0, math.nextafter(left + right, -math.inf))


# ---------------------------------------------------------------------------
# Arb enclosure of the exact lambda-dependent normalized sharp kernel
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class KernelConstants:
    lam: arb
    sqrt_two: arb
    inv_sqrt_two: arb
    pi: arb
    phase: arb
    k_zero: arb


def configure_arb(precision: int = PRECISION_BITS) -> None:
    if precision < 80:
        raise ValueError("at least 80 bits are required")
    ctx.prec = precision


def kernel_constants() -> KernelConstants:
    lam = arb(fmpq(LAM_NUM, LAM_DEN))
    sqrt_two = arb(2).sqrt()
    inv_sqrt_two = 1 / sqrt_two
    phase = lam * inv_sqrt_two
    # Integral normalization:
    #   aStar(lambda) = sinc(lambda/sqrt(2)).
    k_zero = phase.sinc()
    return KernelConstants(
        lam=lam,
        sqrt_two=sqrt_two,
        inv_sqrt_two=inv_sqrt_two,
        pi=arb.pi(),
        phase=phase,
        k_zero=k_zero,
    )


def normalized_kernel(x: arb, constants: KernelConstants | None = None) -> arb:
    r"""Enclose

      k_lambda(x) =
        [sinc(pi*x-lambda/sqrt(2)) + sinc(pi*x+lambda/sqrt(2))]
        / [2*sinc(lambda/sqrt(2))].

    The entire sinc representation avoids removable-singularity cases.
    """
    c = constants or kernel_constants()
    left = (c.pi * x - c.phase).sinc()
    right = (c.pi * x + c.phase).sinc()
    return ((left + right) / 2) / c.k_zero


def squared_kernel_derivatives(
    x: arb, constants: KernelConstants | None = None
) -> tuple[arb, arb, arb]:
    r"""Return enclosures for w=k_lambda^2 and its first two derivatives.

    This explicit derivative representation divides by z^3, so the verifier
    uses it only for x >= 0.95.  General kernel evaluation always uses the
    entire Arb sinc function.
    """
    c = constants or kernel_constants()
    z_left = c.pi * x - c.phase
    z_right = c.pi * x + c.phase

    def sinc_derivatives(z: arb) -> tuple[arb, arb, arb]:
        sine = z.sin()
        cosine = z.cos()
        z_squared = z * z
        value = sine / z
        first = (z * cosine - sine) / z_squared
        second = ((2 - z_squared) * sine - 2 * z * cosine) / (z_squared * z)
        return value, first, second

    left, left_prime, left_second = sinc_derivatives(z_left)
    right, right_prime, right_second = sinc_derivatives(z_right)

    raw = (left + right) / 2
    raw_prime = c.pi * (left_prime + right_prime) / 2
    raw_second = c.pi * c.pi * (left_second + right_second) / 2

    normalization_squared = c.k_zero * c.k_zero
    value = raw * raw / normalization_squared
    first = 2 * raw * raw_prime / normalization_squared
    second = 2 * (raw_prime * raw_prime + raw * raw_second) / normalization_squared
    return value, first, second


def closed_cell(index: int, grid: int = GRID) -> arb:
    """Exact Arb ball representing [index/grid,(index+1)/grid]."""
    if index < 0 or grid <= 0:
        raise ValueError("index must be nonnegative and grid must be positive")
    return arb(fmpq(2 * index + 1, 2 * grid), fmpq(1, 2 * grid))


def _arb_nonnegative_lower_to_float(value: arb) -> float:
    candidate = float(value.lower())
    if candidate <= 0.0:
        return 0.0
    return math.nextafter(candidate, -math.inf)


def squared_kernel_cell_lower(
    index: int, constants: KernelConstants
) -> float:
    """Rigorous binary64 lower bound for min k_lambda(x)^2 on one cell."""
    enclosure = normalized_kernel(closed_cell(index), constants)
    absolute_lower = _arb_nonnegative_lower_to_float(enclosure.abs_lower())
    return down_mul(absolute_lower, absolute_lower)


def build_kernel_table(
    cell_count: int, constants: KernelConstants
) -> List[float]:
    return [squared_kernel_cell_lower(i, constants) for i in range(cell_count)]


def build_second_derivative_lower_table(
    cell_count: int, constants: KernelConstants
) -> List[float]:
    values = [-math.inf] * cell_count
    for index in range(SECOND_DERIVATIVE_START, cell_count):
        _, _, second = squared_kernel_derivatives(closed_cell(index), constants)
        values[index] = math.nextafter(float(second.lower()), -math.inf)
    return values


def table_sha256(values: Sequence[float]) -> str:
    digest = hashlib.sha256()
    for value in values:
        digest.update(struct.pack(">d", value))
    return digest.hexdigest()


class RangeMinimum:
    """O(1) idempotent sparse-table range-minimum queries."""

    def __init__(self, values: Sequence[float]):
        if not values:
            raise ValueError("values must be nonempty")
        self._length = len(values)
        levels: List[List[float]] = [list(values)]
        width = 1
        while 2 * width <= self._length:
            previous = levels[-1]
            half = width
            width *= 2
            levels.append(
                [
                    min(previous[i], previous[i + half])
                    for i in range(self._length - width + 1)
                ]
            )
        self._levels = levels

    @property
    def length(self) -> int:
        return self._length

    def query(self, left: int, right: int) -> float:
        if left < 0 or right < left or right >= self._length:
            raise IndexError((left, right, self._length))
        level = (right - left + 1).bit_length() - 1
        width = 1 << level
        row = self._levels[level]
        return min(row[left], row[right - width + 1])


# ---------------------------------------------------------------------------
# Five-gap branch-and-bound
# ---------------------------------------------------------------------------

CellRange = Tuple[int, int]
DUTBox = Tuple[CellRange, CellRange, CellRange, CellRange, CellRange]


def _components(indices: Iterable[int]) -> List[CellRange]:
    result: List[List[int]] = []
    for index in indices:
        if not result or index > result[-1][1] + 1:
            result.append([index, index])
        else:
            result[-1][1] = index
    return [(left, right) for left, right in result]


def source_sha256() -> str:
    try:
        payload = Path(__file__).read_bytes()
    except OSError:
        return "unavailable"
    return hashlib.sha256(payload).hexdigest()


def verify(progress_every: int = 0) -> dict:
    configure_arb()
    started = time.perf_counter()

    # A few extra cells let interval sums straddle the pressure boundary.
    cell_count = PRESSURE_CUTOFF_CELLS + 8

    constants = kernel_constants()
    table = build_kernel_table(cell_count, constants)
    ranges = RangeMinimum(table)

    second_table = build_second_derivative_lower_table(cell_count, constants)
    second_ranges = RangeMinimum(second_table)

    target_upper = up_ratio(TARGET_NUM, TARGET_DEN)

    def kernel_min(left: int, right: int) -> float:
        if right >= ranges.length:
            # w >= 0 globally.
            return 0.0
        return ranges.query(left, right)

    def second_derivative_min(left: int, right: int) -> float:
        if right >= second_ranges.length:
            return float("-inf")
        return second_ranges.query(left, right)

    # U(g) = eta*g + 2*w(g) is a nonnegative subset of the full objective.
    # If U alone reaches the target, that gap cell can never occur in a
    # counterexample.
    surviving_cells: List[int] = []
    for index in range(PRESSURE_CUTOFF_CELLS):
        one_body = down_ratio(ETA_NUM * index, ETA_DEN * GRID)
        one_body = down_add(one_body, down_mul(2.0, table[index]))
        if one_body < target_upper:
            surviving_cells.append(index)

    components = _components(surviving_cells)

    stack: List[Tuple[DUTBox, int]] = [
        (tuple(parts), 0)  # type: ignore[arg-type]
        for parts in itertools.product(components, repeat=5)
    ]

    initial_boxes = len(stack)
    nodes = 0
    pruned = 0
    splits = 0
    maximum_depth = 0
    pressure_pruned = 0
    interval_pruned = 0
    tangent_pruned = 0

    def box_lower(box: DUTBox) -> float:
        lows = [part[0] for part in box]
        highs = [part[1] for part in box]

        low_prefix = [0]
        high_prefix = [0]
        for low, high in zip(lows, highs):
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        # eta * total span.
        result = down_ratio(
            ETA_NUM * low_prefix[-1],
            ETA_DEN * GRID,
        )

        # All 15 unordered pair separations among six points; each contributes
        # 2*k_lambda(distance)^2 to the Gram energy.
        for span in range(1, 6):
            for start in range(6 - span):
                left = low_prefix[start + span] - low_prefix[start]
                right = (
                    high_prefix[start + span]
                    - high_prefix[start]
                    + span
                    - 1
                )
                result = down_add(
                    result,
                    down_mul(2.0, kernel_min(left, right)),
                )

        return result

    def exact_float(value: float) -> arb:
        numerator, denominator = value.as_integer_ratio()
        return arb(fmpq(numerator, denominator))

    def float_ldl_is_positive(matrix: List[List[float]]) -> bool:
        """Cheap heuristic only; success is rechecked exactly with Arb."""
        lower = [[0.0] * 5 for _ in range(5)]
        diagonal = [0.0] * 5

        for column in range(5):
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= (
                    lower[column][previous]
                    * lower[column][previous]
                    * diagonal[previous]
                )
            if pivot <= 1e-12:
                return False

            diagonal[column] = pivot
            lower[column][column] = 1.0

            for row in range(column + 1, 5):
                value = matrix[row][column]
                for previous in range(column):
                    value -= (
                        lower[row][previous]
                        * lower[column][previous]
                        * diagonal[previous]
                    )
                lower[row][column] = value / pivot

        return True

    def arb_ldl_is_positive(
        terms: Sequence[Tuple[int, int, float]]
    ) -> bool:
        """Prove the rational lower-Hessian matrix positive definite."""
        matrix = [[arb(0) for _ in range(5)] for _ in range(5)]

        for start, span, coefficient in terms:
            exact = exact_float(coefficient)
            for row in range(start, start + span):
                for column in range(start, start + span):
                    matrix[row][column] += exact

        lower = [[arb(0) for _ in range(5)] for _ in range(5)]
        diagonal = [arb(0) for _ in range(5)]

        for column in range(5):
            lower[column][column] = arb(1)
            pivot = matrix[column][column]

            for previous in range(column):
                pivot -= (
                    lower[column][previous]
                    * lower[column][previous]
                    * diagonal[previous]
                )

            if not (pivot > 0):
                return False

            diagonal[column] = pivot

            for row in range(column + 1, 5):
                value = matrix[row][column]
                for previous in range(column):
                    value -= (
                        lower[row][previous]
                        * lower[column][previous]
                        * diagonal[previous]
                    )
                lower[row][column] = value / pivot

        return True

    def convex_tangent_lower(box: DUTBox) -> Optional[arb]:
        """Rigorous tangent lower bound when the full Hessian is certified PD."""
        low_prefix = [0]
        high_prefix = [0]

        for low, high in box:
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        terms: List[Tuple[int, int, float]] = []
        heuristic = [[0.0] * 5 for _ in range(5)]

        for span in range(1, 6):
            for start in range(6 - span):
                left = low_prefix[start + span] - low_prefix[start]
                right = (
                    high_prefix[start + span]
                    - high_prefix[start]
                    + span
                    - 1
                )

                second_lower = second_derivative_min(left, right)
                if second_lower == float("-inf"):
                    return None

                # Pair coefficient is exactly 2, so one downward rounding
                # handles either sign of the derivative bound.
                scalar = math.nextafter(2.0 * second_lower, -math.inf)
                terms.append((start, span, scalar))

                for row in range(start, start + span):
                    for column in range(start, start + span):
                        heuristic[row][column] += scalar

        if not float_ldl_is_positive(heuristic):
            return None
        if not arb_ldl_is_positive(terms):
            return None

        midpoints = [
            fmpq(low + high + 1, 2 * GRID)
            for low, high in box
        ]
        radii = [
            fmpq(high - low + 1, 2 * GRID)
            for low, high in box
        ]

        pressure = arb(fmpq(ETA_NUM, ETA_DEN))
        value = pressure * sum((arb(point) for point in midpoints), arb(0))
        gradient = [pressure for _ in range(5)]

        for span in range(1, 6):
            for start in range(6 - span):
                point = sum(midpoints[start : start + span], fmpq(0))
                potential, derivative, _ = squared_kernel_derivatives(
                    arb(point), constants
                )

                value += 2 * potential
                for coordinate in range(start, start + span):
                    gradient[coordinate] += 2 * derivative

        lower = value
        for derivative, radius in zip(gradient, radii):
            lower -= derivative.abs_upper() * arb(radius)

        return lower

    exact_target = arb(fmpq(TARGET_NUM, TARGET_DEN))

    while stack:
        box, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)

        # If the lower endpoint of the total span is already >= R, the linear
        # pressure term alone reaches the target.
        if sum(part[0] for part in box) >= PRESSURE_CUTOFF_CELLS:
            pruned += 1
            pressure_pruned += 1
            continue

        lower = box_lower(box)
        if lower >= target_upper:
            pruned += 1
            interval_pruned += 1
            continue

        tangent_lower = convex_tangent_lower(box)
        if tangent_lower is not None and tangent_lower >= exact_target:
            pruned += 1
            tangent_pruned += 1
            continue

        widths = [right - left for left, right in box]
        if max(widths) == 0:
            raise RuntimeError(
                "DUT six-point certificate failed at a terminal cell: "
                f"box={box}, lower={lower.hex()}"
            )

        splits += 1
        coordinate = max(range(5), key=widths.__getitem__)
        left, right = box[coordinate]
        midpoint = (left + right) // 2

        lower_half = list(box)
        upper_half = list(box)
        lower_half[coordinate] = (left, midpoint)
        upper_half[coordinate] = (midpoint + 1, right)

        stack.append((tuple(lower_half), depth + 1))  # type: ignore[arg-type]
        stack.append((tuple(upper_half), depth + 1))  # type: ignore[arg-type]

        if progress_every and nodes % progress_every == 0:
            print(
                "dut-six: "
                f"nodes={nodes} pending={len(stack)} depth={maximum_depth}",
                flush=True,
            )

    elapsed = time.perf_counter() - started
    component_text = ";".join(f"[{a},{b}]" for a, b in components)

    return {
        "certificate": "DUT-six-point",
        "verified": True,
        "lambda": f"{LAM_NUM}/{LAM_DEN}",
        "eta": f"{ETA_NUM}/{ETA_DEN}",
        "R_verifier": f"{R_NUM}/{R_DEN}",
        "target": f"{TARGET_NUM}/{TARGET_DEN}",
        "statement": (
            "eta*sum(gaps) + 2*sum_{i<j} k_lambda(x_j-x_i)^2 "
            ">= eta*R_verifier for gaps>=0, sum(gaps)<=R_verifier"
        ),
        "grid": GRID,
        "precision_bits": PRECISION_BITS,
        "kernel_table_sha256": table_sha256(table),
        "second_derivative_table_sha256": table_sha256(second_table),
        "source_sha256": source_sha256(),
        "nodes": nodes,
        "pruned": pruned,
        "splits": splits,
        "maximum_depth": maximum_depth,
        "initial_boxes": initial_boxes,
        "elapsed_seconds": elapsed,
        "pressure_pruned": pressure_pruned,
        "interval_pruned": interval_pruned,
        "tangent_pruned": tangent_pruned,
        "surviving_gap_components_cells": component_text,
        "surviving_gap_components_count": len(components),
        "trust_base": [
            "Python runtime and IEEE-754 binary64 semantics",
            "python-flint and Arb/FLINT",
            "this verifier source",
            "operating system and hardware",
        ],
        "related_verifier": "https://github.com/ainta/zeta-simple-zeros",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--progress-every",
        type=int,
        default=0,
        help="print search progress every N visited nodes (0 disables)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="optional JSON certificate/report path",
    )
    args = parser.parse_args()

    report = verify(progress_every=args.progress_every)
    payload = json.dumps(report, indent=2, sort_keys=True)
    print(payload)

    if args.output is not None:
        args.output.write_text(payload + "\n", encoding="utf-8")
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
