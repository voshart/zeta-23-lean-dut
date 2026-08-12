/-
DUTTailLattice.lean

Arithmetic-progression tail estimates for the DUT finite-grid truncation.

This file combines two ingredients already kernel-checked:
  * DUTTailSeries:  sum' 1/(n+1)^2 <= 2;
  * DUTInteriorBlocks / DUTTailPointwise: every core zero is separated from
    the omitted left/right grid.

The key analytic comparison is

  sum' n, 1 / (D + (n+1)h)^4 <= 2 / (D^2 h^2),

proved without floors and without the exact value of zeta(2).  The same
bound applies to the right tail after replacing D by the first-right-point
gap G = sqrt(T)-h.

We also record the exact progressive distance inequalities for the concrete
Theorem-D lattice.

Intended location:
  Zeta23/ZeroSide/DUTTailLattice.lean
-/

import Zeta23.ZeroSide.DUTTailSeries

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Pointwise majorization of an affine fourth-power tail by the universal
shifted inverse-square majorant. -/
lemma dut_inv_four_affine_le_inv_sq_majorant
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) (n : ℕ) :
    1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4
      ≤ (1 / (D ^ 2 * h ^ 2)) *
          (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
  let q : ℝ := D + ((n + 1 : ℕ) : ℝ) * h
  have hn1 : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hnh : 0 < (((n + 1 : ℕ) : ℝ)) * h := mul_pos hn1 hh
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hDq : D ≤ q := by
    dsimp [q]
    linarith
  have hhq : (((n + 1 : ℕ) : ℝ)) * h ≤ q := by
    dsimp [q]
    linarith
  have hsqD : D ^ 2 ≤ q ^ 2 := by nlinarith
  have hsqH : ((((n + 1 : ℕ) : ℝ)) * h) ^ 2 ≤ q ^ 2 := by nlinarith
  have hprod :
      D ^ 2 * ((((n + 1 : ℕ) : ℝ)) * h) ^ 2 ≤ q ^ 4 := by
    have hm :=
      mul_le_mul hsqD hsqH (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hden : 0 < D ^ 2 * ((((n + 1 : ℕ) : ℝ)) * h) ^ 2 := by
    positivity
  calc
    1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4
        = 1 / q ^ 4 := by rfl
    _ ≤ 1 / (D ^ 2 * ((((n + 1 : ℕ) : ℝ)) * h) ^ 2) :=
      one_div_le_one_div_of_le hden hprod
    _ = (1 / (D ^ 2 * h ^ 2)) *
          (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
      field_simp [hD.ne', hh.ne', ne_of_gt hn1]

/-- Fourth-power arithmetic-progression tail bound:
`Σ 1/(D+(n+1)h)^4 ≤ 2/(D²h²)`. -/
lemma dut_tsum_inv_four_affine_le
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    (∑' n : ℕ, 1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4)
      ≤ 2 / (D ^ 2 * h ^ 2) := by
  have hmaj :
      ∀ n : ℕ,
        1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4
          ≤ (1 / (D ^ 2 * h ^ 2)) *
              (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) :=
    dut_inv_four_affine_le_inv_sq_majorant hD hh

  have hsmaj :
      Summable
        (fun n : ℕ =>
          (1 / (D ^ 2 * h ^ 2)) *
            (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2))) :=
    dut_summable_inv_sq_succ.mul_left _

  have hsum :=
    Summable.tsum_le_tsum
      hmaj
      (Summable.of_nonneg_of_le
        (fun n => by positivity)
        hmaj
        hsmaj)
      hsmaj

  calc
    (∑' n : ℕ, 1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4)
        ≤ ∑' n : ℕ,
            (1 / (D ^ 2 * h ^ 2)) *
              (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := hsum
    _ = (1 / (D ^ 2 * h ^ 2)) *
          (∑' n : ℕ, 1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
      rw [tsum_mul_left]
    _ ≤ (1 / (D ^ 2 * h ^ 2)) * 2 := by
      exact
        mul_le_mul_of_nonneg_left
          dut_tsum_inv_sq_succ_le_two
          (by positivity)
    _ = 2 / (D ^ 2 * h ^ 2) := by ring

/-- Left omitted lattice index: `-1,-2,-3,...`. -/
def dutLeftTailIndex (n : ℕ) : ℤ :=
  -((n + 1 : ℕ) : ℤ)

/-- Right omitted lattice index: `d,d+1,d+2,...`. -/
def dutRightTailIndex (P : Params) (T : ℝ) (n : ℕ) : ℤ :=
  ((P.atD T).d T : ℤ) + n

/-- Exact arithmetic progression of the left omitted lattice. -/
lemma dutD_tau_left_tail
    (P : Params) (T : ℝ) (n : ℕ) :
    (P.atD T).tau T (dutLeftTailIndex n)
      =
      T - ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T := by
  unfold dutLeftTailIndex Params.tau
  push_cast
  ring

/-- Exact arithmetic progression of the right omitted lattice. -/
lemma dutD_tau_right_tail
    (P : Params) (T : ℝ) (n : ℕ) :
    (P.atD T).tau T (dutRightTailIndex P T n)
      =
      (P.atD T).tau T ((P.atD T).d T : ℤ)
        + (n : ℝ) * (P.atD T).hgrid T := by
  unfold dutRightTailIndex Params.tau
  push_cast
  ring

/-- Progressive left-tail distance:
`|gamma - tau_{-(n+1)}| ≥ sqrt(T) + (n+1)h`. -/
lemma dutCoreSix_left_progressive_distance
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    (n : ℕ) :
    D0 T + ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T
      ≤
      |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - (P.atD T).tau T (dutLeftTailIndex n)| := by
  have hh : 0 < (P.atD T).hgrid T := by
    have hhP : 0 < P.hgrid T := by
      unfold Params.hgrid
      positivity
    simpa using hhP
  have hcore := dutCoreSix_lower Z T i hi j
  rw [dutD_tau_left_tail]
  have hnonneg :
      0 ≤
        ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (T - ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T) := by
    have hD : 0 ≤ D0 T := Real.sqrt_nonneg T
    have hn : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
    have hmul :
        0 ≤ ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T :=
      mul_nonneg hn hh.le
    linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- Progressive right-tail distance:
`|gamma - tau_{d+n}| ≥ (sqrt(T)-h) + n h`. -/
lemma dutCoreSix_right_progressive_distance
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT : 0 ≤ T) (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    (n : ℕ) :
    (D0 T - (P.atD T).hgrid T)
        + (n : ℝ) * (P.atD T).hgrid T
      ≤
      |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - (P.atD T).tau T (dutRightTailIndex P T n)| := by
  have hh : 0 < (P.atD T).hgrid T := by
    have hhP : 0 < P.hgrid T := by
      unfold Params.hgrid
      positivity
    simpa using hhP
  have hbase :=
    dutCoreSix_right_distance_at_d Z T P hL hT i hi j
  rw [dutD_tau_right_tail]
  have hdist :
      (D0 T - (P.atD T).hgrid T)
          + (n : ℝ) * (P.atD T).hgrid T
        ≤
        ((P.atD T).tau T ((P.atD T).d T : ℤ)
            + (n : ℝ) * (P.atD T).hgrid T)
          - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im := by
    linarith
  calc
    (D0 T - (P.atD T).hgrid T)
          + (n : ℝ) * (P.atD T).hgrid T
        ≤
        ((P.atD T).tau T ((P.atD T).d T : ℤ)
            + (n : ℝ) * (P.atD T).hgrid T)
          - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im := hdist
    _ ≤
        |((P.atD T).tau T ((P.atD T).d T : ℤ)
            + (n : ℝ) * (P.atD T).hgrid T)
          - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im| :=
      le_abs_self _
    _ =
        |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - ((P.atD T).tau T ((P.atD T).d T : ℤ)
            + (n : ℝ) * (P.atD T).hgrid T)| := by
      rw [abs_sub_comm]

end Zeta23.ZeroSide.RankTraceMult
