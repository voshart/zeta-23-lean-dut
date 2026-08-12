/-
DUTAssemblyBootstrapAllCore.lean

All-core exact fixed-T bootstrap.

This replaces the earlier bootstrap's `6 ≤ dutCoreCount` hypothesis by using
the all-core Assembly seam and proving the core-count lower substitution for
the truncated Nat expression directly.

Intended location:
  Zeta23/ZeroSide/DUTAssemblyBootstrapAllCore.lean
-/

import Zeta23.ZeroSide.DUTAssemblySeamAllCore
import Zeta23.ZeroSide.DUTCoreBoundaryAsymptotic

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Exact lower bound for the averaged DUT saving in terms of the full
dyadic simple-zero count and the two discarded core boundary strips, valid
for every core size. -/
lemma dutCoreAveragedSaving_lower_N0s_all_core
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT4 : 4 ≤ T) :
    (dutEta / 6) *
        (dutR *
            ((Z.N0s T (2 * T) : ℝ)
              - (dutCoreBoundaryN Z T : ℝ) - 5)
          - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤ dutCoreAveragedSaving Z T P := by
  have hrec :=
    dutCoreCount_recovers_N0s Z T hT4

  have hrecR :
      (Z.N0s T (2 * T) : ℝ)
        ≤ (dutCoreCount Z T : ℝ)
          + (dutCoreBoundaryN Z T : ℝ) := by
    exact_mod_cast hrec

  have hcore :
      (Z.N0s T (2 * T) : ℝ)
          - (dutCoreBoundaryN Z T : ℝ) - 5
        ≤ ((dutCoreCount Z T - 5 : ℕ) : ℝ) := by
    by_cases h5 : 5 ≤ dutCoreCount Z T
    · rw [Nat.cast_sub h5]
      norm_num
      linarith
    · have hsmall : dutCoreCount Z T - 5 = 0 := by
        omega
      rw [hsmall]
      norm_num
      have hc4 : dutCoreCount Z T ≤ 4 := by
        omega
      have hc4R : (dutCoreCount Z T : ℝ) ≤ 4 := by
        exact_mod_cast hc4
      linarith

  unfold dutCoreAveragedSaving

  have hR :
      dutR *
          ((Z.N0s T (2 * T) : ℝ)
            - (dutCoreBoundaryN Z T : ℝ) - 5)
        ≤
      dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hcore dutR_nonneg

  have hinner :
      dutR *
          ((Z.N0s T (2 * T) : ℝ)
            - (dutCoreBoundaryN Z T : ℝ) - 5)
          - 5 * ((P.L T / (2 * Real.pi)) * T)
        ≤
      dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
          - 5 * ((P.L T / (2 * Real.pi)) * T) := by
    linarith

  exact
    mul_le_mul_of_nonneg_left hinner
      (div_nonneg dutEta_nonneg (by norm_num))

/-- Fixed-T DUT bootstrap inequality, valid for every core size. -/
theorem dut_seamA_N0s_bootstrap_all_core
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hP : P.Valid)
    (hT4 : 4 ≤ T)
    {θ₀ : ℝ}
    (hTl : Assembly.TailInputs Z (P.atD T) T θ₀)
    (ha : 0 < (P.atD T).a T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hrep :
      ∀ r ∈ Finset.range 6,
        DUTPhaseReplacementResult Z T P r) :
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
      - frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
      - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / ((P.atD T).a T * (P.atD T).L T) *
          (4 + 2 * Real.sqrt
            (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
            + θ₀ / ((P.atD T).a T * (P.atD T).L T))
      + (dutEta / 6) *
          (dutR *
              ((Z.N0s T (2 * T) : ℝ)
                - (dutCoreBoundaryN Z T : ℝ) - 5)
            - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hT0 : 0 ≤ T := by
    linarith

  have hseam :=
    dut_seamA_N0s_all_core
      Z T P hP hT0 hTl ha h8 h4pi hrep

  have hsave :=
    dutCoreAveragedSaving_lower_N0s_all_core
      Z T P hT4

  calc
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - 2 * (Z.N T (2 * T) : ℝ)
        - 3 * (Assembly.NII Z T : ℝ)
        - θ₀ / ((P.atD T).a T * (P.atD T).L T) *
            (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
              + θ₀ / ((P.atD T).a T * (P.atD T).L T))
        + (dutEta / 6) *
            (dutR *
                ((Z.N0s T (2 * T) : ℝ)
                  - (dutCoreBoundaryN Z T : ℝ) - 5)
              - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - 2 * (Z.N T (2 * T) : ℝ)
        - 3 * (Assembly.NII Z T : ℝ)
        - θ₀ / ((P.atD T).a T * (P.atD T).L T) *
            (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
              + θ₀ / ((P.atD T).a T * (P.atD T).L T))
        + dutCoreAveragedSaving Z T P := by
          gcongr
    _ ≤ (Z.N0s T (2 * T) : ℝ) := hseam

end Zeta23.ZeroSide.RankTraceMult
