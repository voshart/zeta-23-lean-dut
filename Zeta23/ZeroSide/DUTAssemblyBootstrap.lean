/-
DUTAssemblyBootstrap.lean

Exact fixed-T bootstrap step for the DUT endgame.

The strengthened Assembly seam contains the explicit saving

  (eta/6) * (R * (dutCoreCount - 5) - 5 * L T/(2*pi)).

DUTCoreBoundary proves
  N0s(T,2T) <= dutCoreCount + dutCoreBoundaryN.

This file substitutes that exact finite lower bound into the saving.  No
asymptotics occur here; the boundary term remains explicit for the next file.

Intended location:
  Zeta23/ZeroSide/DUTAssemblyBootstrap.lean
-/

import Zeta23.ZeroSide.DUTAssemblySeam
import Zeta23.ZeroSide.DUTCoreBoundaryAsymptotic

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Exact lower bound for the averaged DUT saving in terms of the full
dyadic simple-zero count and the two discarded core boundary strips. -/
lemma dutCoreAveragedSaving_lower_N0s
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT4 : 4 ≤ T)
    (hs6 : 6 ≤ dutCoreCount Z T) :
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

  have h5 : 5 ≤ dutCoreCount Z T := by
    omega

  have hcore :
      (Z.N0s T (2 * T) : ℝ)
          - (dutCoreBoundaryN Z T : ℝ) - 5
        ≤ ((dutCoreCount Z T - 5 : ℕ) : ℝ) := by
    rw [Nat.cast_sub h5]
    norm_num
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

/-- Fixed-T DUT bootstrap inequality.

This is `dut_seamA_N0s` with `dutCoreCount` removed from the saving.  The
remaining boundary term is explicit and will be absorbed as `o(N)` in the
next asymptotic splice.
-/
theorem dut_seamA_N0s_bootstrap
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT4 : 4 ≤ T)
    {θ₀ : ℝ}
    (hTl : Assembly.TailInputs Z (P.atD T) T θ₀)
    (ha : 0 < (P.atD T).a T)
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (hcNorm : 0 < dutPhaseNormC T P)
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
    dut_seamA_N0s
      Z T P hT0 hTl ha hL hs6 hcNorm hrep

  have hsave :=
    dutCoreAveragedSaving_lower_N0s
      Z T P hT4 hs6

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
