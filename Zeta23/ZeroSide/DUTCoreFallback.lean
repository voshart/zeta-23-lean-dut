/-
DUTCoreFallback.lean

Remove the artificial `6 ≤ dutCoreCount` hypothesis from the concrete
strengthened c=2 zero-side inequality.

If the core contains at least six simple zeros, use the six-phase DUT theorem.
If it contains fewer than six, `(dutCoreCount - 5 : Nat) = 0`, hence the
explicit "saving" term is nonpositive; Anthropic's original `hatAz_mult2`
then implies the strengthened inequality automatically.

Intended location:
  Zeta23/ZeroSide/DUTCoreFallback.lean
-/

import Zeta23.ZeroSide.DUTHatAzPhase

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The strengthened c=2 `hat(A_z)` inequality for every core size.

The small-core branch is vacuous in the useful direction because the explicit
DUT saving is then nonpositive. -/
theorem dut_hatAz_mult2_all_core
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hP : P.Valid)
    (hT0 : 0 ≤ T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hrep :
      ∀ r ∈ Finset.range 6,
        DUTPhaseReplacementResult Z T P r) :
    4 * rtrace ((P.atD T).hat T (Z.Az (P.atD T) T))
      -
      frobSq ((P.atD T).hat T (Z.Az (P.atD T) T))
      -
      2 * (Z.NIprime T : ℝ)
      +
      dutCoreAveragedSaving Z T P
      ≤
      (Z.s1 T : ℝ) := by
  have hw0 : 0 ≤ P.w :=
    le_trans zero_le_one hP.one_le_w

  have hL : 0 < P.L T := by
    have : 0 < 8 * P.w := by
      nlinarith [hP.one_le_w]
    linarith

  have hcNorm :
      0 < dutPhaseNormC T P := by
    exact dutD_normConst_pos hP h8 h4pi

  by_cases hs6 : 6 ≤ dutCoreCount Z T
  · exact
      dut_hatAz_mult2_of_phase_average
        Z T P (dutD_phiHatConj P T)
        hL hs6 hcNorm hrep
  · have hsmall : dutCoreCount Z T - 5 = 0 := by
      omega

    have hbase :=
      hatAz_mult2
        Z T (P.atD T)
        (dutD_phiHatConj P T)
        (dutD_phiHatReal P T)
        (ThmD.poissonSqD hP h8)
        hcNorm

    have hsave :
        dutCoreAveragedSaving Z T P ≤ 0 := by
      unfold dutCoreAveragedSaving
      rw [hsmall]
      have hLT :
          0 ≤ (P.L T / (2 * Real.pi)) * T := by
        positivity
      have heta : 0 ≤ dutEta / 6 := by
        exact div_nonneg dutEta_nonneg (by norm_num)
      nlinarith

    linarith

end Zeta23.ZeroSide.RankTraceMult
