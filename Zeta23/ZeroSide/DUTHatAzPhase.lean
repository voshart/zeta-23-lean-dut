/-
DUTHatAzPhase.lean

Translate the six-phase averaged DUT rank-trace inequalities from the internal
blockData decomposition to the concrete normalized matrix

  (P.atD T).hat T (Z.Az (P.atD T) T).

This mirrors the final `hatAz_mult2` / `hatAz_mult3` rewrites in
Zeta23/ZeroSide/Mult.lean, but keeps the additional averaged DUT saving term.

No new analytic estimate occurs here.

Intended location:
  Zeta23/ZeroSide/DUTHatAzPhase.lean
-/

import Zeta23.ZeroSide.DUTPhaseAverageRankTrace

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Explicit averaged DUT saving term on the interior core. -/
noncomputable def dutCoreAveragedSaving
    (Z : ZeroConfig) (T : ℝ) (P : Params) : ℝ :=
  (dutEta / 6) *
    (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
      - 5 * ((P.L T / (2 * Real.pi)) * T))

/-- c=2: concrete `hat(A_z)` inequality with the averaged DUT saving. -/
theorem dut_hatAz_mult2_of_phase_average
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T (P.atD T))
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (hcNorm : 0 < dutPhaseNormC T P)
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
  have h :=
    (dutPhase_average_rank_trace
      Z T P hL hs6 hcNorm hrep).1

  rw [
    hat_Az_eq_hatP_add_hatQ Z T (P.atD T) (dutD_phiHatConj P T),
    NIprime_eq_mk Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T)),
    s1_eq_mk Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T))
  ]

  simpa [
    dutPhaseRankBaseTwo,
    dutCoreAveragedSaving,
    DUTPhaseData,
    blockData,
    dutPhaseNormC,
    hatP,
    hatQ
  ] using h

/-- c=3: concrete `hat(A_z)` inequality with the averaged DUT saving. -/
theorem dut_hatAz_mult3_of_phase_average
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T (P.atD T))
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (hcNorm : 0 < dutPhaseNormC T P)
    (hrep :
      ∀ r ∈ Finset.range 6,
        DUTPhaseReplacementResult Z T P r) :
    6 * rtrace ((P.atD T).hat T (Z.Az (P.atD T) T))
      -
      frobSq ((P.atD T).hat T (Z.Az (P.atD T) T))
      -
      3 * (Z.NIprime T : ℝ)
      +
      dutCoreAveragedSaving Z T P
      ≤
      2 * ((Z.ZIprime T).ncard : ℝ) := by
  have h :=
    (dutPhase_average_rank_trace
      Z T P hL hs6 hcNorm hrep).2

  let D :=
    blockData Z T (P.atD T) (dutD_phiHatConj P T)
  let Pr :=
    mkPairReps Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T))

  rw [
    hat_Az_eq_hatP_add_hatQ Z T (P.atD T) (dutD_phiHatConj P T),
    NIprime_eq_mk Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T)),
    ncard_ZIprime_eq,
    s1_eq_mk Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T)),
    s2_eq_mk Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T)),
    p_eq_mk Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (dutD_phiHatConj P T))
  ]

  have hcard :
      Fintype.card (ZI Z T)
        = D.s₁ + D.s₂ + 2 * Pr.p := by
    exact D.card_eq Pr

  rw [hcard] at h

  simpa [
    dutPhaseRankBaseThree,
    dutCoreAveragedSaving,
    DUTPhaseData,
    blockData,
    dutPhaseNormC,
    hatP,
    hatQ,
    D, Pr
  ] using h

end Zeta23.ZeroSide.RankTraceMult
