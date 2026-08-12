/-
DUTVerifierCertificateBridge.lean

Transfer the dimensionless six-point verifier proposition to the original
physical-coordinate `DUTSharpVerifierCertificate`.

Together with `DUTVerifierKernelBridge`, this proves that the only remaining
external input is exactly `DUTFixedScaleFreeSharpCertificate` -- the
dimensionless proposition checked by verify_dut_six.py.
-/

import Zeta23.ZeroSide.DUTVerifierKernelBridge

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Positive physical-to-verifier scaling preserves strict ordering. -/
private theorem dutVerifierCoord_strictMono
    {L : ℝ} (hL : 0 < L) :
    StrictMono (dutVerifierCoord L) := by
  intro a b hab
  unfold dutVerifierCoord
  have hscale :
      0 < L / (2 * Real.pi) := by
    positivity
  exact mul_lt_mul_of_pos_left hab hscale

/-- Coordinate differences commute with the verifier scaling. -/
private theorem dutVerifierCoord_sub
    {L a b : ℝ} :
    dutVerifierCoord L (a - b)
      =
    dutVerifierCoord L a - dutVerifierCoord L b := by
  unfold dutVerifierCoord
  ring

/-- The normalized six-span is exactly the endpoint span after applying the
dimensionless verifier coordinate. -/
private theorem dutNormalizedSixSpan_eq_verifierCoord_span
    (P : Params) (T : ℝ) (gamma : Fin 6 → ℝ) :
    dutNormalizedSixSpan P T gamma
      =
    dutVerifierCoord (P.L T) (gamma 5)
      - dutVerifierCoord (P.L T) (gamma 0) := by
  unfold dutNormalizedSixSpan dutVerifierCoord
  ring

/-- Entrywise identity between the physical sharp matrix and the
dimensionless matrix evaluated on scaled ordinates. -/
theorem dutSharpMatrixOfOrdinates_eq_scaleFree
    (P : Params) (hP : P.Valid)
    {T : ℝ} (hL : 0 < P.L T)
    (gamma : Fin 6 → ℝ) :
    dutSharpMatrixOfOrdinates P T gamma
      =
    dutScaleFreeSharpMatrix P.lam
      (fun j => dutVerifierCoord (P.L T) (gamma j)) := by
  ext j l
  unfold dutSharpMatrixOfOrdinates dutScaleFreeSharpMatrix
  rw [dutDSharpKernel_eq_scaleFree P hP hL]
  rw [dutVerifierCoord_sub]

/-- A dimensionless six-point certificate at `P.lam` implies the exact
physical-coordinate verifier contract required by the DUT proof. -/
theorem dutSharpVerifierCertificate_of_scaleFree
    (P : Params) (hP : P.Valid)
    (hcert : DUTScaleFreeSharpCertificate P.lam) :
    DUTSharpVerifierCertificate P := by
  intro T hL gamma hgamma

  let x : Fin 6 → ℝ :=
    fun j => dutVerifierCoord (P.L T) (gamma j)

  have hxmono : StrictMono x := by
    intro j l hjl
    dsimp [x]
    exact dutVerifierCoord_strictMono hL (hgamma hjl)

  have h := hcert x hxmono

  have hspan :
      dutNormalizedSixSpan P T gamma
        = x 5 - x 0 := by
    dsimp [x]
    exact dutNormalizedSixSpan_eq_verifierCoord_span P T gamma

  have hmat :
      dutSharpMatrixOfOrdinates P T gamma
        = dutScaleFreeSharpMatrix P.lam x := by
    dsimp [x]
    exact dutSharpMatrixOfOrdinates_eq_scaleFree P hP hL gamma

  rw [hspan, hmat]
  exact h

/-- The successful external verifier run is therefore aimed at exactly the
certificate needed by the concrete fixed-lambda parameter family. -/
theorem dutFixedSharpVerifierCertificate_of_scaleFree
    (hcert : DUTFixedScaleFreeSharpCertificate) :
    DUTSharpVerifierCertificate
      (paramsOf stdProfile dutVerifierLam) := by
  have h0 : 0 < dutVerifierLam := by
    linarith [dutVerifierLam_half_le]
  have hP :
      (paramsOf stdProfile dutVerifierLam).Valid :=
    paramsOf_valid taperProfile_stdProfile
      h0 dutVerifierLam_lt_one.le
  exact
    dutSharpVerifierCertificate_of_scaleFree
      (paramsOf stdProfile dutVerifierLam) hP hcert

/-- Final 67.27918% theorem with the external boundary stated in the exact
dimensionless form checked by the Arb verifier. -/
theorem dut_thmD₀_simple_6727918_of_scaleFree_certificate
    (hcert : DUTFixedScaleFreeSharpCertificate) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3363959 : ℝ) / 5000000 - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  exact
    dut_thmD₀_simple_6727918_fixed
      (dutFixedSharpVerifierCertificate_of_scaleFree hcert)

end Zeta23.ZeroSide.RankTraceMult
