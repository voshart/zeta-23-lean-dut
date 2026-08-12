/-
DUTSharpCertificateSeam.lean

Precise Lean contract for the remaining external six-point computation.

The rigorous external verifier works in normalized ordinate coordinates:
if gamma_0 < ... < gamma_5, its span variable is

    span = (L / (2*pi)) * (gamma_5 - gamma_0).

This file makes the computer-assisted seam explicit.

The external verifier certifies the stronger cutoff `dutVerifierR = 9.45`,
while Lean consumes the buffered cutoff `dutR = 9.40`.  Below the Lean cutoff,
the difference is the fixed rational margin `dutCertificateTransferSlack`.
At or beyond the Lean cutoff the target saving is zero, so no transfer margin
is needed.

Intended location:
  Zeta23/ZeroSide/DUTSharpCertificateSeam.lean
-/

import Zeta23.ZeroSide.DUTCoreCertifiedBlocks

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The dimensionless six-point span used by the external verifier:
physical ordinate length multiplied by `L/(2*pi)`. -/
noncomputable def dutNormalizedSixSpan
    (P : Params) (T : ℝ) (gamma : Fin 6 → ℝ) : ℝ :=
  (P.L T / (2 * Real.pi)) * (gamma 5 - gamma 0)

/-- Matrix obtained by evaluating the exact normalized sharp Theorem-D kernel
on an arbitrary six-tuple of real ordinates. -/
noncomputable def dutSharpMatrixOfOrdinates
    (P : Params) (T : ℝ) (gamma : Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  fun j l => (dutDSharpKernel P T (gamma j - gamma l) : ℂ)

/-- **Exact external verifier contract.**

This states only the inequality actually checked by the rigorous external
interval/integer verifier, using the verifier cutoff `dutVerifierR = 189/20`.
No extra uniform additive slack is assumed. -/
def DUTSharpVerifierCertificate (P : Params) : Prop :=
  ∀ (T : ℝ), 0 < P.L T →
    ∀ gamma : Fin 6 → ℝ, StrictMono gamma →
      dutVerifierCertificateRhs (dutNormalizedSixSpan P T gamma)
        ≤ dutGramEnergy (dutSharpMatrixOfOrdinates P T gamma)

/-- The canonical core ordering is strictly increasing in ordinate. -/
lemma dutCoreOrderedZero_im_strictMono
    (Z : ZeroConfig) (T : ℝ) :
    StrictMono
      (fun k : Fin (dutCoreCount Z T) =>
        (dutCoreOrderedZero Z T k).im) := by
  intro a b hab
  change
    (((dutCoreOrderIso Z T) a : DUTCoreSimpleZero Z T) : ℂ).im <
      (((dutCoreOrderIso Z T) b : DUTCoreSimpleZero Z T) : ℂ).im
  change (dutCoreOrderIso Z T a) < (dutCoreOrderIso Z T b)
  exact (dutCoreOrderIso Z T).strictMono hab

/-- Hence every consecutive six-block in the core is strictly increasing. -/
lemma dutCoreSix_im_strictMono
    (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    StrictMono
      (fun j : Fin 6 =>
        ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im) := by
  intro j l hjl
  apply dutCoreOrderedZero_im_strictMono Z T
  unfold dutCoreSixIndex
  simp only [Fin.mk_lt_mk]
  omega

/-- The actual normalized span of a core six-block. -/
noncomputable def dutCoreSixNormalizedSpan
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) : ℝ :=
  dutNormalizedSixSpan P T
    (fun j : Fin 6 =>
      ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im)

/-- The actual core six-span is nonnegative whenever `L > 0`. -/
lemma dutCoreSixNormalizedSpan_nonneg
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    0 ≤ dutCoreSixNormalizedSpan Z T P i hi := by
  have hmono := dutCoreSix_im_strictMono Z T i hi
  have h05 :
      ((dutCoreSixZI Z T i hi (0 : Fin 6) : ZI Z T) : ℂ).im
        <
      ((dutCoreSixZI Z T i hi (5 : Fin 6) : ZI Z T) : ℂ).im := by
    exact hmono (by decide)
  unfold dutCoreSixNormalizedSpan dutNormalizedSixSpan
  have hscale : 0 ≤ P.L T / (2 * Real.pi) := by positivity
  exact mul_nonneg hscale (sub_nonneg.mpr h05.le)

/-- The arbitrary-ordinate sharp matrix specializes definitionally to the
concrete core sharp matrix. -/
lemma dutSharpMatrixOfOrdinates_core
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    dutSharpMatrixOfOrdinates P T
        (fun j : Fin 6 =>
          ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im)
      =
    dutCoreSixSharpMatrix Z T P i hi := by
  rfl

/-- The verifier certificate specializes to every actual core
six-block. -/
lemma dutCoreSix_sharp_energy_of_verifier_certificate
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hcert : DUTSharpVerifierCertificate P)
    (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    dutVerifierCertificateRhs
        (dutCoreSixNormalizedSpan Z T P i hi)
      ≤ dutGramEnergy (dutCoreSixSharpMatrix Z T P i hi) := by
  have h :=
    hcert T hL
      (fun j : Fin 6 =>
        ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im)
      (dutCoreSix_im_strictMono Z T i hi)
  simpa [dutCoreSixNormalizedSpan,
    dutSharpMatrixOfOrdinates_core] using h

/-- **Verifier certificate + buffered transfer control -> actual local DUT saving.**

If the matrix-transfer loss is at most the fixed rational budget created by
the `9.45 -> 9.40` cutoff buffer, the actual core block obtains both DUT
charge savings. -/
theorem dutCoreSix_certificate_of_external_sharp
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hcert : DUTSharpVerifierCertificate P)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 : 0 < D0 T - 2 * (P.atD T).hgrid T)
    (hdelta : 0 ≤ dutCoreSixEntryError T P)
    (hloss :
      dutCoreSixTransferLoss T P ≤ dutCertificateTransferSlack)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    let v := dutCoreSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j))
      ≤ 18 - dutCertificateRhs
        (dutCoreSixNormalizedSpan Z T P i hi)
      ∧
    (∑ j, kc 3 (xsq vr j))
      ≤ 30 - dutCertificateRhs
        (dutCoreSixNormalizedSpan Z T P i hi) := by
  have h8 : 8 * P.w ≤ P.L T := by
    have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
    linarith
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  let span := dutCoreSixNormalizedSpan Z T P i hi
  have hspan0 : 0 ≤ span := by
    dsimp [span]
    exact dutCoreSixNormalizedSpan_nonneg Z T P hL i hi

  by_cases hcut : span < dutR
  · have hver :
        dutVerifierCertificateRhs span
          ≤ dutGramEnergy (dutCoreSixSharpMatrix Z T P i hi) := by
      dsimp [span]
      exact
        dutCoreSix_sharp_energy_of_verifier_certificate
          Z T P hcert hL i hi
    have hmargin :
        dutCertificateRhs span + dutCoreSixTransferLoss T P
          ≤ dutVerifierCertificateRhs span := by
      have hbuf :=
        dutCertificateRhs_add_slack_le_verifierRhs hcut
      linarith
    have hsharp :
        dutCertificateRhs span + dutCoreSixTransferLoss T P
          ≤ dutGramEnergy (dutCoreSixSharpMatrix Z T P i hi) :=
      hmargin.trans hver
    exact
      dutCoreSix_certificate_of_sharp_margin
        Z T P hP hT h16 h4pi hgap2 hdelta
        i hi span hspan0 hsharp
  · have hge : dutR ≤ span := le_of_not_gt hcut
    have hrhs0 : dutCertificateRhs span = 0 :=
      dutCertificateRhs_eq_zero_of_ge hge
    have hgram0 :
        0 ≤ dutGramEnergy (dutCoreSixGramMatrixD Z T P i hi) := by
      rw [← dutSpectralEnergy_coreSpectrum_eq]
      unfold dutSpectralEnergy
      positivity
    have henergy :
        dutCertificateRhs span
          ≤ dutGramEnergy (dutCoreSixGramMatrixD Z T P i hi) := by
      rw [hrhs0]
      exact hgram0
    exact
      dutCoreSix_certificate_of_gram_energy
        Z T P hP h8 h4pi i hi span hspan0 henergy

end Zeta23.ZeroSide.RankTraceMult
