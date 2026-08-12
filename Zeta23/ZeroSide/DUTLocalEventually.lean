/-
DUTLocalEventually.lean

Package all asymptotic hypotheses needed by the local six-zero certificate.

For fixed valid Theorem-D parameters P and an external sharp verifier
certificate, all analytic side conditions eventually hold simultaneously:

  * T > 0;
  * 16 w <= L(T);
  * 4 pi w <= L(T);
  * sqrt(T) - 2 hgrid(T) > 0;
  * dutCoreSixEntryError(T,P) >= 0;
  * dutCoreSixTransferLoss(T,P) <= dutCertificateTransferSlack.

Hence every actual consecutive interior-core six-block eventually satisfies
the c=2 and c=3 charge savings from DUTSharpCertificateSeam.

This is the final local/asymptotic wrapper before global phase bookkeeping.

Intended location:
  Zeta23/ZeroSide/DUTLocalEventually.lean
-/

import Zeta23.ZeroSide.DUTEntryErrorLimit

noncomputable section
set_option linter.unusedSectionVars false

open Filter Matrix Finset RHLinalg
open scoped Topology BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The full collection of analytic hypotheses required by
`dutCoreSix_certificate_of_external_sharp` holds eventually. -/
lemma dutCoreSix_local_hypotheses_eventually
    (P : Params) (hP : P.Valid) :
    ∀ᶠ T : ℝ in atTop,
      0 < T
      ∧ 16 * P.w ≤ P.L T
      ∧ 4 * Real.pi * P.w ≤ P.L T
      ∧ 0 < D0 T - 2 * (P.atD T).hgrid T
      ∧ 0 ≤ dutCoreSixEntryError T P
      ∧ dutCoreSixTransferLoss T P ≤ dutCertificateTransferSlack := by
  have hLtop : Tendsto (P.L) atTop atTop :=
    Assembly.tendsto_L_atTop P hP.lam_pos

  have hh0 :
      Tendsto (fun T : ℝ => (P.atD T).hgrid T)
        atTop (𝓝 0) := by
    have h :=
      hLtop.const_div_atTop (2 * Real.pi)
    simpa [Params.atD_hgrid, Params.hgrid] using h

  have hT1 : ∀ᶠ T : ℝ in atTop, 1 ≤ T :=
    eventually_ge_atTop 1

  have h16 :
      ∀ᶠ T : ℝ in atTop, 16 * P.w ≤ P.L T :=
    hLtop.eventually
      (eventually_ge_atTop (16 * P.w))

  have h4pi :
      ∀ᶠ T : ℝ in atTop,
        4 * Real.pi * P.w ≤ P.L T :=
    hLtop.eventually
      (eventually_ge_atTop (4 * Real.pi * P.w))

  have hhsmall :
      ∀ᶠ T : ℝ in atTop,
        (P.atD T).hgrid T ≤ 1 / 4 := by
    exact
      hh0.eventually
        (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))

  have hloss :
      ∀ᶠ T : ℝ in atTop,
        dutCoreSixTransferLoss T P ≤ dutCertificateTransferSlack :=
    dutCoreSixTransferLoss_eventually_le_buffer P hP

  filter_upwards [hT1, h16, h4pi, hhsmall, hloss]
    with T hT1T h16T h4piT hhsmallT hlossT

  have hT : 0 < T :=
    lt_of_lt_of_le zero_lt_one hT1T

  have h8 : 8 * P.w ≤ P.L T := by
    have hw0 : 0 ≤ P.w :=
      le_trans zero_le_one hP.one_le_w
    linarith

  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]

  have hh : 0 < (P.atD T).hgrid T := by
    simp only [Params.atD_hgrid, Params.hgrid]
    positivity

  have hsqrt1 : 1 ≤ D0 T := by
    unfold D0
    have hs := Real.sq_sqrt hT.le
    have hs0 := Real.sqrt_nonneg T
    nlinarith

  have hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T := by
    linarith

  have ha12 : 1 / 2 ≤ (P.atD T).a T :=
    (ThmD.aD_range_of hP h8 h4piT).1

  have ha : 0 < (P.atD T).a T := by
    linarith

  have hraw :
      0 ≤ dutCoreSixRawTailBudget T P :=
    dutCoreSixRawTailBudget_nonneg
      T P (Real.sqrt_pos.2 hT) hh hgap2

  have hnormden :
      0 < (P.atD T).a T * (P.atD T).L T ^ 2 := by
    simp only [Params.atD_L]
    positivity

  have htail :
      0 ≤ dutCoreSixNormalizedTailBudget T P := by
    unfold dutCoreSixNormalizedTailBudget
    exact div_nonneg hraw hnormden.le

  have htaper :
      0 ≤ 40 * P.w / P.L T := by
    have hw0 : 0 ≤ P.w :=
      le_trans zero_le_one hP.one_le_w
    exact div_nonneg (mul_nonneg (by norm_num) hw0) hL.le

  have hdelta :
      0 ≤ dutCoreSixEntryError T P := by
    unfold dutCoreSixEntryError
    linarith

  exact
    ⟨hT, h16T, h4piT, hgap2, hdelta, hlossT⟩

/-- **Eventually every actual interior-core six-block satisfies the verified
local DUT certificate.** -/
theorem dutCoreSix_certificate_eventually
    (P : Params) (hP : P.Valid)
    (hcert : DUTSharpVerifierCertificate P) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (Z : ZeroConfig)
        (i : ℕ) (hi : i + 5 < dutCoreCount Z T),
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
  filter_upwards [dutCoreSix_local_hypotheses_eventually P hP]
    with T hT
  rcases hT with
    ⟨hTpos, h16, h4pi, hgap2, hdelta, hloss⟩
  intro Z i hi
  exact
    dutCoreSix_certificate_of_external_sharp
      Z T P hP hcert
      hTpos h16 h4pi hgap2 hdelta hloss
      i hi

end Zeta23.ZeroSide.RankTraceMult
