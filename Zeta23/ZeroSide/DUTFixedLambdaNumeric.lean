/-
DUTFixedLambdaNumeric.lean

Pin the one-certificate DUT finish line to one explicit rational parameter

  lambda_DUT = 999999999 / 1000000000.

The numerical headline file proves a small certified margin at lambda = 1.
Anthropic's cStar Lipschitz theorem then transports enough of that margin
to this explicit rational lambda.

The resulting final theorem has exactly one remaining external input:
the finite six-point verifier certificate at `dutVerifierLam`.

Intended location:
  Zeta23/ZeroSide/DUTFixedLambdaNumeric.lean
-/

import Zeta23.ZeroSide.DUTFinalOneCertificate
import Zeta23.ZeroSide.DUTHeadlineNumeric

noncomputable section
set_option linter.unusedSectionVars false

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Concrete rational lambda used for the final finite verifier. -/
def dutVerifierLam : ℝ :=
  999999999 / 1000000000

lemma dutVerifierLam_half_le :
    (1 : ℝ) / 2 ≤ dutVerifierLam := by
  norm_num [dutVerifierLam]

lemma dutVerifierLam_lt_one :
    dutVerifierLam < 1 := by
  norm_num [dutVerifierLam]

/-- The explicit fixed lambda still clears the 67.27918% target. -/
theorem dutRate_dutVerifierLam_gt_6727918 :
    (3363959 : ℝ) / 5000000
      < dutRate (ThmD.cStar dutVerifierLam) dutVerifierLam := by
  have hlam0 : 0 ≤ dutVerifierLam := by
    norm_num [dutVerifierLam]
  have hlam1 : dutVerifierLam ≤ 1 := by
    norm_num [dutVerifierLam]

  have hcLip :=
    ThmD.cStar_lipschitzOn
      hlam0 hlam1
      (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1)

  have hcLip' :
      |ThmD.cStar dutVerifierLam - ThmD.cStar 1|
        ≤ (7 : ℝ) / 500000000 := by
    calc
      |ThmD.cStar dutVerifierLam - ThmD.cStar 1|
          ≤ 14 * |dutVerifierLam - 1| := hcLip
      _ = (7 : ℝ) / 500000000 := by
        norm_num [dutVerifierLam]

  have hheadline :
      dutHeadlineRate
        =
      (ThmD.HD 1 - 9 / 8000)
        / (199577 / 200000) := by
    simp only [
      dutHeadlineRate, dutRate, dutNumer, dutDen, dutQ, dutBeta,
      dutEta, dutR, ThmD.HD, one_div
    ]
    ring

  have hden :
      (0 : ℝ) < 199577 / 200000 := by
    norm_num

  have hstrong := dutHeadlineRate_gt_6727928
  rw [hheadline] at hstrong
  rw [lt_div_iff₀ hden] at hstrong

  have hHD23 :
      (2 : ℝ) / 3 < ThmD.HD 1 := by
    norm_num at hstrong ⊢
    linarith

  have hc1pos :
      0 < ThmD.cStar 1 :=
    ThmD.cStar_pos (by norm_num) (by norm_num)

  have hinv :
      (ThmD.cStar 1)⁻¹ < (4 : ℝ) / 3 := by
    simp only [ThmD.HD, one_div] at hHD23
    linarith

  have hc1low :
      (3 : ℝ) / 4 < ThmD.cStar 1 := by
    have hm :=
      mul_lt_mul_of_pos_right hinv hc1pos
    have hcancel :
        (ThmD.cStar 1)⁻¹ * ThmD.cStar 1 = 1 := by
      exact inv_mul_cancel₀ hc1pos.ne'
    rw [hcancel] at hm
    nlinarith

  have hnum :
      ThmD.cStar 1 - ThmD.cStar dutVerifierLam
        ≤ (7 : ℝ) / 500000000 := by
    have hh := (abs_le.mp hcLip').1
    linarith

  have hclamlow :
      (7 : ℝ) / 10 < ThmD.cStar dutVerifierLam := by
    linarith [hc1low, hnum]

  have hclampos :
      0 < ThmD.cStar dutVerifierLam := by
    linarith [hclamlow]

  have hc1low7 :
      (7 : ℝ) / 10 < ThmD.cStar 1 := by
    linarith [hc1low]

  have hprod :
      (49 : ℝ) / 100
        < ThmD.cStar dutVerifierLam * ThmD.cStar 1 := by
    calc
      (49 : ℝ) / 100
          = ((7 : ℝ) / 10) * ((7 : ℝ) / 10) := by norm_num
      _ < ThmD.cStar dutVerifierLam * ((7 : ℝ) / 10) :=
        mul_lt_mul_of_pos_right hclamlow (by norm_num)
      _ < ThmD.cStar dutVerifierLam * ThmD.cStar 1 :=
        mul_lt_mul_of_pos_left hc1low7 hclampos

  have hHDid :
      (ThmD.HD 1 - ThmD.HD dutVerifierLam)
          * (ThmD.cStar dutVerifierLam * ThmD.cStar 1)
        =
      ThmD.cStar 1 - ThmD.cStar dutVerifierLam := by
    simp only [ThmD.HD]
    field_simp [hc1pos.ne', hclampos.ne']
    <;> ring

  have hHDloss :
      ThmD.HD 1 - ThmD.HD dutVerifierLam
        < (1 : ℝ) / 20000000 := by
    by_cases hnonpos :
        ThmD.HD 1 - ThmD.HD dutVerifierLam ≤ 0
    · linarith
    · have hdpos :
          0 < ThmD.HD 1 - ThmD.HD dutVerifierLam :=
        lt_of_not_ge hnonpos
      have hm :
          ((49 : ℝ) / 100)
              * (ThmD.HD 1 - ThmD.HD dutVerifierLam)
            <
          (ThmD.cStar dutVerifierLam * ThmD.cStar 1)
              * (ThmD.HD 1 - ThmD.HD dutVerifierLam) :=
        mul_lt_mul_of_pos_right hprod hdpos
      have hid' :
          (ThmD.cStar dutVerifierLam * ThmD.cStar 1)
              * (ThmD.HD 1 - ThmD.HD dutVerifierLam)
            =
          ThmD.cStar 1 - ThmD.cStar dutVerifierLam := by
        rw [mul_comm]
        exact hHDid
      rw [hid'] at hm
      norm_num at hm hnum ⊢
      linarith

  have hrateLam :
      dutRate (ThmD.cStar dutVerifierLam) dutVerifierLam
        =
      (ThmD.HD dutVerifierLam - (9 / 8000) * dutVerifierLam)
        / (199577 / 200000) := by
    simp only [
      dutRate, dutNumer, dutDen, dutQ, dutBeta,
      dutEta, dutR, ThmD.HD, one_div
    ]
    ring

  have hlamNumer :
      (6713697 : ℝ) / 10000000
        <
      ThmD.HD dutVerifierLam
        - (9 / 8000) * dutVerifierLam := by
    norm_num [dutVerifierLam] at hstrong hHDloss ⊢
    linarith

  rw [hrateLam, lt_div_iff₀ hden]
  have htarget :
      ((3363959 : ℝ) / 5000000)
          * (199577 / 200000)
        < (6713697 : ℝ) / 10000000 := by
    norm_num
  exact htarget.trans hlamNumer

/-- Final explicit one-certificate theorem.

After this point the only remaining hypothesis is the finite rigorous
six-point verifier certificate at the concrete rational `dutVerifierLam`. -/
theorem dut_thmD₀_simple_6727918_fixed
    (hcert :
      DUTSharpVerifierCertificate
        (paramsOf stdProfile dutVerifierLam)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3363959 : ℝ) / 5000000 - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  exact
    dut_thmD₀_simple_6727918_of_one_certificate
      dutVerifierLam_half_le
      dutVerifierLam_lt_one
      hcert
      dutRate_dutVerifierLam_gt_6727918

end Zeta23.ZeroSide.RankTraceMult
