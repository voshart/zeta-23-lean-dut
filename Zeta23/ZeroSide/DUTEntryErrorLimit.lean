/-
DUTEntryErrorLimit.lean

Concrete asymptotic closure of the interior finite-grid/sharp-kernel transfer.

For fixed valid parameters P, the uniform entrywise error

    dutCoreSixEntryError T P
      = normalized finite-grid tail + 40 w / L

tends to zero as T -> infinity.

The key pointwise estimate is deliberately coarse.  Once
  * T >= 1,
  * a_D >= 1/2,
  * hgrid <= 1/4,

the right omitted-grid gap satisfies

    sqrt(T) - 2 hgrid >= sqrt(T)/2,

and cancellation of hgrid = 2*pi/L against the normalization L^2 gives

    normalized tail <= 5 * dutDTailConst(P)^2 / T.

Both this term and 40 w / L tend to zero.

Intended location:
  Zeta23/ZeroSide/DUTEntryErrorLimit.lean
-/

import Zeta23.ZeroSide.DUTTransferLossLimit
import Zeta23.ThmD.Endgame

noncomputable section
set_option linter.unusedSectionVars false

open Filter
open scoped Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23

/-- Exact algebraic form of the normalized two-sided tail after cancelling
`hgrid^2 * L^2 = (2*pi)^2`. -/
private lemma dutCoreSixNormalizedTailBudget_formula
    (T : ℝ) (P : Params)
    (hT : 0 < T)
    (hL : 0 < P.L T)
    (ha : 0 < (P.atD T).a T)
    (hgap : 0 < D0 T - 2 * (P.atD T).hgrid T) :
    dutCoreSixNormalizedTailBudget T P
      =
      (dutDTailConst P) ^ 2 /
        (2 * Real.pi ^ 2 * (P.atD T).a T * T)
      +
      (dutDTailConst P) ^ 2 /
        (2 * Real.pi ^ 2 * (P.atD T).a T *
          (D0 T - 2 * (P.atD T).hgrid T) ^ 2) := by
  unfold dutCoreSixNormalizedTailBudget dutCoreSixRawTailBudget
  simp only [Params.atD_hgrid, Params.atD_L]
  have hDsq : D0 T ^ 2 = T := by
    simp [D0, Real.sq_sqrt hT.le]
  rw [hDsq]
  unfold Params.hgrid
  field_simp [hT.ne', hL.ne', ha.ne', hgap.ne', Real.pi_ne_zero]

/-- Coarse pointwise tail estimate sufficient for the limit proof. -/
private lemma dutCoreSixNormalizedTailBudget_le_inv
    (T : ℝ) (P : Params) (hP : P.Valid)
    (hT1 : 1 ≤ T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hhsmall : (P.atD T).hgrid T ≤ 1 / 4) :
    dutCoreSixNormalizedTailBudget T P
      ≤ 5 * (dutDTailConst P) ^ 2 / T := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
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
  have hgap_half :
      D0 T / 2 ≤ D0 T - 2 * (P.atD T).hgrid T := by
    linarith
  have hgap : 0 < D0 T - 2 * (P.atD T).hgrid T := by
    have : 0 < D0 T / 2 := by positivity
    linarith

  have ha12 : 1 / 2 ≤ (P.atD T).a T :=
    (ThmD.aD_range_of hP h8 h4pi).1
  have ha : 0 < (P.atD T).a T := by
    linarith

  let C2 : ℝ := (dutDTailConst P) ^ 2
  have hC2 : 0 ≤ C2 := by
    dsimp [C2]
    positivity

  have hpi2 : 1 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have h2a : 1 ≤ 2 * (P.atD T).a T := by
    linarith
  have hcoef :
      1 ≤ 2 * Real.pi ^ 2 * (P.atD T).a T := by
    have hm :=
      mul_le_mul_of_nonneg_left h2a (sq_nonneg Real.pi)
    nlinarith

  have hden1 :
      T ≤ 2 * Real.pi ^ 2 * (P.atD T).a T * T := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hcoef hT.le)

  have hterm1 :
      C2 / (2 * Real.pi ^ 2 * (P.atD T).a T * T)
        ≤ C2 / T := by
    exact div_le_div_of_nonneg_left hC2 hT hden1

  have hDsq : D0 T ^ 2 = T := by
    simp [D0, Real.sq_sqrt hT.le]

  have hgap_sq :
      T / 4 ≤ (D0 T - 2 * (P.atD T).hgrid T) ^ 2 := by
    have hhalf0 : 0 ≤ D0 T / 2 := by positivity
    have hsq :
        (D0 T / 2) ^ 2
          ≤ (D0 T - 2 * (P.atD T).hgrid T) ^ 2 := by
      nlinarith [sq_nonneg
        ((D0 T - 2 * (P.atD T).hgrid T) - D0 T / 2)]
    rw [div_pow, hDsq] at hsq
    norm_num at hsq ⊢
    exact hsq

  have hden2 :
      T / 4
        ≤ 2 * Real.pi ^ 2 * (P.atD T).a T *
            (D0 T - 2 * (P.atD T).hgrid T) ^ 2 := by
    calc
      T / 4
          ≤ (D0 T - 2 * (P.atD T).hgrid T) ^ 2 := hgap_sq
      _ ≤ 2 * Real.pi ^ 2 * (P.atD T).a T *
            (D0 T - 2 * (P.atD T).hgrid T) ^ 2 := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hcoef
            (sq_nonneg (D0 T - 2 * (P.atD T).hgrid T)))

  have hterm2a :
      C2 /
          (2 * Real.pi ^ 2 * (P.atD T).a T *
            (D0 T - 2 * (P.atD T).hgrid T) ^ 2)
        ≤ C2 / (T / 4) := by
    exact
      div_le_div_of_nonneg_left hC2 (by positivity) hden2

  have hterm2 :
      C2 /
          (2 * Real.pi ^ 2 * (P.atD T).a T *
            (D0 T - 2 * (P.atD T).hgrid T) ^ 2)
        ≤ 4 * C2 / T := by
    calc
      _ ≤ C2 / (T / 4) := hterm2a
      _ = 4 * C2 / T := by
        field_simp [hT.ne']

  have hsum :
      (dutDTailConst P) ^ 2 /
          (2 * Real.pi ^ 2 * (P.atD T).a T * T)
        +
      (dutDTailConst P) ^ 2 /
          (2 * Real.pi ^ 2 * (P.atD T).a T *
            (D0 T - 2 * (P.atD T).hgrid T) ^ 2)
        ≤
      (dutDTailConst P) ^ 2 / T
        + 4 * (dutDTailConst P) ^ 2 / T := by
    have hterm2' :
        (dutDTailConst P) ^ 2 /
            (2 * Real.pi ^ 2 * (P.atD T).a T *
              (D0 T - 2 * (P.atD T).hgrid T) ^ 2)
          ≤ 4 * (dutDTailConst P) ^ 2 / T := by
      simpa only [C2, Params.atD_hgrid] using hterm2
    have hterm1' :
        (dutDTailConst P) ^ 2 /
            (2 * Real.pi ^ 2 * (P.atD T).a T * T)
          ≤ (dutDTailConst P) ^ 2 / T := by
      simpa only [C2] using hterm1
    exact add_le_add hterm1' hterm2'
  calc
    dutCoreSixNormalizedTailBudget T P
        =
        (dutDTailConst P) ^ 2 /
            (2 * Real.pi ^ 2 * (P.atD T).a T * T)
          +
        (dutDTailConst P) ^ 2 /
            (2 * Real.pi ^ 2 * (P.atD T).a T *
              (D0 T - 2 * (P.atD T).hgrid T) ^ 2) :=
      dutCoreSixNormalizedTailBudget_formula T P hT hL ha hgap
    _ ≤ (dutDTailConst P) ^ 2 / T
          + 4 * (dutDTailConst P) ^ 2 / T := hsum
    _ = 5 * (dutDTailConst P) ^ 2 / T := by ring

/-- The normalized finite-grid tail tends to zero. -/
lemma dutCoreSixNormalizedTailBudget_tendsto_zero
    (P : Params) (hP : P.Valid) :
    Tendsto
      (fun T : ℝ => dutCoreSixNormalizedTailBudget T P)
      atTop (𝓝 0) := by
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
  have h8 : ∀ᶠ T : ℝ in atTop, 8 * P.w ≤ P.L T :=
    hLtop.eventually (eventually_ge_atTop (8 * P.w))
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

  have hnonneg :
      ∀ᶠ T : ℝ in atTop,
        0 ≤ dutCoreSixNormalizedTailBudget T P := by
    filter_upwards [hT1, h8, h4pi, hhsmall]
      with T hT1T h8T h4piT hhT
    have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1T
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
    have hgap :
        0 < D0 T - 2 * (P.atD T).hgrid T := by
      linarith
    have hraw :=
      dutCoreSixRawTailBudget_nonneg T P
        (Real.sqrt_pos.2 hT) hh hgap
    have ha12 : 1 / 2 ≤ (P.atD T).a T :=
      (ThmD.aD_range_of hP h8T h4piT).1
    have hden :
        0 < (P.atD T).a T * (P.atD T).L T ^ 2 := by
      have ha : 0 < (P.atD T).a T := by linarith
      simp only [Params.atD_L]
      positivity
    unfold dutCoreSixNormalizedTailBudget
    exact div_nonneg hraw hden.le

  have hupper :
      ∀ᶠ T : ℝ in atTop,
        dutCoreSixNormalizedTailBudget T P
          ≤ 5 * (dutDTailConst P) ^ 2 / T := by
    filter_upwards [hT1, h8, h4pi, hhsmall]
      with T hT1T h8T h4piT hhT
    exact
      dutCoreSixNormalizedTailBudget_le_inv
        T P hP hT1T h8T h4piT hhT

  have hup :
      Tendsto
        (fun T : ℝ => 5 * (dutDTailConst P) ^ 2 / T)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_id.const_div_atTop
        (5 * (dutDTailConst P) ^ 2))

  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup
      hnonneg hupper

/-- **Concrete entrywise Gram/sharp error tends to zero.** -/
theorem dutCoreSixEntryError_tendsto_zero
    (P : Params) (hP : P.Valid) :
    Tendsto (fun T : ℝ => dutCoreSixEntryError T P)
      atTop (𝓝 0) := by
  have htail :=
    dutCoreSixNormalizedTailBudget_tendsto_zero P hP
  have hLtop : Tendsto (P.L) atTop atTop :=
    Assembly.tendsto_L_atTop P hP.lam_pos
  have htaper :
      Tendsto (fun T : ℝ => 40 * P.w / P.L T)
        atTop (𝓝 0) := by
    simpa using hLtop.const_div_atTop (40 * P.w)
  simpa [dutCoreSixEntryError] using htail.add htaper

/-- Hence the concrete matrix-transfer loss eventually fits into the buffered
certificate budget. -/
theorem dutCoreSixTransferLoss_eventually_le_buffer
    (P : Params) (hP : P.Valid) :
    ∀ᶠ T : ℝ in atTop,
      dutCoreSixTransferLoss T P ≤ dutCertificateTransferSlack :=
  dutCoreSixTransferLoss_eventually_le_slack_of_entryError
    P (dutCoreSixEntryError_tendsto_zero P hP)

end Zeta23.ZeroSide.RankTraceMult
