/-
DUTSelfBootstrap.lean

Pure algebra for the global DUT endgame.

Starting from the strengthened fixed-T inequality

  (2 - cinv) N - E
    + (eta/6) * (R * (N0s - boundary - 5) - 5 * length)
    <= N0s,

move the N0s contribution in the saving to the right.  This isolates the
exact denominator

  1 - (eta/6) R

and the main numerator

  2 - c^{-1} - 5 (eta/6) lambda.

No asymptotics occur here.

Intended location:
  Zeta23/ZeroSide/DUTSelfBootstrap.lean
-/

import Zeta23.ZeroSide.DUTAssemblyC

noncomputable section
set_option linter.unusedSectionVars false

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The phase-averaged coefficient `eta / 6`. -/
def dutBeta : ℝ := dutEta / 6

/-- Coefficient of `N0s` contributed by the DUT saving. -/
def dutQ : ℝ := dutBeta * dutR

/-- Positive denominator after moving the DUT `N0s` contribution right. -/
def dutDen : ℝ := 1 - dutQ

/-- Main asymptotic numerator before dividing by `dutDen`. -/
def dutNumer (c lam : ℝ) : ℝ :=
  2 - c⁻¹ - 5 * dutBeta * lam

/-- Final fixed-lambda DUT rate associated with a limiting ratio constant `c`. -/
def dutRate (c lam : ℝ) : ℝ :=
  dutNumer c lam / dutDen

lemma dutBeta_nonneg : 0 ≤ dutBeta := by
  exact div_nonneg dutEta_nonneg (by norm_num)

lemma dutQ_nonneg : 0 ≤ dutQ := by
  exact mul_nonneg dutBeta_nonneg dutR_nonneg

lemma dutDen_pos : 0 < dutDen := by
  norm_num [dutDen, dutQ, dutBeta, dutEta, dutR]

lemma dutDen_ne : dutDen ≠ 0 :=
  dutDen_pos.ne'

/-- Exact self-bootstrap rearrangement.

The signed drift terms are deliberately kept signed: each will later be
`o(N)`, so absolute values are unnecessary at this algebraic stage. -/
theorem dut_self_bootstrap_rearrange
    {N N0s cinv c lam baseErr boundary length : ℝ}
    (h :
      (2 - cinv) * N - baseErr
        + dutBeta *
            (dutR * (N0s - boundary - 5) - 5 * length)
        ≤ N0s) :
    dutNumer c lam * N
        -
        (baseErr
          + (cinv - c⁻¹) * N
          + dutQ * boundary
          + 5 * dutQ
          + 5 * dutBeta * (length - lam * N))
      ≤ dutDen * N0s := by
  have hid :
      (dutNumer c lam * N
          -
          (baseErr
            + (cinv - c⁻¹) * N
            + dutQ * boundary
            + 5 * dutQ
            + 5 * dutBeta * (length - lam * N)))
          - dutDen * N0s
        =
      ((2 - cinv) * N - baseErr
          + dutBeta *
              (dutR * (N0s - boundary - 5) - 5 * length))
          - N0s := by
    simp only [dutNumer, dutDen, dutQ]
    ring

  have h0 :
      ((2 - cinv) * N - baseErr
          + dutBeta *
              (dutR * (N0s - boundary - 5) - 5 * length))
          - N0s ≤ 0 :=
    sub_nonpos.mpr h

  rw [← hid] at h0
  exact sub_nonpos.mp h0

/-- Divide a scaled lower bound by the positive DUT denominator. -/
theorem dut_divide_scaled_bound
    {A N N0s err : ℝ}
    (h : A * N - err ≤ dutDen * N0s) :
    (A / dutDen) * N - err / dutDen ≤ N0s := by
  have heq :
      ((A / dutDen) * N - err / dutDen) * dutDen
        = A * N - err := by
    field_simp [dutDen_ne]
    <;> ring
  nlinarith [dutDen_pos]

end Zeta23.ZeroSide.RankTraceMult
