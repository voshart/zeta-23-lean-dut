/-
DUTFinalHeadline.lean

Lambda -> 1^- headline form for the DUT-strengthened simple-zero theorem.

The external verifier remains an explicit hypothesis, uniformly for the
standard Montgomery--Taylor family over lambda in [1/2,1).

Intended location:
  Zeta23/ZeroSide/DUTFinalHeadline.lean
-/

import Zeta23.ZeroSide.DUTFinalLam
import Zeta23.ThmD.Limit

noncomputable section
set_option linter.unusedSectionVars false

open Filter Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Exact limiting DUT headline rate. -/
def dutHeadlineRate : ℝ :=
  dutRate (ThmD.cStar 1) 1

/-- Continuity at lambda = 1 of the DUT rate along the admissible interval. -/
lemma dutRate_cStar_continuousWithinAt_one :
    ContinuousWithinAt
      (fun lam : ℝ => dutRate (ThmD.cStar lam) lam)
      (Set.Icc 0 1) 1 := by
  have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨zero_le_one, le_rfl⟩
  have hc :
      ContinuousWithinAt
        ThmD.cStar (Set.Icc 0 1) 1 :=
    ThmD.cStar_continuousOn 1 hmem
  have hc1 : ThmD.cStar 1 ≠ 0 :=
    (ThmD.cStar_pos one_pos le_rfl).ne'
  have hcinv :
      ContinuousWithinAt
        (fun lam : ℝ => (ThmD.cStar lam)⁻¹)
        (Set.Icc 0 1) 1 := by
    exact hc.inv₀ hc1
  have hnum :
      ContinuousWithinAt
        (fun lam : ℝ =>
          2 - (ThmD.cStar lam)⁻¹
            - 5 * dutBeta * lam)
        (Set.Icc 0 1) 1 := by
    exact
      (continuousWithinAt_const.sub hcinv).sub
        (continuousWithinAt_const.mul continuousWithinAt_id)
  unfold dutRate dutNumer
  exact hnum.div_const dutDen

/-- Lambda -> 1^- DUT headline theorem, conditional only on the uniform
external six-point verifier contract. -/
theorem dut_thmD₀_simple
    (hcert :
      ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
        DUTSharpVerifierCertificate
          (paramsOf stdProfile lam)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (dutHeadlineRate - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  unfold dutHeadlineRate
  refine
    ThmD.eps_form_of_approx
      (g := fun lam : ℝ =>
        dutRate (ThmD.cStar lam) lam)
      (ThmD.approx_of_continuousWithinAt
        dutRate_cStar_continuousWithinAt_one)
      (fun _ => Nat.cast_nonneg _)
      ?_
  intro lam hlam hlt
  have h0 : 0 < lam := by
    linarith
  exact
    dut_thmD_simple_lam h0 hlt
      (hcert lam hlam hlt)

end Zeta23.ZeroSide.RankTraceMult
