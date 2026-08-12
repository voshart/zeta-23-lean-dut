/-
DUTRankTrace_v2.lean

Small formal core for the Defect-Utilizing Tightening (DUT) refinement,
written against the public Anthropic zeta-23-lean API as inspected 2026-08-11.

This file deliberately proves only the algebraic/rank-trace interface.  It does
not yet formalize the six-zero spectral rotation, phase partition, or analytic
Gabor-to-kernel transfer.
-/

import Zeta23.ZeroSide.RankTraceMult

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

/-! ## 1. The c = 2 defect -/

/-- Defect of the exact c=2 spectral charge relative to the affine
`2*p + 1` bookkeeping.  On `[0,2]` this is `(p-1)^2`; above `2` it is
`2*p-3`. -/
def dutDefect2 (p : ℝ) : ℝ := 3 - kc 2 p - 2 * (1 - p)

lemma dutDefect2_of_le {p : ℝ} (h : p ≤ 2) :
    dutDefect2 p = (p - 1) ^ 2 := by
  rw [dutDefect2, kc_of_le h]
  ring

lemma dutDefect2_of_ge {p : ℝ} (h : 2 ≤ p) :
    dutDefect2 p = 2 * p - 3 := by
  rw [dutDefect2, kc_of_ge h]
  ring

lemma dutDefect2_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ dutDefect2 p := by
  rcases le_total p 2 with h | h
  · rw [dutDefect2_of_le h]
    exact sq_nonneg _
  · rw [dutDefect2_of_ge h]
    linarith

/-- Exact pointwise charge identity. -/
lemma kc_two_eq_affine_sub_defect (p : ℝ) :
    kc 2 p = 2 * p + 1 - dutDefect2 p := by
  unfold dutDefect2
  ring

/-- Exact summed charge identity over any finite index type. -/
lemma sum_kc_two_eq_affine_sub_defect {ι : Type*} [Fintype ι]
    (p : ι → ℝ) :
    (∑ i, kc 2 (p i))
      = 2 * (∑ i, p i) + (Fintype.card ι : ℝ)
        - ∑ i, dutDefect2 (p i) := by
  simp_rw [kc_two_eq_affine_sub_defect]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- If the total squared mass is at most the number of original simple
rank-one slots, the exact charge is at most `3*slots - defect`. -/
lemma sum_kc_two_le_card_sub_defect {ι : Type*} [Fintype ι]
    (p : ι → ℝ)
    (htr : (∑ i, p i) ≤ (Fintype.card ι : ℝ)) :
    (∑ i, kc 2 (p i))
      ≤ 3 * (Fintype.card ι : ℝ) - ∑ i, dutDefect2 (p i) := by
  rw [sum_kc_two_eq_affine_sub_defect]
  linarith

/-- Six-slot specialization used by a DUT block. -/
lemma sum_kc_two_fin6_le (p : Fin 6 → ℝ)
    (htr : (∑ i, p i) ≤ 6) :
    (∑ i, kc 2 (p i)) ≤ 18 - ∑ i, dutDefect2 (p i) := by
  have h := sum_kc_two_le_card_sub_defect p (by simpa using htr)
  norm_num at h ⊢
  exact h

/-! ## 2. Transport Anthropic's exact k-charge lemma across an equal Pmat -/

/-- `rank_trace_mult_k` may be applied to any nonnegative rank-one
decomposition of the same positive matrix `Pmat`.  This is the formal seam
needed by DUT: blockwise unitary mixing changes the atom norms/charges but not
the positive matrix itself. -/
theorem rank_trace_mult_k_transport
    {𝕜 : Type*} [RCLike 𝕜]
    {n ι κ : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (v : ι → n → 𝕜)
    {m' : κ → ℝ} (hm' : ∀ j, 0 ≤ m' j) (v' : κ → n → 𝕜)
    (hP : Pmat m v = Pmat m' v')
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (Pmat m v + Q) - frobSq (Pmat m v + Q)
      ≤ (∑ j, kc c (m' j * xsq v' j)) + c ^ 2 * b := by
  have h := rank_trace_mult_k hm' v' hQ hb hc
  rw [← hP] at h
  exact h

/-- Generic c=2 DUT interface: any alternative decomposition with exact charge
`≤ base - Delta` yields the same saving `Delta` with coefficient one in the
rank-trace inequality. -/
theorem rank_trace_mult_k_transport_two_with_saving
    {𝕜 : Type*} [RCLike 𝕜]
    {n ι κ : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (v : ι → n → 𝕜)
    {m' : κ → ℝ} (hm' : ∀ j, 0 ≤ m' j) (v' : κ → n → 𝕜)
    (hP : Pmat m v = Pmat m' v')
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b)
    {base Delta : ℝ}
    (hcharge : (∑ j, kc 2 (m' j * xsq v' j)) ≤ base - Delta) :
    4 * rtrace (Pmat m v + Q) - frobSq (Pmat m v + Q)
      ≤ base - Delta + 4 * b := by
  have h := rank_trace_mult_k_transport hm v hm' v' hP hQ hb
    (c := 2) (by norm_num)
  norm_num at h
  linarith

/-! ## 3. Counting coefficient of Delta -/

/-- The three-line bookkeeping behind the coefficient-one saving.
If `C ≤ 3*s1 + 4*s2 + 4*p - Delta` and the total zero count satisfies
`s1 + 2*s2 + 2*p ≤ N`, then `s1 ≥ C - 2*N + Delta`. -/
lemma dut_counting_with_saving
    {C s1 s2 p N Delta : ℝ}
    (hC : C ≤ 3 * s1 + 4 * s2 + 4 * p - Delta)
    (hN : s1 + 2 * s2 + 2 * p ≤ N) :
    C - 2 * N + Delta ≤ s1 := by
  linarith

end Zeta23.ZeroSide.RankTraceMult
