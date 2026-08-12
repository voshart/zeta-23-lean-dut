/-
DUTCharge3.lean

c = 3 defect and six-column charge specialization for the DUT refinement.
Intended location: Zeta23/ZeroSide/DUTCharge3.lean
-/

import Zeta23.ZeroSide.DUTBlockRotation

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

/-- Defect of the exact c=3 spectral charge relative to the affine
`4*p + 1` bookkeeping.  On `[0,3]` this is `(p-1)^2`; above `3` it is
`4*p-8`. -/
def dutDefect3 (p : ℝ) : ℝ := 5 - kc 3 p - 4 * (1 - p)

lemma dutDefect3_of_le {p : ℝ} (h : p ≤ 3) :
    dutDefect3 p = (p - 1) ^ 2 := by
  rw [dutDefect3, kc_of_le h]
  ring

lemma dutDefect3_of_ge {p : ℝ} (h : 3 ≤ p) :
    dutDefect3 p = 4 * p - 8 := by
  rw [dutDefect3, kc_of_ge h]
  ring

lemma dutDefect3_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ dutDefect3 p := by
  rcases le_total p 3 with h | h
  · rw [dutDefect3_of_le h]
    exact sq_nonneg _
  · rw [dutDefect3_of_ge h]
    linarith

/-- Exact pointwise c=3 charge identity. -/
lemma kc_three_eq_affine_sub_defect (p : ℝ) :
    kc 3 p = 4 * p + 1 - dutDefect3 p := by
  unfold dutDefect3
  ring

/-- Exact summed c=3 charge identity over any finite index type. -/
lemma sum_kc_three_eq_affine_sub_defect {ι : Type*} [Fintype ι]
    (p : ι → ℝ) :
    (∑ i, kc 3 (p i))
      = 4 * (∑ i, p i) + (Fintype.card ι : ℝ)
        - ∑ i, dutDefect3 (p i) := by
  simp_rw [kc_three_eq_affine_sub_defect]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- If the total squared mass is at most the number of original simple slots,
the exact c=3 charge is at most `5*slots - defect`. -/
lemma sum_kc_three_le_card_sub_defect {ι : Type*} [Fintype ι]
    (p : ι → ℝ)
    (htr : (∑ i, p i) ≤ (Fintype.card ι : ℝ)) :
    (∑ i, kc 3 (p i))
      ≤ 5 * (Fintype.card ι : ℝ) - ∑ i, dutDefect3 (p i) := by
  rw [sum_kc_three_eq_affine_sub_defect]
  linarith

/-- Six-slot c=3 specialization. -/
lemma sum_kc_three_fin6_le (p : Fin 6 → ℝ)
    (htr : (∑ i, p i) ≤ 6) :
    (∑ i, kc 3 (p i)) ≤ 30 - ∑ i, dutDefect3 (p i) := by
  have h := sum_kc_three_le_card_sub_defect p (by simpa using htr)
  norm_num at h ⊢
  exact h

/-- Generic c=3 DUT transport interface. -/
theorem rank_trace_mult_k_transport_three_with_saving
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
    (hcharge : (∑ j, kc 3 (m' j * xsq v' j)) ≤ base - Delta) :
    6 * rtrace (Pmat m v + Q) - frobSq (Pmat m v + Q)
      ≤ base - Delta + 9 * b := by
  have h := rank_trace_mult_k_transport hm v hm' v' hP hQ hb
    (c := 3) (by norm_num)
  norm_num at h
  linarith

/-- Six-column c=3 analogue of `fin6_rotated_charge_and_P`. -/
theorem fin6_rotated_charge3_and_P
    {𝕜 : Type*} [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n]
    (v : Fin 6 → n → 𝕜)
    (htrace : (∑ j, xsq v j) ≤ 6) :
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤
      30 - ∑ j, dutDefect3 (xsq vr j) := by
  dsimp only
  constructor
  · exact Pmat_one_gramEigenRotate_eq v
  · apply sum_kc_three_fin6_le
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    have hM : (Wᴴ * W).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self W
    calc
      (∑ j, xsq (columns (gramEigenRotateMatrix W)) j)
          = ∑ j, hM.1.eigenvalues j := by
              apply Finset.sum_congr rfl
              intro j _
              exact xsq_columns_gramEigenRotateMatrix W j
      _ = rtrace (Wᴴ * W) := by
              rw [rtrace_eq_sum_eigenvalues hM.1]
      _ = rtrace (W * Wᴴ) := by
              unfold rtrace
              rw [trace_mul_comm]
      _ = ∑ j, xsq v j := by
              have hp := rtrace_Pmat
                (m := fun _ : Fin 6 => (1 : ℝ))
                (fun _ => by norm_num) v
              simpa [Pmat, W] using hp
      _ ≤ 6 := htrace

end Zeta23.ZeroSide.RankTraceMult
