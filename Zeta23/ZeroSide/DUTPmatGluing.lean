/-
DUTPmatGluing.lean

Generic finite-dimensional gluing lemmas for DUT.

The remaining global zero-side step replaces several pairwise-disjoint
six-tuples of simple-zero atoms by their Gram-eigenbasis rotations, while
leaving all other on-line atoms untouched.

This file isolates the generic algebra needed for that construction:

  * Pmat over a sum type is the sum of the two Pmats;
  * Pmat over a sigma type is the sum of the fiber Pmats;
  * charge sums over the same index constructions split identically.

Thus a family of disjoint local Pmat-preserving rotations may be glued by
summing their local equalities.

Intended location:
  Zeta23/ZeroSide/DUTPmatGluing.lean
-/

import Zeta23.ZeroSide.DUTCoreBoundaryAsymptotic

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Pmat` is additive across a disjoint sum of two atom index types. -/
lemma Pmat_sumElim
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (m₁ : ι → ℝ) (hm₁ : ∀ i, 0 ≤ m₁ i)
    (v₁ : ι → n → 𝕜)
    (m₂ : κ → ℝ) (hm₂ : ∀ j, 0 ≤ m₂ j)
    (v₂ : κ → n → 𝕜) :
    Pmat (Sum.elim m₁ m₂) (Sum.elim v₁ v₂)
      =
    Pmat m₁ v₁ + Pmat m₂ v₂ := by
  have hm :
      ∀ x : ι ⊕ κ, 0 ≤ Sum.elim m₁ m₂ x := by
    intro x
    cases x with
    | inl i => exact hm₁ i
    | inr j => exact hm₂ j
  ext a b
  simp only [Matrix.add_apply]
  rw [
    Pmat_apply hm (Sum.elim v₁ v₂) a b,
    Pmat_apply hm₁ v₁ a b,
    Pmat_apply hm₂ v₂ a b,
    Fintype.sum_sum_type
  ]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- The `kc` charge sum splits over a disjoint sum index type. -/
lemma sum_kc_sumElim
    {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (c : ℝ)
    (m₁ : ι → ℝ) (v₁ : ι → n → 𝕜)
    (m₂ : κ → ℝ) (v₂ : κ → n → 𝕜) :
    (∑ x : ι ⊕ κ,
      kc c
        (Sum.elim m₁ m₂ x *
          xsq (Sum.elim v₁ v₂) x))
      =
    (∑ i : ι, kc c (m₁ i * xsq v₁ i))
      +
    (∑ j : κ, kc c (m₂ j * xsq v₂ j)) := by
  rw [Fintype.sum_sum_type]
  simp only [xsq, Sum.elim_inl, Sum.elim_inr]

/-- `Pmat` over a sigma-indexed family is the sum of the fiber Pmats. -/
lemma Pmat_sigma
    {β : Type*} [Fintype β] [DecidableEq β]
    {ι : β → Type*}
    [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (m : ∀ b, ι b → ℝ)
    (hm : ∀ b i, 0 ≤ m b i)
    (v : ∀ b, ι b → n → 𝕜) :
    Pmat
        (fun x : Sigma ι => m x.1 x.2)
        (fun x : Sigma ι => v x.1 x.2)
      =
    ∑ b : β, Pmat (m b) (v b) := by
  have hmσ :
      ∀ x : Sigma ι, 0 ≤ m x.1 x.2 := by
    intro x
    exact hm x.1 x.2
  ext a d
  simp only [Matrix.sum_apply]
  rw [Pmat_apply hmσ (fun x : Sigma ι => v x.1 x.2) a d]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Pmat_apply (hm b) (v b) a d]

/-- The `kc` charge sum over a sigma family is the sum of fiber charge sums. -/
lemma sum_kc_sigma
    {β : Type*} [Fintype β]
    {ι : β → Type*} [∀ b, Fintype (ι b)]
    (c : ℝ)
    (m : ∀ b, ι b → ℝ)
    (v : ∀ b, ι b → n → 𝕜) :
    (∑ x : Sigma ι,
      kc c (m x.1 x.2 * xsq (fun y : Sigma ι => v y.1 y.2) x))
      =
    ∑ b : β, ∑ i : ι b, kc c (m b i * xsq (v b) i) := by
  rw [Fintype.sum_sigma]
  simp only [xsq]

/-- All-one specialization used for a family of rotated six-blocks. -/
lemma Pmat_sigma_one
    {β : Type*} [Fintype β] [DecidableEq β]
    {ι : β → Type*}
    [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (v : ∀ b, ι b → n → 𝕜) :
    Pmat
        (fun _ : Sigma ι => (1 : ℝ))
        (fun x : Sigma ι => v x.1 x.2)
      =
    ∑ b : β, Pmat (fun _ : ι b => (1 : ℝ)) (v b) := by
  simpa using
    (Pmat_sigma
      (m := fun b (_ : ι b) => (1 : ℝ))
      (hm := fun _ _ => by norm_num)
      v)

/-- If every fiber rotation preserves its local all-one `Pmat`, then the
sigma-glued family preserves the sum of all local block Pmats. -/
lemma Pmat_sigma_one_congr
    {β : Type*} [Fintype β] [DecidableEq β]
    {ι : β → Type*}
    [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (v v' : ∀ b, ι b → n → 𝕜)
    (hlocal :
      ∀ b,
        Pmat (fun _ : ι b => (1 : ℝ)) (v' b)
          =
        Pmat (fun _ : ι b => (1 : ℝ)) (v b)) :
    Pmat
        (fun _ : Sigma ι => (1 : ℝ))
        (fun x : Sigma ι => v' x.1 x.2)
      =
    Pmat
        (fun _ : Sigma ι => (1 : ℝ))
        (fun x : Sigma ι => v x.1 x.2) := by
  rw [Pmat_sigma_one v', Pmat_sigma_one v]
  apply Finset.sum_congr rfl
  intro b hb
  exact hlocal b

/-- Fiberwise charge savings add exactly under sigma gluing. -/
lemma sum_kc_sigma_le_of_fiber
    {β : Type*} [Fintype β]
    {ι : β → Type*} [∀ b, Fintype (ι b)]
    (c : ℝ)
    (v : ∀ b, ι b → n → 𝕜)
    (base saving : β → ℝ)
    (h :
      ∀ b,
        (∑ i : ι b, kc c (xsq (v b) i))
          ≤ base b - saving b) :
    (∑ x : Sigma ι,
      kc c
        (xsq (fun y : Sigma ι => v y.1 y.2) x))
      ≤
    (∑ b : β, base b) - ∑ b : β, saving b := by
  have hsplit :
      (∑ x : Sigma ι,
        kc c
          (xsq (fun y : Sigma ι => v y.1 y.2) x))
        =
      ∑ b : β, ∑ i : ι b, kc c (xsq (v b) i) := by
    rw [Fintype.sum_sigma]
    simp only [xsq]
  rw [hsplit]
  have hs :
      (∑ b : β, ∑ i : ι b, kc c (xsq (v b) i))
        ≤
      ∑ b : β, (base b - saving b) :=
    Finset.sum_le_sum fun b _ => h b
  rw [Finset.sum_sub_distrib] at hs
  exact hs

end Zeta23.ZeroSide.RankTraceMult
