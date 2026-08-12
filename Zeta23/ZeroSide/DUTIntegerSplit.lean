/-
DUTIntegerSplit.lean

Generic decomposition of an absolutely/summably controlled integer series into

  negative indices  +  finite block [0,d)  +  right tail [d,∞).

This is the bookkeeping lemma needed to turn the full Poisson HasSum into
the actual finite Gabor sum plus the two omitted tails already bounded in
DUTTailProduct.

Intended location:
  Zeta23/ZeroSide/DUTIntegerSplit.lean
-/

import Zeta23.ZeroSide.DUTTailProduct
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Classical

/-- Generic right-tail index beginning at the natural cutoff `d`. -/
def dutRightIndexFrom (d n : ℕ) : ℤ :=
  (d : ℤ) + (n : ℤ)

/-- Finite-middle index `Fin d -> ℤ`. -/
def dutMiddleIndex {d : ℕ} (k : Fin d) : ℤ :=
  ((k : ℕ) : ℤ)

lemma dutLeftTailIndex_injective :
    Function.Injective dutLeftTailIndex := by
  intro a b h
  have h' : (((a + 1 : ℕ) : ℤ)) = (((b + 1 : ℕ) : ℤ)) := by
    exact neg_injective h
  have hn : a + 1 = b + 1 := by
    exact_mod_cast h'
  omega

lemma dutRightIndexFrom_injective (d : ℕ) :
    Function.Injective (dutRightIndexFrom d) := by
  intro a b h
  unfold dutRightIndexFrom at h
  have h' : (a : ℤ) = (b : ℤ) := by
    omega
  exact_mod_cast h'

lemma dutMiddleIndex_injective (d : ℕ) :
    Function.Injective (@dutMiddleIndex d) := by
  intro a b h
  have h' : (((a : ℕ) : ℤ)) = (((b : ℕ) : ℤ)) := by
    simpa [dutMiddleIndex] using h
  have hab : (a : ℕ) = (b : ℕ) := by
    exact_mod_cast h'
  exact Fin.ext hab

/-- Negative integers are exactly the range of `n ↦ -(n+1)`. -/
lemma range_dutLeftTailIndex :
    Set.range dutLeftTailIndex = {k : ℤ | k < 0} := by
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    change -(((n + 1 : ℕ) : ℤ)) < 0
    have hn : (0 : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast (Nat.zero_le n)
    omega
  · intro hk
    obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hk
    refine ⟨n, ?_⟩
    rw [hn]
    simp [dutLeftTailIndex, Int.negSucc_eq]

/-- Integers at least `d` are exactly the generic right-tail range. -/
lemma range_dutRightIndexFrom (d : ℕ) :
    Set.range (dutRightIndexFrom d) = {k : ℤ | (d : ℤ) ≤ k} := by
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    change (d : ℤ) ≤ (d : ℤ) + (n : ℤ)
    exact Int.le_add_of_nonneg_right (by positivity)
  · intro hk
    obtain ⟨n, hn⟩ := Int.le.dest hk
    refine ⟨n, ?_⟩
    unfold dutRightIndexFrom
    exact hn

/-- Integers in `[0,d)` are exactly the range of `Fin d`. -/
lemma range_dutMiddleIndex (d : ℕ) :
    Set.range (@dutMiddleIndex d) =
      {k : ℤ | 0 ≤ k ∧ k < (d : ℤ)} := by
  ext k
  constructor
  · rintro ⟨a, rfl⟩
    simp [dutMiddleIndex]
  · rintro ⟨hk0, hkd⟩
    have hnat : k.toNat < d := by
      rw [Int.toNat_lt hk0]
      exact hkd
    refine ⟨⟨k.toNat, hnat⟩, ?_⟩
    unfold dutMiddleIndex
    simpa using (Int.toNat_of_nonneg hk0).symm

/-- The three ranges are pairwise disjoint in the order used for summation. -/
lemma dut_integer_ranges_disjoint_left_middle (d : ℕ) :
    Disjoint (Set.range dutLeftTailIndex)
      (Set.range (@dutMiddleIndex d)) := by
  rw [range_dutLeftTailIndex, range_dutMiddleIndex]
  exact Set.disjoint_left.2 (by
    intro k hkL hkM
    simp only [Set.mem_setOf_eq] at hkL hkM
    omega)

lemma dut_integer_ranges_disjoint_leftMiddle_right (d : ℕ) :
    Disjoint
      (Set.range dutLeftTailIndex ∪ Set.range (@dutMiddleIndex d))
      (Set.range (dutRightIndexFrom d)) := by
  rw [range_dutLeftTailIndex, range_dutMiddleIndex, range_dutRightIndexFrom]
  exact Set.disjoint_left.2 (by
    intro k hkLM hkR
    simp only [Set.mem_union, Set.mem_setOf_eq] at hkLM hkR
    rcases hkLM with hkL | hkM <;> omega)

/-- The negative/middle/right ranges cover every integer. -/
lemma dut_integer_ranges_cover (d : ℕ) :
    Set.range dutLeftTailIndex ∪
      (Set.range (@dutMiddleIndex d) ∪ Set.range (dutRightIndexFrom d))
      = Set.univ := by
  rw [range_dutLeftTailIndex, range_dutMiddleIndex, range_dutRightIndexFrom]
  ext k
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega

/-- **Generic integer-series split.**

Given summability of the two tails and a known full integer `HasSum`, the full
sum is exactly the negative tail plus the finite block `[0,d)` plus the right
tail. -/
theorem dut_hasSum_integer_split
    {f : ℤ → ℝ} {a : ℝ} (d : ℕ)
    (hfull : HasSum f a)
    (hleft : Summable (fun n : ℕ => f (dutLeftTailIndex n)))
    (hright : Summable (fun n : ℕ => f (dutRightIndexFrom d n))) :
    a =
      (∑' n : ℕ, f (dutLeftTailIndex n))
        + (∑ k : Fin d, f (dutMiddleIndex k))
        + (∑' n : ℕ, f (dutRightIndexFrom d n)) := by
  let L : Set ℤ := Set.range dutLeftTailIndex
  let M : Set ℤ := Set.range (@dutMiddleIndex d)
  let R : Set ℤ := Set.range (dutRightIndexFrom d)

  have hLs :
      HasSum (fun k : L => f k)
        (∑' n : ℕ, f (dutLeftTailIndex n)) := by
    exact
      (dutLeftTailIndex_injective.hasSum_range_iff).2
        hleft.hasSum

  have hMs :
      HasSum (fun k : M => f k)
        (∑ k : Fin d, f (dutMiddleIndex k)) := by
    have hm0 :
        HasSum (fun k : Fin d => f (dutMiddleIndex k))
          (∑ k : Fin d, f (dutMiddleIndex k)) :=
      hasSum_fintype _
    exact
      (dutMiddleIndex_injective d).hasSum_range_iff.mpr hm0

  have hRs :
      HasSum (fun k : R => f k)
        (∑' n : ℕ, f (dutRightIndexFrom d n)) := by
    exact
      ((dutRightIndexFrom_injective d).hasSum_range_iff).2
        hright.hasSum

  have hLM :
      HasSum
        (fun k : (L ∪ M : Set ℤ) => f k)
        ((∑' n : ℕ, f (dutLeftTailIndex n))
          + (∑ k : Fin d, f (dutMiddleIndex k))) := by
    exact hLs.add_disjoint
      (by
        dsimp [L, M]
        exact dut_integer_ranges_disjoint_left_middle d)
      hMs

  have hLMR :
      HasSum
        (fun k : ((L ∪ M) ∪ R : Set ℤ) => f k)
        (((∑' n : ℕ, f (dutLeftTailIndex n))
          + (∑ k : Fin d, f (dutMiddleIndex k)))
          + (∑' n : ℕ, f (dutRightIndexFrom d n))) := by
    exact hLM.add_disjoint
      (by
        dsimp [L, M, R]
        exact dut_integer_ranges_disjoint_leftMiddle_right d)
      hRs

  have hcover : (L ∪ M) ∪ R = Set.univ := by
    dsimp [L, M, R]
    rw [Set.union_assoc]
    exact dut_integer_ranges_cover d

  rw [hcover] at hLMR

  have hfull_univ :
      HasSum
        (fun k : (Set.univ : Set ℤ) => f k)
        a := by
    exact
      (hasSum_subtype_iff_of_support_subset
        (s := (Set.univ : Set ℤ))
        (by simp)).2 hfull

  have hu := hfull_univ.unique hLMR
  simpa [add_assoc] using hu

end Zeta23.ZeroSide.RankTraceMult
