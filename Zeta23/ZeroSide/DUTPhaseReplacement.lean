/-
DUTPhaseReplacement.lean

Actual finite-dimensional phase replacement for DUT.

Fix one residue class r mod 6.  The valid consecutive six-window starts in
that phase are the filtered finite set

  { i < s-5 | r = i % 6 },   s = dutCoreCount Z T.

Their six slots form a sigma type.  The corresponding core simple zeros are
pairwise distinct, hence embed into the upstream on-line atom type.  Splitting
the full on-line type into

  selected six-block atoms  ⊕  untouched atoms

allows all local Gram-eigenbasis rotations in the phase to be performed
simultaneously.

Main theorem `dutPhaseReplacement`:
  * the alternative global decomposition has exactly the original `blockP`;
  * its c=2 charge is at most the original integer charge minus the phase
    certificate saving;
  * likewise for c=3.

This is the finite-dimensional splice required before applying
`rank_trace_mult_k` globally.

Intended location:
  Zeta23/ZeroSide/DUTPhaseReplacement.lean
-/

import Zeta23.ZeroSide.DUTPmatGluing
import Mathlib.Logic.Equiv.Sum

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-! ## Reindexing Pmat and charge sums by a finite equivalence -/

lemma Pmat_equiv_reindex
    {𝕜 : Type*} [RCLike 𝕜]
    {n ι κ : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ)
    (m : κ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (v : κ → n → 𝕜) :
    Pmat (fun i => m (e i)) (fun i => v (e i))
      = Pmat m v := by
  ext a b
  rw [
    Pmat_apply (fun i => hm (e i)) (fun i => v (e i)) a b,
    Pmat_apply hm v a b
  ]
  simpa using
    (Equiv.sum_comp e
      (fun j : κ =>
        (m j : 𝕜) * (v j a * starRingEnd 𝕜 (v j b))))

lemma sum_kc_equiv_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (c : ℝ) (f : κ → ℝ) :
    (∑ i : ι, kc c (f (e i)))
      = ∑ j : κ, kc c (f j) := by
  simpa using Equiv.sum_comp e (fun j : κ => kc c (f j))

/-! ## Exact phase start/slot indexing -/

/-- Valid six-window starts in phase `r`. -/
def dutPhaseStarts (s r : ℕ) : Finset ℕ :=
  (Finset.range (s - 5)).filter (fun i => r = i % 6)

/-- Finite type of valid starts in one phase. -/
abbrev DUTPhaseStart (s r : ℕ) := ↥(dutPhaseStarts s r)

/-- One selected atom is a valid phase start together with one of its six
slots. -/
abbrev DUTPhaseAtom (s r : ℕ) :=
  Sigma (fun _ : DUTPhaseStart s r => Fin 6)

lemma dutPhaseStart_mem_range
    {s r : ℕ} (i : DUTPhaseStart s r) :
    (i : ℕ) ∈ Finset.range (s - 5) :=
  (Finset.mem_filter.mp i.2).1

lemma dutPhaseStart_mod
    {s r : ℕ} (i : DUTPhaseStart s r) :
    r = (i : ℕ) % 6 :=
  (Finset.mem_filter.mp i.2).2

lemma dutPhaseStart_hi
    {s r : ℕ} (i : DUTPhaseStart s r) :
    (i : ℕ) + 5 < s := by
  have hi := Finset.mem_range.mp (dutPhaseStart_mem_range i)
  omega

/-- Core index occupied by a selected phase atom. -/
def dutPhaseCoreIndex
    {s r : ℕ} (x : DUTPhaseAtom s r) : Fin s :=
  ⟨(x.1 : ℕ) + (x.2 : ℕ), by
    have hi := dutPhaseStart_hi x.1
    have hj : (x.2 : ℕ) ≤ 5 := by omega
    omega⟩

/-- Different block/slot pairs in one phase select different core zeros. -/
lemma dutPhaseCoreIndex_injective
    {s r : ℕ} :
    Function.Injective
      (dutPhaseCoreIndex : DUTPhaseAtom s r → Fin s) := by
  intro x y hxy
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  have hv : (i : ℕ) + (j : ℕ) = (i' : ℕ) + (j' : ℕ) := by
    simpa [dutPhaseCoreIndex] using congrArg Fin.val hxy
  have hmod : (i : ℕ) % 6 = (i' : ℕ) % 6 := by
    rw [← dutPhaseStart_mod i, ← dutPhaseStart_mod i']
  have hj : (j : ℕ) < 6 := j.isLt
  have hj' : (j' : ℕ) < 6 := j'.isLt
  have hdivi := Nat.mod_add_div (i : ℕ) 6
  have hdivi' := Nat.mod_add_div (i' : ℕ) 6
  have hiEq : (i : ℕ) = (i' : ℕ) := by
    omega
  have hjEq : (j : ℕ) = (j' : ℕ) := by
    omega
  have hiFin : i = i' := Subtype.ext hiEq
  subst i'
  have hjFin : j = j' := Fin.ext hjEq
  subst j'
  rfl

/-- The sigma sum of one value per phase start is exactly the existing phase
contribution. -/
lemma dutPhaseContribution_eq_sum_starts
    (delta : ℕ → ℝ) (s r : ℕ) :
    dutPhaseContribution delta s r
      = ∑ i : DUTPhaseStart s r, delta (i : ℕ) := by
  classical
  calc
    dutPhaseContribution delta s r
        = ∑ i ∈ dutPhaseStarts s r, delta i := by
            unfold dutPhaseContribution dutPhaseStarts
            rw [Finset.sum_filter]
    _ = ∑ i : DUTPhaseStart s r, delta (i : ℕ) := by
          symm
          exact Finset.sum_coe_sort (dutPhaseStarts s r) delta

/-! ## Embedding selected core atoms into the upstream on-line family -/

lemma dutCoreOrderedZI_injective
    (Z : ZeroConfig) (T : ℝ) :
    Function.Injective (dutCoreOrderedZI Z T) := by
  intro a b hab
  have hz :
      dutCoreOrderedZero Z T a = dutCoreOrderedZero Z T b := by
    simpa only [coe_dutCoreOrderedZI] using
      congrArg (fun z : ZI Z T => (z : ℂ)) hab
  have hcore :
      (dutCoreOrderIso Z T) a = (dutCoreOrderIso Z T) b := by
    apply Subtype.ext
    exact hz
  exact (dutCoreOrderIso Z T).injective hcore

abbrev DUTPhaseDOnLine
    (Z : ZeroConfig) (T : ℝ) (P : Params) :=
  (blockData Z T (P.atD T) (dutD_phiHatConj P T)).onLine

/-- The actual upstream on-line atom selected by a phase block/slot. -/
noncomputable def dutPhaseSelectedOnLine
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (x : DUTPhaseAtom (dutCoreCount Z T) r) :
    DUTPhaseDOnLine Z T P :=
  dutCoreSixOnLineD Z T P
    (x.1 : ℕ) (dutPhaseStart_hi x.1) x.2

lemma dutPhaseSelectedOnLine_injective
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    Function.Injective (dutPhaseSelectedOnLine Z T P r) := by
  intro x y hxy
  have hz :
      dutCoreSixZI Z T
          (x.1 : ℕ) (dutPhaseStart_hi x.1) x.2
        =
      dutCoreSixZI Z T
          (y.1 : ℕ) (dutPhaseStart_hi y.1) y.2 :=
    congrArg Subtype.val hxy
  have hordered :
      dutCoreOrderedZI Z T (dutPhaseCoreIndex x)
        =
      dutCoreOrderedZI Z T (dutPhaseCoreIndex y) := by
    simpa [
      dutCoreSixZI, dutCoreSixIndex, dutPhaseCoreIndex
    ] using hz
  have hidx :=
    dutCoreOrderedZI_injective Z T hordered
  exact dutPhaseCoreIndex_injective hidx

/-- Selected on-line atoms as a set. -/
def dutPhaseSelectedSet
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    Set (DUTPhaseDOnLine Z T P) :=
  Set.range (dutPhaseSelectedOnLine Z T P r)

/-- Untouched on-line atoms in the chosen phase. -/
abbrev DUTPhaseRest
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :=
  {z : DUTPhaseDOnLine Z T P //
    z ∉ dutPhaseSelectedSet Z T P r}

/-- Selected sigma atoms are equivalent to their range in the on-line family. -/
noncomputable def dutPhaseSelectedEquiv
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    DUTPhaseAtom (dutCoreCount Z T) r
      ≃
    {z : DUTPhaseDOnLine Z T P //
      z ∈ dutPhaseSelectedSet Z T P r} :=
  Equiv.ofInjective
    (dutPhaseSelectedOnLine Z T P r)
    (dutPhaseSelectedOnLine_injective Z T P r)

/-- Split all on-line atoms into selected phase atoms plus untouched atoms. -/
noncomputable def dutPhaseSplitEquiv
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    DUTPhaseAtom (dutCoreCount Z T) r
        ⊕ DUTPhaseRest Z T P r
      ≃
    DUTPhaseDOnLine Z T P := by
  classical
  exact
    ((dutPhaseSelectedEquiv Z T P r).sumCongr
      (Equiv.refl (DUTPhaseRest Z T P r))).trans
      (Equiv.sumCompl
        (fun z : DUTPhaseDOnLine Z T P =>
          z ∈ dutPhaseSelectedSet Z T P r))

@[simp] lemma dutPhaseSplitEquiv_inl
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (x : DUTPhaseAtom (dutCoreCount Z T) r) :
    dutPhaseSplitEquiv Z T P r (Sum.inl x)
      = dutPhaseSelectedOnLine Z T P r x := by
  classical
  change
    Equiv.sumCompl
        (fun z : DUTPhaseDOnLine Z T P =>
          z ∈ dutPhaseSelectedSet Z T P r)
        (Sum.inl (dutPhaseSelectedEquiv Z T P r x))
      =
    dutPhaseSelectedOnLine Z T P r x
  rw [Equiv.sumCompl_apply_inl]
  rfl

@[simp] lemma dutPhaseSplitEquiv_inr
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (z : DUTPhaseRest Z T P r) :
    dutPhaseSplitEquiv Z T P r (Sum.inr z) = z.1 := by
  classical
  change
    Equiv.sumCompl
        (fun z : DUTPhaseDOnLine Z T P =>
          z ∈ dutPhaseSelectedSet Z T P r)
        (Sum.inr z)
      = z.1
  exact Equiv.sumCompl_apply_inr z

/-- Every selected phase atom is simple, so its on-line multiplicity is one. -/
lemma dutPhaseSelected_mhat_eq_one
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (x : DUTPhaseAtom (dutCoreCount Z T) r) :
    (blockData Z T (P.atD T) (dutD_phiHatConj P T)).mhat
        (dutPhaseSelectedOnLine Z T P r x)
      = 1 := by
  change
    (Z.mult
      (dutCoreOrderedZero Z T
        (dutCoreSixIndex (x.1 : ℕ)
          (dutPhaseStart_hi x.1) x.2)) : ℝ) = 1
  rw [dutCoreOrderedZero_mult]
  norm_num

/-! ## Original and rotated block vectors -/

noncomputable def dutPhaseOriginalBlockV
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (i : DUTPhaseStart (dutCoreCount Z T) r) :
    Fin 6 → Fin ((P.atD T).d T) → ℂ :=
  dutCoreSixVhatD Z T P
    (i : ℕ) (dutPhaseStart_hi i)

noncomputable def dutPhaseRotatedBlockV
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (i : DUTPhaseStart (dutCoreCount Z T) r) :
    Fin 6 → Fin ((P.atD T).d T) → ℂ :=
  let v := dutPhaseOriginalBlockV Z T P r i
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  columns (gramEigenRotateMatrix W)

lemma dutPhaseSelected_vhat_eq_original
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (x : DUTPhaseAtom (dutCoreCount Z T) r) :
    (blockData Z T (P.atD T) (dutD_phiHatConj P T)).vhat
        ((P.atD T).a T * (P.atD T).L T ^ 2)
        (dutPhaseSelectedOnLine Z T P r x)
      =
    dutPhaseOriginalBlockV Z T P r x.1 x.2 := by
  rfl

/-! ## Global alternative decomposition -/

noncomputable def dutPhaseBaseM
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    DUTPhaseAtom (dutCoreCount Z T) r
        ⊕ DUTPhaseRest Z T P r → ℝ :=
  Sum.elim
    (fun _ => (1 : ℝ))
    (fun z =>
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).mhat z.1)

noncomputable def dutPhaseBaseV
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    DUTPhaseAtom (dutCoreCount Z T) r
        ⊕ DUTPhaseRest Z T P r →
      Fin ((P.atD T).d T) → ℂ :=
  Sum.elim
    (fun x =>
      dutPhaseOriginalBlockV Z T P r x.1 x.2)
    (fun z =>
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).vhat
          ((P.atD T).a T * (P.atD T).L T ^ 2) z.1)

noncomputable def dutPhaseAltM
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    DUTPhaseAtom (dutCoreCount Z T) r
        ⊕ DUTPhaseRest Z T P r → ℝ :=
  dutPhaseBaseM Z T P r

noncomputable def dutPhaseAltV
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    DUTPhaseAtom (dutCoreCount Z T) r
        ⊕ DUTPhaseRest Z T P r →
      Fin ((P.atD T).d T) → ℂ :=
  Sum.elim
    (fun x =>
      dutPhaseRotatedBlockV Z T P r x.1 x.2)
    (fun z =>
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).vhat
          ((P.atD T).a T * (P.atD T).L T ^ 2) z.1)

lemma dutPhaseBaseM_eq_pullback
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    dutPhaseBaseM Z T P r
      =
    fun x =>
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).mhat
          (dutPhaseSplitEquiv Z T P r x) := by
  funext x
  cases x with
  | inl a =>
      change
        1 =
        (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat
            (dutPhaseSplitEquiv Z T P r (Sum.inl a))
      rw [
        dutPhaseSplitEquiv_inl,
        dutPhaseSelected_mhat_eq_one
      ]
  | inr z =>
      change
        (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1
          =
        (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat
            (dutPhaseSplitEquiv Z T P r (Sum.inr z))
      rw [dutPhaseSplitEquiv_inr]

lemma dutPhaseBaseV_eq_pullback
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    dutPhaseBaseV Z T P r
      =
    fun x =>
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).vhat
          ((P.atD T).a T * (P.atD T).L T ^ 2)
          (dutPhaseSplitEquiv Z T P r x) := by
  funext x
  cases x with
  | inl a =>
      change
        dutPhaseOriginalBlockV Z T P r a.1 a.2
          =
        (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).vhat
            ((P.atD T).a T * (P.atD T).L T ^ 2)
            (dutPhaseSplitEquiv Z T P r (Sum.inl a))
      rw [
        dutPhaseSplitEquiv_inl,
        dutPhaseSelected_vhat_eq_original
      ]
  | inr z =>
      change
        (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).vhat
            ((P.atD T).a T * (P.atD T).L T ^ 2) z.1
          =
        (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).vhat
            ((P.atD T).a T * (P.atD T).L T ^ 2)
            (dutPhaseSplitEquiv Z T P r (Sum.inr z))
      rw [dutPhaseSplitEquiv_inr]

/-- The unrotated split decomposition is exactly the upstream blockP. -/
theorem dutPhaseBasePmat_eq_blockP
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hc :
      0 < (P.atD T).a T * (P.atD T).L T ^ 2) :
    Pmat
        (dutPhaseBaseM Z T P r)
        (dutPhaseBaseV Z T P r)
      =
    (blockData Z T (P.atD T)
      (dutD_phiHatConj P T)).blockP
        ((P.atD T).a T * (P.atD T).L T ^ 2) := by
  let D :=
    blockData Z T (P.atD T) (dutD_phiHatConj P T)
  rw [D.blockP_eq_Pmat hc]
  rw [
    dutPhaseBaseM_eq_pullback,
    dutPhaseBaseV_eq_pullback
  ]
  exact
    Pmat_equiv_reindex
      (dutPhaseSplitEquiv Z T P r)
      D.mhat D.mhat_nonneg
      (D.vhat ((P.atD T).a T * (P.atD T).L T ^ 2))

/-- Simultaneous local Pmat preservation glues to global Pmat preservation. -/
theorem dutPhaseAltPmat_eq_blockP
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hc :
      0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hlocalP :
      ∀ i : DUTPhaseStart (dutCoreCount Z T) r,
        Pmat (fun _ : Fin 6 => (1 : ℝ))
            (dutPhaseRotatedBlockV Z T P r i)
          =
        Pmat (fun _ : Fin 6 => (1 : ℝ))
            (dutPhaseOriginalBlockV Z T P r i)) :
    Pmat
        (dutPhaseAltM Z T P r)
        (dutPhaseAltV Z T P r)
      =
    (blockData Z T (P.atD T)
      (dutD_phiHatConj P T)).blockP
        ((P.atD T).a T * (P.atD T).L T ^ 2) := by
  have hmrest :
      ∀ z : DUTPhaseRest Z T P r,
        0 ≤
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).mhat z.1 :=
    fun z =>
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).mhat_nonneg z.1

  have hleft :
      Pmat
          (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
          (fun x =>
            dutPhaseRotatedBlockV Z T P r x.1 x.2)
        =
      Pmat
          (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
          (fun x =>
            dutPhaseOriginalBlockV Z T P r x.1 x.2) := by
    exact
      Pmat_sigma_one_congr
        (v := fun i =>
          dutPhaseOriginalBlockV Z T P r i)
        (v' := fun i =>
          dutPhaseRotatedBlockV Z T P r i)
        hlocalP

  have haltSplit :
      Pmat
          (dutPhaseAltM Z T P r)
          (dutPhaseAltV Z T P r)
        =
      Pmat
          (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
          (fun x =>
            dutPhaseRotatedBlockV Z T P r x.1 x.2)
        +
      Pmat
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).mhat z.1)
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).vhat
                ((P.atD T).a T * (P.atD T).L T ^ 2) z.1) := by
    simpa [
      dutPhaseAltM, dutPhaseBaseM, dutPhaseAltV
    ] using
      (Pmat_sumElim
        (n := Fin ((P.atD T).d T))
        (𝕜 := ℂ)
        (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
        (fun _ => by norm_num)
        (fun x =>
          dutPhaseRotatedBlockV Z T P r x.1 x.2)
        (fun z : DUTPhaseRest Z T P r =>
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).mhat z.1)
        hmrest
        (fun z : DUTPhaseRest Z T P r =>
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2) z.1))

  have hbaseSplit :
      Pmat
          (dutPhaseBaseM Z T P r)
          (dutPhaseBaseV Z T P r)
        =
      Pmat
          (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
          (fun x =>
            dutPhaseOriginalBlockV Z T P r x.1 x.2)
        +
      Pmat
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).mhat z.1)
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).vhat
                ((P.atD T).a T * (P.atD T).L T ^ 2) z.1) := by
    simpa [
      dutPhaseBaseM, dutPhaseBaseV
    ] using
      (Pmat_sumElim
        (n := Fin ((P.atD T).d T))
        (𝕜 := ℂ)
        (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
        (fun _ => by norm_num)
        (fun x =>
          dutPhaseOriginalBlockV Z T P r x.1 x.2)
        (fun z : DUTPhaseRest Z T P r =>
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).mhat z.1)
        hmrest
        (fun z : DUTPhaseRest Z T P r =>
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2) z.1))

  calc
    Pmat
        (dutPhaseAltM Z T P r)
        (dutPhaseAltV Z T P r)
        =
      Pmat
          (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
          (fun x =>
            dutPhaseRotatedBlockV Z T P r x.1 x.2)
        +
      Pmat
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).mhat z.1)
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).vhat
                ((P.atD T).a T * (P.atD T).L T ^ 2) z.1) := haltSplit
    _ =
      Pmat
          (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
          (fun x =>
            dutPhaseOriginalBlockV Z T P r x.1 x.2)
        +
      Pmat
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).mhat z.1)
          (fun z : DUTPhaseRest Z T P r =>
            (blockData Z T (P.atD T)
              (dutD_phiHatConj P T)).vhat
                ((P.atD T).a T * (P.atD T).L T ^ 2) z.1) := by rw [hleft]
    _ =
      Pmat
        (dutPhaseBaseM Z T P r)
        (dutPhaseBaseV Z T P r) := hbaseSplit.symm
    _ =
      (blockData Z T (P.atD T)
        (dutD_phiHatConj P T)).blockP
          ((P.atD T).a T * (P.atD T).L T ^ 2) := by
        exact dutPhaseBasePmat_eq_blockP Z T P r hc

/-! ## Charge bookkeeping -/

private lemma dut_xsq_nonneg
    {𝕜 : Type*} [RCLike 𝕜]
    {n ι : Type*} [Fintype n]
    (v : ι → n → 𝕜) (i : ι) :
    0 ≤ xsq v i := by
  unfold xsq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- On untouched atoms, the direct k-charge is bounded by the integer
multiplicity charge when the normalized vector has squared norm at most one. -/
lemma dutPhaseRest_charge_le_integer
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    {c : ℝ} (hc : 0 ≤ c)
    (hxsq :
      ∀ z : DUTPhaseDOnLine Z T P,
        xsq
          ((blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2))
          z ≤ 1) :
    (∑ z : DUTPhaseRest Z T P r,
      kc c
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1
          *
        xsq
          ((blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2))
          z.1))
      ≤
    ∑ z : DUTPhaseRest Z T P r,
      kc c
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1) := by
  apply Finset.sum_le_sum
  intro z hz
  let D :=
    blockData Z T (P.atD T) (dutD_phiHatConj P T)
  have hm : 0 ≤ D.mhat z.1 := D.mhat_nonneg z.1
  have hx0 :
      0 ≤ xsq
        (D.vhat ((P.atD T).a T * (P.atD T).L T ^ 2))
        z.1 :=
    dut_xsq_nonneg
      (D.vhat ((P.atD T).a T * (P.atD T).L T ^ 2))
      z.1
  have hx1 := hxsq z.1
  apply kc_mono hc
  nlinarith

/-- Integer c=2 charge splits as 18 per selected six-block plus untouched
integer charge. -/
lemma dutPhase_integer_charge_split_two
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    (∑ z : DUTPhaseDOnLine Z T P,
      kc 2
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z))
      =
    (∑ _i : DUTPhaseStart (dutCoreCount Z T) r, (18 : ℝ))
      +
    ∑ z : DUTPhaseRest Z T P r,
      kc 2
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1) := by
  let D :=
    blockData Z T (P.atD T) (dutD_phiHatConj P T)
  have hre :=
    sum_kc_equiv_reindex
      (dutPhaseSplitEquiv Z T P r)
      2 (fun z : DUTPhaseDOnLine Z T P => D.mhat z)
  rw [Fintype.sum_sum_type] at hre
  have hsel :
      (∑ x : DUTPhaseAtom (dutCoreCount Z T) r,
        kc 2
          (D.mhat
            (dutPhaseSplitEquiv Z T P r (Sum.inl x))))
        =
      ∑ _i : DUTPhaseStart (dutCoreCount Z T) r, (18 : ℝ) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dutPhaseSplitEquiv_inl]
    have hone :
        ∀ j : Fin 6,
          D.mhat
            (dutPhaseSelectedOnLine Z T P r
              ⟨i, j⟩) = 1 :=
      fun j => dutPhaseSelected_mhat_eq_one Z T P r ⟨i, j⟩
    simp_rw [hone, kc_two_one]
    norm_num
  have hrest :
      (∑ z : DUTPhaseRest Z T P r,
        kc 2
          (D.mhat
            (dutPhaseSplitEquiv Z T P r (Sum.inr z))))
        =
      ∑ z : DUTPhaseRest Z T P r,
        kc 2 (D.mhat z.1) := by
    simp
  rw [hsel, hrest] at hre
  exact hre.symm

/-- Integer c=3 charge splits as 30 per selected six-block plus untouched
integer charge. -/
lemma dutPhase_integer_charge_split_three
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    (∑ z : DUTPhaseDOnLine Z T P,
      kc 3
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z))
      =
    (∑ _i : DUTPhaseStart (dutCoreCount Z T) r, (30 : ℝ))
      +
    ∑ z : DUTPhaseRest Z T P r,
      kc 3
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1) := by
  let D :=
    blockData Z T (P.atD T) (dutD_phiHatConj P T)
  have hre :=
    sum_kc_equiv_reindex
      (dutPhaseSplitEquiv Z T P r)
      3 (fun z : DUTPhaseDOnLine Z T P => D.mhat z)
  rw [Fintype.sum_sum_type] at hre
  have hsel :
      (∑ x : DUTPhaseAtom (dutCoreCount Z T) r,
        kc 3
          (D.mhat
            (dutPhaseSplitEquiv Z T P r (Sum.inl x))))
        =
      ∑ _i : DUTPhaseStart (dutCoreCount Z T) r, (30 : ℝ) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dutPhaseSplitEquiv_inl]
    have hone :
        ∀ j : Fin 6,
          D.mhat
            (dutPhaseSelectedOnLine Z T P r
              ⟨i, j⟩) = 1 :=
      fun j => dutPhaseSelected_mhat_eq_one Z T P r ⟨i, j⟩
    simp_rw [hone, kc_three_one]
    norm_num
  have hrest :
      (∑ z : DUTPhaseRest Z T P r,
        kc 3
          (D.mhat
            (dutPhaseSplitEquiv Z T P r (Sum.inr z))))
        =
      ∑ z : DUTPhaseRest Z T P r,
        kc 3 (D.mhat z.1) := by
    simp
  rw [hsel, hrest] at hre
  exact hre.symm

/-- **Actual one-phase global replacement.**

The local hypotheses are exactly the conclusions supplied by the certified
six-block theorem for every valid start in this residue class. -/
theorem dutPhaseReplacement
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hcNorm :
      0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hxsq :
      ∀ z : DUTPhaseDOnLine Z T P,
        xsq
          ((blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2))
          z ≤ 1)
    (hlocal :
      ∀ i : DUTPhaseStart (dutCoreCount Z T) r,
        Pmat (fun _ : Fin 6 => (1 : ℝ))
            (dutPhaseRotatedBlockV Z T P r i)
          =
        Pmat (fun _ : Fin 6 => (1 : ℝ))
            (dutPhaseOriginalBlockV Z T P r i)
        ∧
        (∑ j : Fin 6,
          kc 2
            (xsq (dutPhaseRotatedBlockV Z T P r i) j))
          ≤
        18 - dutCoreWindowSaving Z T P (i : ℕ)
        ∧
        (∑ j : Fin 6,
          kc 3
            (xsq (dutPhaseRotatedBlockV Z T P r i) j))
          ≤
        30 - dutCoreWindowSaving Z T P (i : ℕ)) :
    Pmat
        (dutPhaseAltM Z T P r)
        (dutPhaseAltV Z T P r)
      =
    (blockData Z T (P.atD T)
      (dutD_phiHatConj P T)).blockP
        ((P.atD T).a T * (P.atD T).L T ^ 2)
    ∧
    (∑ x,
      kc 2
        (dutPhaseAltM Z T P r x *
          xsq (dutPhaseAltV Z T P r) x))
      ≤
    (∑ z : DUTPhaseDOnLine Z T P,
      kc 2
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z))
      -
    dutPhaseContribution
      (dutCoreWindowSaving Z T P)
      (dutCoreCount Z T) r
    ∧
    (∑ x,
      kc 3
        (dutPhaseAltM Z T P r x *
          xsq (dutPhaseAltV Z T P r) x))
      ≤
    (∑ z : DUTPhaseDOnLine Z T P,
      kc 3
        ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z))
      -
    dutPhaseContribution
      (dutCoreWindowSaving Z T P)
      (dutCoreCount Z T) r := by
  have hPmat :=
    dutPhaseAltPmat_eq_blockP
      Z T P r hcNorm (fun i => (hlocal i).1)

  have hleft2 :
      (∑ x : DUTPhaseAtom (dutCoreCount Z T) r,
        kc 2
          (xsq
            (fun y : DUTPhaseAtom (dutCoreCount Z T) r =>
              dutPhaseRotatedBlockV Z T P r y.1 y.2)
            x))
        ≤
      (∑ _i : DUTPhaseStart (dutCoreCount Z T) r, (18 : ℝ))
        -
      ∑ i : DUTPhaseStart (dutCoreCount Z T) r,
        dutCoreWindowSaving Z T P (i : ℕ) := by
    exact
      sum_kc_sigma_le_of_fiber
        (n := Fin ((P.atD T).d T))
        (𝕜 := ℂ)
        2
        (fun i => dutPhaseRotatedBlockV Z T P r i)
        (fun _ => (18 : ℝ))
        (fun i => dutCoreWindowSaving Z T P (i : ℕ))
        (fun i => (hlocal i).2.1)

  have hleft3 :
      (∑ x : DUTPhaseAtom (dutCoreCount Z T) r,
        kc 3
          (xsq
            (fun y : DUTPhaseAtom (dutCoreCount Z T) r =>
              dutPhaseRotatedBlockV Z T P r y.1 y.2)
            x))
        ≤
      (∑ _i : DUTPhaseStart (dutCoreCount Z T) r, (30 : ℝ))
        -
      ∑ i : DUTPhaseStart (dutCoreCount Z T) r,
        dutCoreWindowSaving Z T P (i : ℕ) := by
    exact
      sum_kc_sigma_le_of_fiber
        (n := Fin ((P.atD T).d T))
        (𝕜 := ℂ)
        3
        (fun i => dutPhaseRotatedBlockV Z T P r i)
        (fun _ => (30 : ℝ))
        (fun i => dutCoreWindowSaving Z T P (i : ℕ))
        (fun i => (hlocal i).2.2)

  have hrest2 :=
    dutPhaseRest_charge_le_integer
      Z T P r (c := 2) (by norm_num) hxsq
  have hrest3 :=
    dutPhaseRest_charge_le_integer
      Z T P r (c := 3) (by norm_num) hxsq

  have hsplit2 :=
    dutPhase_integer_charge_split_two Z T P r
  have hsplit3 :=
    dutPhase_integer_charge_split_three Z T P r

  have hphase :
      dutPhaseContribution
          (dutCoreWindowSaving Z T P)
          (dutCoreCount Z T) r
        =
      ∑ i : DUTPhaseStart (dutCoreCount Z T) r,
        dutCoreWindowSaving Z T P (i : ℕ) :=
    dutPhaseContribution_eq_sum_starts
      (dutCoreWindowSaving Z T P)
      (dutCoreCount Z T) r

  have haltSplit2 :
      (∑ x,
        kc 2
          (dutPhaseAltM Z T P r x *
            xsq (dutPhaseAltV Z T P r) x))
        =
      (∑ x : DUTPhaseAtom (dutCoreCount Z T) r,
        kc 2
          (xsq
            (fun y : DUTPhaseAtom (dutCoreCount Z T) r =>
              dutPhaseRotatedBlockV Z T P r y.1 y.2)
            x))
        +
      (∑ z : DUTPhaseRest Z T P r,
        kc 2
          ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1 *
            xsq
              ((blockData Z T (P.atD T)
                (dutD_phiHatConj P T)).vhat
                  ((P.atD T).a T * (P.atD T).L T ^ 2))
              z.1)) := by
    simpa [
      dutPhaseAltM, dutPhaseBaseM, dutPhaseAltV, xsq
    ] using
      (sum_kc_sumElim
        (n := Fin ((P.atD T).d T))
        (𝕜 := ℂ)
        2
        (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
        (fun x =>
          dutPhaseRotatedBlockV Z T P r x.1 x.2)
        (fun z : DUTPhaseRest Z T P r => (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1)
        (fun z : DUTPhaseRest Z T P r =>
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2) z.1))

  have haltSplit3 :
      (∑ x,
        kc 3
          (dutPhaseAltM Z T P r x *
            xsq (dutPhaseAltV Z T P r) x))
        =
      (∑ x : DUTPhaseAtom (dutCoreCount Z T) r,
        kc 3
          (xsq
            (fun y : DUTPhaseAtom (dutCoreCount Z T) r =>
              dutPhaseRotatedBlockV Z T P r y.1 y.2)
            x))
        +
      (∑ z : DUTPhaseRest Z T P r,
        kc 3
          ((blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1 *
            xsq
              ((blockData Z T (P.atD T)
                (dutD_phiHatConj P T)).vhat
                  ((P.atD T).a T * (P.atD T).L T ^ 2))
              z.1)) := by
    simpa [
      dutPhaseAltM, dutPhaseBaseM, dutPhaseAltV, xsq
    ] using
      (sum_kc_sumElim
        (n := Fin ((P.atD T).d T))
        (𝕜 := ℂ)
        3
        (fun _ : DUTPhaseAtom (dutCoreCount Z T) r => (1 : ℝ))
        (fun x =>
          dutPhaseRotatedBlockV Z T P r x.1 x.2)
        (fun z : DUTPhaseRest Z T P r => (blockData Z T (P.atD T)
          (dutD_phiHatConj P T)).mhat z.1)
        (fun z : DUTPhaseRest Z T P r =>
          (blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2) z.1))

  constructor
  · exact hPmat
  constructor
  · rw [haltSplit2, hphase]
    rw [hsplit2]
    linarith
  · rw [haltSplit3, hphase]
    rw [hsplit3]
    linarith

end Zeta23.ZeroSide.RankTraceMult
