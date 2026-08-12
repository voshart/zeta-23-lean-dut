/-
DUTPhaseRankTrace.lean

Apply the upstream multiplicity-aware rank-trace inequality to the alternative
one-phase decomposition built in DUTPhaseReplacement.

The crucial point is that `rank_trace_mult_k` accepts an arbitrary
nonnegative-mass decomposition `Pmat m v`.  Hence the Gram-eigenbasis rotated
blocks do NOT need an individual `xsq <= 1` bound.  The phase-replacement
theorem already supplies the sharper total charge estimate.

For one phase r, if the alternative decomposition preserves blockP and its
c=2 / c=3 charges are reduced by `dutPhaseContribution`, then

  4 tr(P+Q) - ||P+Q||_F^2 - 2 Ncount + phaseSaving <= s₁

and

  6 tr(P+Q) - ||P+Q||_F^2 - 3 Ncount + phaseSaving
    <= 2 * #(all distinct zeros in the enlarged block window).

This is the rank-trace seam immediately before concrete `hat(A_z)` and
six-phase averaging.

Intended location:
  Zeta23/ZeroSide/DUTPhaseRankTrace.lean
-/

import Zeta23.ZeroSide.DUTPhaseReplacement
import Zeta23.ZeroSide.Mult

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

abbrev DUTPhaseData
    (Z : ZeroConfig) (T : ℝ) (P : Params) :=
  blockData Z T (P.atD T) (dutD_phiHatConj P T)

abbrev dutPhaseNormC
    (T : ℝ) (P : Params) : ℝ :=
  (P.atD T).a T * (P.atD T).L T ^ 2

/-- The alternative phase masses are nonnegative: selected atoms have mass one
and untouched atoms retain their nonnegative integer multiplicity. -/
lemma dutPhaseAltM_nonneg
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) :
    ∀ x, 0 ≤ dutPhaseAltM Z T P r x := by
  intro x
  cases x with
  | inl a =>
      simp [dutPhaseAltM, dutPhaseBaseM]
  | inr z =>
      simp only [dutPhaseAltM, dutPhaseBaseM, Sum.elim_inr]
      exact (DUTPhaseData Z T P).mhat_nonneg z.1

/-- Integer c=2 on-line charge in the original decomposition. -/
lemma dutPhase_original_kc_two
    (Z : ZeroConfig) (T : ℝ) (P : Params) :
    (∑ z : DUTPhaseDOnLine Z T P,
      kc 2 ((DUTPhaseData Z T P).mhat z))
      =
    3 * ((DUTPhaseData Z T P).s₁ : ℝ)
      + 4 * ((DUTPhaseData Z T P).s₂ : ℝ) := by
  let D := DUTPhaseData Z T P
  have h :=
    sum_kc_two_nat
      (fun z : D.onLine => D.m z)
      (fun z => D.one_le_m z)
  simp only [ZeroBlockData.mhat] at h ⊢
  rw [
    h,
    D.card_sub_filter (fun n => n = 1),
    D.card_sub_filter (fun n => 2 ≤ n),
    D.card_onLine_m_eq_one
  ]
  have h2 :
      (D.onLine.filter (fun z => 2 ≤ D.m z)).card = D.s₂ := by
    unfold ZeroBlockData.s₂ ZeroBlockData.S₂ ZeroBlockData.onLine
    rw [Finset.filter_filter]
  rw [h2]

/-- One-phase c=2 rank-trace improvement from an already constructed
Pmat-preserving phase replacement. -/
theorem dutPhase_rank_trace_two_of_replacement
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hcNorm : 0 < dutPhaseNormC T P)
    (hPmat :
      Pmat
          (dutPhaseAltM Z T P r)
          (dutPhaseAltV Z T P r)
        =
      (DUTPhaseData Z T P).blockP
        (dutPhaseNormC T P))
    (hcharge :
      (∑ x,
        kc 2
          (dutPhaseAltM Z T P r x *
            xsq (dutPhaseAltV Z T P r) x))
        ≤
      (∑ z : DUTPhaseDOnLine Z T P,
        kc 2 ((DUTPhaseData Z T P).mhat z))
        -
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r) :
    4 *
        rtrace
          ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
            + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      frobSq
        ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
          + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      2 * ((DUTPhaseData Z T P).Ncount : ℝ)
      +
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r
      ≤
    ((DUTPhaseData Z T P).s₁ : ℝ) := by
  let D := DUTPhaseData Z T P
  let Pr :=
    mkPairReps Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (Z := Z) (T := T) (P := P.atD T)
        (dutD_phiHatConj P T))

  have hR :=
    rank_trace_mult_k
      (𝕜 := ℂ)
      (dutPhaseAltM_nonneg Z T P r)
      (dutPhaseAltV Z T P r)
      (D.blockQ_isHermitian (dutPhaseNormC T P))
      (D.posIndex_blockQ_le Pr hcNorm)
      (c := 2) (by norm_num)

  rw [hPmat] at hR

  have hk :=
    dutPhase_original_kc_two Z T P

  have hN :
      (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p
        ≤ D.Ncount := by
    exact_mod_cast
      D.s₁_add_two_s₂_add_two_p_le_Ncount Pr

  rw [hk] at hcharge
  rw [Fintype.sum_sum_type] at hcharge
  norm_num at hR
  dsimp only [D] at hN hR

  have hRcharge :
      4 *
          rtrace
            ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
              + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
        ≤
      3 * ((DUTPhaseData Z T P).s₁ : ℝ)
        + 4 * ((DUTPhaseData Z T P).s₂ : ℝ)
        - dutPhaseContribution
            (dutCoreWindowSaving Z T P)
            (dutCoreCount Z T) r
        + 4 * (Pr.p : ℝ)
        + frobSq
            ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
              + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P)) := by
    calc
      4 *
          rtrace
            ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
              + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
          ≤
        (∑ a₁,
            kc 2
              (dutPhaseAltM Z T P r (Sum.inl a₁) *
                xsq (dutPhaseAltV Z T P r) (Sum.inl a₁)))
          +
        (∑ a₂,
            kc 2
              (dutPhaseAltM Z T P r (Sum.inr a₂) *
                xsq (dutPhaseAltV Z T P r) (Sum.inr a₂)))
          + 4 * (Pr.p : ℝ)
          + frobSq
              ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
                + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P)) := hR
      _ ≤
        (3 * ((DUTPhaseData Z T P).s₁ : ℝ)
          + 4 * ((DUTPhaseData Z T P).s₂ : ℝ)
          - dutPhaseContribution
              (dutCoreWindowSaving Z T P)
              (dutCoreCount Z T) r)
          + 4 * (Pr.p : ℝ)
          + frobSq
              ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
                + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P)) := by
        linarith [hcharge]

  have hcount :
      3 * ((DUTPhaseData Z T P).s₁ : ℝ)
        + 4 * ((DUTPhaseData Z T P).s₂ : ℝ)
        + 4 * (Pr.p : ℝ)
        - 2 * ((DUTPhaseData Z T P).Ncount : ℝ)
      ≤ ((DUTPhaseData Z T P).s₁ : ℝ) := by
    linarith [hN]

  linarith [hRcharge, hcount]

/-- One-phase c=3 rank-trace improvement from an already constructed
Pmat-preserving phase replacement. -/
theorem dutPhase_rank_trace_three_of_replacement
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hcNorm : 0 < dutPhaseNormC T P)
    (hPmat :
      Pmat
          (dutPhaseAltM Z T P r)
          (dutPhaseAltV Z T P r)
        =
      (DUTPhaseData Z T P).blockP
        (dutPhaseNormC T P))
    (hcharge :
      (∑ x,
        kc 3
          (dutPhaseAltM Z T P r x *
            xsq (dutPhaseAltV Z T P r) x))
        ≤
      (∑ z : DUTPhaseDOnLine Z T P,
        kc 3 ((DUTPhaseData Z T P).mhat z))
        -
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r) :
    6 *
        rtrace
          ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
            + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      frobSq
        ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
          + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      3 * ((DUTPhaseData Z T P).Ncount : ℝ)
      +
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r
      ≤
    2 * (Fintype.card (ZI Z T) : ℝ) := by
  let D := DUTPhaseData Z T P
  let Pr :=
    mkPairReps Z T
      (evalVec Z T (P.atD T))
      (evalVec_reflect (Z := Z) (T := T) (P := P.atD T)
        (dutD_phiHatConj P T))

  have hR :=
    rank_trace_mult_k
      (𝕜 := ℂ)
      (dutPhaseAltM_nonneg Z T P r)
      (dutPhaseAltV Z T P r)
      (D.blockQ_isHermitian (dutPhaseNormC T P))
      (D.posIndex_blockQ_le Pr hcNorm)
      (c := 3) (by norm_num)

  rw [hPmat] at hR

  let a₁ : ℝ :=
    ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ)
  let a₂ : ℝ :=
    ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ)
  let a₃ : ℝ :=
    ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ)

  have hk :
      ∑ z : D.onLine, kc 3 (D.mhat z)
        = 5 * a₁ + 8 * a₂ + 9 * a₃ := by
    have h :=
      sum_kc_three_nat
        (fun z : D.onLine => D.m z)
        (fun z => D.one_le_m z)
    simp only [ZeroBlockData.mhat] at h ⊢
    rw [
      h,
      D.card_sub_filter (fun n => n = 1),
      D.card_sub_filter (fun n => n = 2),
      D.card_sub_filter (fun n => 3 ≤ n)
    ]

  have hs1 : a₁ = D.s₁ := by
    simp only [a₁]
    rw [D.card_onLine_m_eq_one]

  have hs2 : a₂ + a₃ = D.s₂ := by
    simp only [a₂, a₃]
    exact_mod_cast D.card_two_add_card_ge_three

  have hNon :
      a₁ + 2 * a₂ + 3 * a₃ ≤ D.Non :=
    D.Non_ge_weighted

  have hN :
      (D.Non : ℝ) + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.Non_add_two_p_le_Ncount Pr

  have hcard :
      (Fintype.card (ZI Z T) : ℝ)
        = D.s₁ + D.s₂ + 2 * Pr.p := by
    exact_mod_cast D.card_eq Pr

  have ha₂ : 0 ≤ a₂ := Nat.cast_nonneg _
  have ha₃ : 0 ≤ a₃ := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ Pr.p := Nat.cast_nonneg _

  rw [hk] at hcharge
  rw [Fintype.sum_sum_type] at hcharge
  norm_num at hR
  dsimp only [D] at hR hNon hN hcard hs1 hs2

  have hRcharge :
      6 *
          rtrace
            ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
              + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
        ≤
      5 * a₁ + 8 * a₂ + 9 * a₃
        - dutPhaseContribution
            (dutCoreWindowSaving Z T P)
            (dutCoreCount Z T) r
        + 9 * (Pr.p : ℝ)
        + frobSq
            ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
              + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P)) := by
    calc
      6 *
          rtrace
            ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
              + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
          ≤
        (∑ a₁,
            kc 3
              (dutPhaseAltM Z T P r (Sum.inl a₁) *
                xsq (dutPhaseAltV Z T P r) (Sum.inl a₁)))
          +
        (∑ a₂,
            kc 3
              (dutPhaseAltM Z T P r (Sum.inr a₂) *
                xsq (dutPhaseAltV Z T P r) (Sum.inr a₂)))
          + 9 * (Pr.p : ℝ)
          + frobSq
              ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
                + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P)) := hR
      _ ≤
        (5 * a₁ + 8 * a₂ + 9 * a₃
          - dutPhaseContribution
              (dutCoreWindowSaving Z T P)
              (dutCoreCount Z T) r)
          + 9 * (Pr.p : ℝ)
          + frobSq
              ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
                + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P)) := by
        linarith [hcharge]

  have hcount :
      5 * a₁ + 8 * a₂ + 9 * a₃
        + 9 * (Pr.p : ℝ)
        - 3 * ((DUTPhaseData Z T P).Ncount : ℝ)
      ≤ 2 * (Fintype.card (ZI Z T) : ℝ) := by
    linarith [hNon, hN, hcard, hs1, hs2, ha₂, ha₃, hp]

  linarith [hRcharge, hcount]

/-- Package the two one-phase strengthened rank-trace inequalities directly
from the output of `dutPhaseReplacement`. -/
theorem dutPhase_rank_trace_of_replacement
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hcNorm : 0 < dutPhaseNormC T P)
    (hrep :
      Pmat
          (dutPhaseAltM Z T P r)
          (dutPhaseAltV Z T P r)
        =
      (DUTPhaseData Z T P).blockP
        (dutPhaseNormC T P)
      ∧
      (∑ x,
        kc 2
          (dutPhaseAltM Z T P r x *
            xsq (dutPhaseAltV Z T P r) x))
        ≤
      (∑ z : DUTPhaseDOnLine Z T P,
        kc 2 ((DUTPhaseData Z T P).mhat z))
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
        kc 3 ((DUTPhaseData Z T P).mhat z))
        -
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r) :
    (4 *
        rtrace
          ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
            + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      frobSq
        ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
          + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      2 * ((DUTPhaseData Z T P).Ncount : ℝ)
      +
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r
      ≤
      ((DUTPhaseData Z T P).s₁ : ℝ))
    ∧
    (6 *
        rtrace
          ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
            + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      frobSq
        ((DUTPhaseData Z T P).blockP (dutPhaseNormC T P)
          + (DUTPhaseData Z T P).blockQ (dutPhaseNormC T P))
      -
      3 * ((DUTPhaseData Z T P).Ncount : ℝ)
      +
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r
      ≤
      2 * (Fintype.card (ZI Z T) : ℝ)) := by
  constructor
  · exact
      dutPhase_rank_trace_two_of_replacement
        Z T P r hcNorm hrep.1 hrep.2.1
  · exact
      dutPhase_rank_trace_three_of_replacement
        Z T P r hcNorm hrep.1 hrep.2.2

end Zeta23.ZeroSide.RankTraceMult
