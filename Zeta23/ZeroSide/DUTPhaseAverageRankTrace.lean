/-
DUTPhaseAverageRankTrace.lean

Six-phase averaging of the strengthened rank-trace inequalities.

DUTPhaseReplacement constructs, for each residue class mod 6, an alternative
global decomposition with the same blockP and a charge saving equal to that
phase's sum of local DUT certificate savings.

DUTPhaseRankTrace converts such a replacement into the strengthened c=2/c=3
rank-trace inequalities for that phase.

DUTCorePhaseCertificate then averages the six phase inequalities and lower
bounds the total phase saving by the explicit buffered DUT term

  (dutEta / 6) *
    (dutR * (dutCoreCount - 5)
      - 5 * (L*T/(2*pi))).

This file packages exactly that composition.

Intended location:
  Zeta23/ZeroSide/DUTPhaseAverageRankTrace.lean
-/

import Zeta23.ZeroSide.DUTPhaseRankTrace

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The common c=2 rank-trace expression before the phase saving. -/
noncomputable def dutPhaseRankBaseTwo
    (Z : ZeroConfig) (T : ℝ) (P : Params) : ℝ :=
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

/-- The common c=3 rank-trace expression before the phase saving. -/
noncomputable def dutPhaseRankBaseThree
    (Z : ZeroConfig) (T : ℝ) (P : Params) : ℝ :=
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

/-- Named proposition for the output of one actual phase replacement. -/
def DUTPhaseReplacementResult
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ) : Prop :=
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
    (dutCoreCount Z T) r

/-- Existing one-phase replacement theorem, repackaged under the named
proposition above. -/
lemma dutPhaseReplacementResult_of_local
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
    DUTPhaseReplacementResult Z T P r := by
  unfold DUTPhaseReplacementResult
  exact
    dutPhaseReplacement
      Z T P r hcNorm hxsq hlocal

/-- A replacement result yields the two strengthened one-phase rank-trace
inequalities in compact base-expression form. -/
lemma dutPhase_rank_trace_compact
    (Z : ZeroConfig) (T : ℝ) (P : Params) (r : ℕ)
    (hcNorm : 0 < dutPhaseNormC T P)
    (hrep : DUTPhaseReplacementResult Z T P r) :
    dutPhaseRankBaseTwo Z T P
        +
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r
      ≤
      ((DUTPhaseData Z T P).s₁ : ℝ)
    ∧
    dutPhaseRankBaseThree Z T P
        +
      dutPhaseContribution
        (dutCoreWindowSaving Z T P)
        (dutCoreCount Z T) r
      ≤
      2 * (Fintype.card (ZI Z T) : ℝ) := by
  have h :=
    dutPhase_rank_trace_of_replacement
      Z T P r hcNorm (by
        simpa [DUTPhaseReplacementResult] using hrep)
  simpa [
    dutPhaseRankBaseTwo,
    dutPhaseRankBaseThree
  ] using h

/-- **Six-phase averaged strengthened rank-trace inequalities.**

Assuming a valid replacement has been constructed in each of the six residue
classes, the averaged saving is bounded below by the explicit core DUT term. -/
theorem dutPhase_average_rank_trace
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (hcNorm : 0 < dutPhaseNormC T P)
    (hrep :
      ∀ r ∈ Finset.range 6,
        DUTPhaseReplacementResult Z T P r) :
    dutPhaseRankBaseTwo Z T P
        +
      (dutEta / 6) *
        (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
          - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤
      ((DUTPhaseData Z T P).s₁ : ℝ)
    ∧
    dutPhaseRankBaseThree Z T P
        +
      (dutEta / 6) *
        (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
          - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤
      2 * (Fintype.card (ZI Z T) : ℝ) := by
  have hphase2 :
      ∀ r ∈ Finset.range 6,
        dutPhaseRankBaseTwo Z T P
          +
        dutPhaseContribution
          (dutCoreWindowSaving Z T P)
          (dutCoreCount Z T) r
        ≤
        ((DUTPhaseData Z T P).s₁ : ℝ) := by
    intro r hr
    exact
      (dutPhase_rank_trace_compact
        Z T P r hcNorm (hrep r hr)).1

  have hphase3 :
      ∀ r ∈ Finset.range 6,
        dutPhaseRankBaseThree Z T P
          +
        dutPhaseContribution
          (dutCoreWindowSaving Z T P)
          (dutCoreCount Z T) r
        ≤
        2 * (Fintype.card (ZI Z T) : ℝ) := by
    intro r hr
    exact
      (dutPhase_rank_trace_compact
        Z T P r hcNorm (hrep r hr)).2

  constructor
  · exact
      dutCore_certificate_phase_averaged_counting
        (simple := ((DUTPhaseData Z T P).s₁ : ℝ))
        (Lbase := dutPhaseRankBaseTwo Z T P)
        Z T P hL hs6 hphase2
  · exact
      dutCore_certificate_phase_averaged_counting
        (simple := 2 * (Fintype.card (ZI Z T) : ℝ))
        (Lbase := dutPhaseRankBaseThree Z T P)
        Z T P hL hs6 hphase3

end Zeta23.ZeroSide.RankTraceMult
