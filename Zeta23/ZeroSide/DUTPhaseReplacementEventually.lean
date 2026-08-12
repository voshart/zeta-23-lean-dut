/-
DUTPhaseReplacementEventually.lean

Global wrapper from the already-built eventual local six-block certificate to
the six phase-replacement propositions consumed by DUTPhaseAverageRankTrace.

Intended location:
  Zeta23/ZeroSide/DUTPhaseReplacementEventually.lean
-/

import Zeta23.ZeroSide.DUTPhaseAverageRankTrace

noncomputable section
set_option linter.unusedSectionVars false

open Filter Matrix Finset RHLinalg
open scoped Topology BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Eventually, every one of the six phase replacements exists for every
zero configuration.  This discharges the `hrep` hypothesis used by the global
DUT rank-trace splice. -/
theorem dutPhaseReplacementResult_eventually
    (P : Params) (hP : P.Valid)
    (hcert : DUTSharpVerifierCertificate P) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (Z : ZeroConfig) (r : ℕ),
        r ∈ Finset.range 6 →
          DUTPhaseReplacementResult Z T P r := by
  filter_upwards [
    dutCoreSix_local_hypotheses_eventually P hP,
    dutCoreSix_certificate_eventually P hP hcert
  ] with T hloc hcertT

  rcases hloc with
    ⟨hTpos, h16, h4pi, hgap2, hdelta, hloss⟩

  have h8 : 8 * P.w ≤ P.L T := by
    have hw0 : 0 ≤ P.w :=
      le_trans zero_le_one hP.one_le_w
    linarith

  have hcNorm :
      0 < (P.atD T).a T * (P.atD T).L T ^ 2 :=
    dutD_normConst_pos hP h8 h4pi

  intro Z r hr

  have hxsq :
      ∀ z : DUTPhaseDOnLine Z T P,
        xsq
          ((blockData Z T (P.atD T)
            (dutD_phiHatConj P T)).vhat
              ((P.atD T).a T * (P.atD T).L T ^ 2))
          z ≤ 1 := by
    intro z
    let D :=
      blockData Z T (P.atD T) (dutD_phiHatConj P T)
    change
      xsq
        (D.vhat ((P.atD T).a T * (P.atD T).L T ^ 2))
        z ≤ 1
    exact
      D.xsq_vhat_le
        hcNorm
        (sum_normSq_v_le
          Z T (P.atD T)
          (dutD_phiHatConj P T)
          (dutD_phiHatReal P T)
          (ThmD.poissonSqD hP h8))
        z

  have hlocal :
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
        30 - dutCoreWindowSaving Z T P (i : ℕ) := by
    intro i
    have hi := dutPhaseStart_hi i
    have hc := hcertT Z (i : ℕ) hi
    simpa [
      dutPhaseOriginalBlockV,
      dutPhaseRotatedBlockV,
      dutCoreWindowSaving,
      hi
    ] using hc

  exact
    dutPhaseReplacementResult_of_local
      Z T P r hcNorm hxsq hlocal

end Zeta23.ZeroSide.RankTraceMult
