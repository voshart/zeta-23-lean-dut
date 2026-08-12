/-
DUTFinalLam.lean

Concrete fixed-lambda instantiation of the abstract DUT endgame.

This follows Zeta23.ThmD.Final.thmD_lam_abstract verbatim on the prime/tail
side, replacing the ordinary zero-side block input by the verified DUT
six-point certificate.

The only additional hypothesis is the exact external verifier contract
`DUTSharpVerifierCertificate P`.

Intended location:
  Zeta23/ZeroSide/DUTFinalLam.lean
-/

import Zeta23.ThmD.Final
import Zeta23.ZeroSide.DUTEndgameAbstract

noncomputable section
set_option linter.unusedSectionVars false

open Filter Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Fixed-λ concrete DUT theorem for an abstract zero configuration carrying
the paper's analytic inputs. -/
theorem dut_thmD_lam_abstract
    (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (hcert : DUTSharpVerifierCertificate P) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (dutRate (ThmD.cStar P.lam) P.lam - ε)
          * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hLoc :=
    ThmD.localHypsCoreD_eventually hP

  have hTr :=
    ThmD.tracesBoundsD_concrete
      (Z := Z) hP H hLoc

  have hc :=
    ThmD.tendsto_cRatio_concrete hP Z

  have hc0 :=
    ThmD.cStar_pos hP.lam_pos hP.lam_le_one

  have ha :
      ∀ᶠ T in atTop,
        1 / 2 ≤ (ThmD.concreteDataD P Z).aT T
          ∧ (ThmD.concreteDataD P Z).aT T ≤ 1 :=
    (ThmD.concreteFactsD hP H hLoc).ab_range.mono
      fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩

  obtain ⟨θ₀, hTail, hθ₀⟩ :=
    ThmD.eventually_tailPackageD Z H hP

  obtain ⟨A₀, hA₀, hloc⟩ :=
    H.RvM.local_count

  have hNII :=
    Tail.eventually_NII_le Z hA₀ hloc

  have hGzGp :=
    ThmD.eventually_GzGpD Z H hP

  have hId :
      ∀ᶠ T in atTop,
        (P.atD T).trGtilde T
            = (ThmD.concreteDataD P Z).trG T
        ∧
        (P.atD T).trGtildeSq T
            = (ThmD.concreteDataD P Z).trG2 T
        ∧
        (P.atD T).a T
            = (ThmD.concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP,
        Params.atD_trGtildeSq T hP,
        Params.atD_a T hP⟩

  have hcalE :=
    Assembly.calE_tendsto_zero
      P hP.lam_pos hP.lam_le_one
      (zero_le_one.trans hP.one_le_w)

  exact
    dut_thmD_simple_abstract
      Z H P hP hlam
      (ThmD.concreteDataD P Z).aT
      (ThmD.concreteDataD P Z).bT
      (ThmD.concreteDataD P Z).JT
      (ThmD.concreteDataD P Z).trG
      (ThmD.concreteDataD P Z).trG2
      hTr hc0 hc ha hcert
      θ₀ hTail hθ₀ hNII hGzGp hId hcalE

/-- ζ, fixed λ: conditional only on the external DUT verifier certificate for
the standard Montgomery--Taylor parameter family. -/
theorem dut_thmD_simple_lam
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hcert :
      DUTSharpVerifierCertificate
        (paramsOf stdProfile lam)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (dutRate (ThmD.cStar lam) lam - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  have hP :=
    paramsOf_valid taperProfile_stdProfile h0 h1.le

  exact
    dut_thmD_lam_abstract
      zetaZeroConfig paperInputs_zeta
      (paramsOf stdProfile lam) hP h1 hcert

end Zeta23.ZeroSide.RankTraceMult
