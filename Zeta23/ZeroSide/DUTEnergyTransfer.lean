/-
DUTEnergyTransfer.lean

Quantitative Lean-side interface for the remaining finite-Gabor -> ideal-kernel
transfer.

The hard analytic input may be stated as two scalar comparisons between the
actual six-zero Gram matrix A and an ideal six-by-six kernel matrix K:

  |frobSq A - frobSq K| <= epsF,
  |rtrace A - rtrace K| <= epsT.

Since

  dutGramEnergy B = frobSq B - 2 * rtrace B + 6,

these imply

  dutGramEnergy A >= dutGramEnergy K - (epsF + 2 epsT).

Thus an ideal-kernel certificate with this explicit transfer margin yields the
actual finite-block certificate already consumed by DUTGramEnergy.

This module does NOT prove the analytic estimates epsF, epsT and does NOT
formalize the external interval certificate.  It only kernel-checks their exact
quantitative interface.

Intended location:
  Zeta23/ZeroSide/DUTEnergyTransfer.lean
-/

import Zeta23.ZeroSide.DUTGramEnergy

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Frobenius-square and real-trace transfer bounds control the DUT Gram
energy with the explicit loss `epsF + 2 * epsT`. -/
lemma dutGramEnergy_transfer_lower
    {𝕜 : Type*} [RCLike 𝕜]
    (A K : Matrix (Fin 6) (Fin 6) 𝕜)
    {epsF epsT : ℝ}
    (hfrob : |frobSq A - frobSq K| ≤ epsF)
    (htrace : |rtrace A - rtrace K| ≤ epsT) :
    dutGramEnergy K - (epsF + 2 * epsT) ≤ dutGramEnergy A := by
  have hfrob_lower : -epsF ≤ frobSq A - frobSq K :=
    (abs_le.mp hfrob).1
  have htrace_upper : rtrace A - rtrace K ≤ epsT :=
    (abs_le.mp htrace).2
  unfold dutGramEnergy
  linarith

/-- If the ideal-kernel energy beats the DUT certificate by the explicit
transfer loss, then the actual finite Gram matrix satisfies the unmodified DUT
certificate. -/
lemma dutCertificateRhs_le_actualGramEnergy_of_transfer
    {𝕜 : Type*} [RCLike 𝕜]
    (A K : Matrix (Fin 6) (Fin 6) 𝕜)
    (span epsF epsT : ℝ)
    (hideal : dutCertificateRhs span + epsF + 2 * epsT ≤ dutGramEnergy K)
    (hfrob : |frobSq A - frobSq K| ≤ epsF)
    (htrace : |rtrace A - rtrace K| ≤ epsT) :
    dutCertificateRhs span ≤ dutGramEnergy A := by
  have htransfer := dutGramEnergy_transfer_lower A K hfrob htrace
  linarith

/-- Concrete consecutive-six-zero theorem with the remaining analytic transfer
fully exposed.

`K` is an ideal six-by-six kernel matrix.  The external/analytic work only has
to supply:

* an ideal energy lower bound with margin `epsF + 2*epsT`;
* a Frobenius-square transfer estimate;
* a real-trace transfer estimate.

Lean then gives the actual upstream block rotation, `Pmat` preservation, and
both c=2 and c=3 charge savings. -/
theorem dut_consecutive_six_certificate_of_ideal_transfer
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (K : Matrix (Fin 6) (Fin 6) ℂ)
    (epsF epsT : ℝ)
    (hideal : dutCertificateRhs span + epsF + 2 * epsT ≤ dutGramEnergy K)
    (hfrob :
      |frobSq (dutSixGramMatrix Z T P hconj i hi) - frobSq K| ≤ epsF)
    (htrace :
      |rtrace (dutSixGramMatrix Z T P hconj i hi) - rtrace K| ≤ epsT) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  have henergy : dutCertificateRhs span ≤
      dutGramEnergy (dutSixGramMatrix Z T P hconj i hi) :=
    dutCertificateRhs_le_actualGramEnergy_of_transfer
      (dutSixGramMatrix Z T P hconj i hi) K span epsF epsT
      hideal hfrob htrace
  exact dut_consecutive_six_certificate_of_gram_energy
    Z T P hconj hreal hPois hc i hi span hspan henergy

end Zeta23.ZeroSide.RankTraceMult
