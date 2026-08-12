/-
DUTCertifiedBlocks.lean

Join the concrete six-zero bridge to the external certificate interface.

For an actual consecutive six-tuple of simple critical-line zeros, let W be
the matrix of the upstream normalized evaluation vectors and let lam be the
spectrum of WᴴW.  If an external/future transfer theorem supplies

  dutCertificateRhs span <= dutSpectralEnergy lam,

then Lean derives the corresponding c=2 and c=3 charge savings for the
Gram-eigenbasis rotation while preserving Pmat.

This module deliberately does NOT prove the finite-Gabor -> ideal-kernel
energy inequality.  That remains the next analytic/certificate seam.

Intended location:
  Zeta23/ZeroSide/DUTCertifiedBlocks.lean
-/

import Zeta23.ZeroSide.DUTZeroBlocks
import Zeta23.ZeroSide.DUTCertificateInterface

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Column-Gram spectrum of an actual consecutive six-zero DUT block. -/
noncomputable def dutSixGramSpectrum
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) : Fin 6 → ℝ :=
  let v := dutSixVhat Z T P hconj i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  (Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues

lemma dutSixGramSpectrum_nonneg
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) (j : Fin 6) :
    0 ≤ dutSixGramSpectrum Z T P hconj i hi j := by
  let v := dutSixVhat Z T P hconj i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  have hM : (Wᴴ * W).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self W
  change 0 ≤ hM.1.eigenvalues j
  exact hM.eigenvalues_nonneg j

/-- The squared norms after the verified Gram-eigenbasis rotation are exactly
`dutSixGramSpectrum`. -/
lemma xsq_dutSix_rotated_eq_spectrum
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) (j : Fin 6) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    xsq vr j = dutSixGramSpectrum Z T P hconj i hi j := by
  dsimp only
  exact xsq_columns_gramEigenRotateMatrix
    (Wmat (fun _ : Fin 6 => (1 : ℝ))
      (dutSixVhat Z T P hconj i hi)) j

/-- Concrete c=2 block consequence of a certified spectral-energy lower bound.
The only unproved input here is `henergy`. -/
theorem dut_consecutive_six_certificate_charge2
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤
      dutSpectralEnergy (dutSixGramSpectrum Z T P hconj i hi)) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span := by
  dsimp only
  let v := dutSixVhat Z T P hconj i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  let vr := columns (gramEigenRotateMatrix W)
  have htrace : (∑ j, xsq v j) ≤ 6 :=
    sum_xsq_dutSixVhat_le_six Z T P hconj hreal hPois hc i hi
  have hrot := fin6_rotated_charge_and_P v htrace
  have hcert : dutCertificateRhs span ≤
      ∑ j, dutDefect2 (dutSixGramSpectrum Z T P hconj i hi j) :=
    dutDefect2_ge_certificate_of_energy
      (dutSixGramSpectrum Z T P hconj i hi)
      (dutSixGramSpectrum_nonneg Z T P hconj i hi)
      hspan henergy
  have hdef : (∑ j, dutDefect2 (xsq vr j)) =
      ∑ j, dutDefect2 (dutSixGramSpectrum Z T P hconj i hi j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [xsq_dutSix_rotated_eq_spectrum Z T P hconj i hi j]
  constructor
  · simpa [v, W, vr] using hrot.1
  · have hrot' : (∑ j, kc 2 (xsq vr j)) ≤
        18 - ∑ j, dutDefect2 (xsq vr j) := by
      simpa [v, W, vr] using hrot.2
    rw [hdef] at hrot'
    linarith

/-- Concrete c=3 block consequence of the same certified spectral-energy lower
bound. -/
theorem dut_consecutive_six_certificate_charge3
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤
      dutSpectralEnergy (dutSixGramSpectrum Z T P hconj i hi)) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  dsimp only
  let v := dutSixVhat Z T P hconj i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  let vr := columns (gramEigenRotateMatrix W)
  have htrace : (∑ j, xsq v j) ≤ 6 :=
    sum_xsq_dutSixVhat_le_six Z T P hconj hreal hPois hc i hi
  have hrot := fin6_rotated_charge3_and_P v htrace
  have hcert : dutCertificateRhs span ≤
      ∑ j, dutDefect3 (dutSixGramSpectrum Z T P hconj i hi j) :=
    dutDefect3_ge_certificate_of_energy
      (dutSixGramSpectrum Z T P hconj i hi)
      (dutSixGramSpectrum_nonneg Z T P hconj i hi)
      hspan henergy
  have hdef : (∑ j, dutDefect3 (xsq vr j)) =
      ∑ j, dutDefect3 (dutSixGramSpectrum Z T P hconj i hi j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [xsq_dutSix_rotated_eq_spectrum Z T P hconj i hi j]
  constructor
  · simpa [v, W, vr] using hrot.1
  · have hrot' : (∑ j, kc 3 (xsq vr j)) ≤
        30 - ∑ j, dutDefect3 (xsq vr j) := by
      simpa [v, W, vr] using hrot.2
    rw [hdef] at hrot'
    linarith

/-- The same external six-point energy certificate supplies both local charge
savings for the concrete upstream block. -/
theorem dut_consecutive_six_certificate_both
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤
      dutSpectralEnergy (dutSixGramSpectrum Z T P hconj i hi)) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  dsimp only
  have h2 := dut_consecutive_six_certificate_charge2
    Z T P hconj hreal hPois hc i hi span hspan henergy
  have h3 := dut_consecutive_six_certificate_charge3
    Z T P hconj hreal hPois hc i hi span hspan henergy
  exact ⟨h2.1, h2.2, h3.2⟩

end Zeta23.ZeroSide.RankTraceMult
