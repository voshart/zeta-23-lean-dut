/-
DUTThmDBlocks.lean

Correct concrete DUT bridge for Anthropic's Theorem-D cosine window.

The previously checked generic DUTZeroBlocks/DUTCertifiedBlocks modules are
valid for every Params value.  This file instantiates them at the height-T
window-realizing parameter set `P.atD T` from Zeta23.ThmD.ParamsD.  At height
T this is exactly Anthropic's Montgomery--Taylor window

  phi_D(u) = sqrt(cos(sqrt 2 * P.lam * u / P.L T)) * taper(u).

Thus the concrete six-zero Gram matrices below have the cosine-bulk limiting
kernel with kappa = sqrt 2 * P.lam, not the flat/sinc limiting kernel.

Intended location:
  Zeta23/ZeroSide/DUTThmDBlocks.lean
-/

import Zeta23.ThmD.ZeroSideD
import Zeta23.ZeroSide.DUTEnergyTransfer

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Conjugation symmetry for the height-T Theorem-D window. -/
lemma dutD_phiHatConj (P : Params) (T : ℝ) :
    PhiHatConj T (P.atD T) :=
  fun z => GzGp.phiHat_conj (P.atD T) T z

/-- Reality of the Fourier transform on the real axis for the height-T
Theorem-D window. -/
lemma dutD_phiHatReal (P : Params) (T : ℝ) :
    PhiHatReal T (P.atD T) :=
  fun r => GzGp.phiHat_ofReal (P.atD T) T r

/-- Positivity of the normalization constant used for the six normalized
Theorem-D evaluation vectors. -/
lemma dutD_normConst_pos {P : Params} (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T) :
    0 < (P.atD T).a T * (P.atD T).L T ^ 2 := by
  have ha : 0 < (P.atD T).a T := by
    linarith [(ThmD.aD_range_of hP h8 h4pi).1]
  have hL : 0 < (P.atD T).L T := by
    rw [Params.atD_L]
    linarith [hP.one_le_w]
  exact mul_pos ha (pow_pos hL 2)

/-- Six consecutive simple-zero vectors for Anthropic's Theorem-D cosine
window.  This is just the already checked generic `dutSixVhat` instantiated at
`P.atD T`. -/
noncomputable def dutSixVhatD
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :=
  dutSixVhat Z T (P.atD T) (dutD_phiHatConj P T) i hi

/-- Actual six-by-six Gram matrix of the Theorem-D-window block. -/
noncomputable def dutSixGramMatrixD
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < Z.s1 T) : Matrix (Fin 6) (Fin 6) ℂ :=
  dutSixGramMatrix Z T (P.atD T) (dutD_phiHatConj P T) i hi

/-- The upstream Poisson theorem gives the trace <= 6 hypothesis for every
actual six-zero block built from the Theorem-D window. -/
lemma sum_xsq_dutSixVhatD_le_six
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    (∑ j, xsq (dutSixVhatD Z T P i hi) j) ≤ 6 := by
  exact sum_xsq_dutSixVhat_le_six Z T (P.atD T)
    (dutD_phiHatConj P T) (dutD_phiHatReal P T)
    (ThmD.poissonSqD hP h8) (dutD_normConst_pos hP h8 h4pi) i hi

/-- Concrete local DUT rotation/charge theorem for the *actual Theorem-D
cosine window*. -/
theorem dut_consecutive_six_rotated_charge_and_P_D
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    let v := dutSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤
      18 - ∑ j, dutDefect2 (xsq vr j) := by
  exact fin6_rotated_charge_and_P
    (dutSixVhatD Z T P i hi)
    (sum_xsq_dutSixVhatD_le_six Z T P hP h8 h4pi i hi)

/-- If the remaining Gram-energy certificate is supplied for the actual
Theorem-D-window block, Lean gives both c=2 and c=3 local charge savings. -/
theorem dut_consecutive_six_certificate_of_gram_energy_D
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤
      dutGramEnergy (dutSixGramMatrixD Z T P i hi)) :
    let v := dutSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  exact dut_consecutive_six_certificate_of_gram_energy
    Z T (P.atD T) (dutD_phiHatConj P T) (dutD_phiHatReal P T)
    (ThmD.poissonSqD hP h8) (dutD_normConst_pos hP h8 h4pi)
    i hi span hspan henergy

/-- Same theorem with the remaining finite-window -> ideal-kernel transfer
exposed as Frobenius-square and trace errors. -/
theorem dut_consecutive_six_certificate_of_ideal_transfer_D
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (K : Matrix (Fin 6) (Fin 6) ℂ)
    (epsF epsT : ℝ)
    (hideal : dutCertificateRhs span + epsF + 2 * epsT ≤ dutGramEnergy K)
    (hfrob :
      |frobSq (dutSixGramMatrixD Z T P i hi) - frobSq K| ≤ epsF)
    (htrace :
      |rtrace (dutSixGramMatrixD Z T P i hi) - rtrace K| ≤ epsT) :
    let v := dutSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  exact dut_consecutive_six_certificate_of_ideal_transfer
    Z T (P.atD T) (dutD_phiHatConj P T) (dutD_phiHatReal P T)
    (ThmD.poissonSqD hP h8) (dutD_normConst_pos hP h8 h4pi)
    i hi span hspan K epsF epsT hideal hfrob htrace

end Zeta23.ZeroSide.RankTraceMult
