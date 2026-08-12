/-
DUTCoreCertifiedBlocks.lean

Splice the interior-core finite-grid/sharp-kernel transfer into the existing
DUT six-point certificate machinery.

This file closes the Lean-side local block chain:

  sharp six-point energy with transfer margin
      -> actual core Gram energy
      -> Gram spectrum energy
      -> c=2 and c=3 DUT defect saving
      -> verified Gram-eigenbasis rotation preserving Pmat.

No external numerical certificate is formalized here.  The remaining local
input is a lower bound for the ideal sharp matrix energy with the explicit
matrix-transfer loss already proved in DUTMatrixTransfer.

Intended location:
  Zeta23/ZeroSide/DUTCoreCertifiedBlocks.lean
-/

import Zeta23.ZeroSide.DUTMatrixTransfer

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Spectrum of the actual interior-core Theorem-D Gram matrix. -/
noncomputable def dutCoreSixGramSpectrumD
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) : Fin 6 → ℝ :=
  (dutCoreSixGramMatrixD_posSemidef Z T P i hi).1.eigenvalues

lemma dutCoreSixGramSpectrumD_nonneg
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    0 ≤ dutCoreSixGramSpectrumD Z T P i hi j := by
  unfold dutCoreSixGramSpectrumD
  exact
    (dutCoreSixGramMatrixD_posSemidef Z T P i hi).eigenvalues_nonneg j

/-- Squared norms after the Gram-eigenbasis rotation are exactly the spectrum
of the actual core Gram matrix. -/
lemma xsq_dutCoreSix_rotated_eq_spectrum
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    let v := dutCoreSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    xsq vr j = dutCoreSixGramSpectrumD Z T P i hi j := by
  dsimp only
  unfold dutCoreSixGramSpectrumD dutCoreSixGramMatrixD
  exact
    xsq_columns_gramEigenRotateMatrix
      (Wmat (fun _ : Fin 6 => (1 : ℝ))
        (dutCoreSixVhatD Z T P i hi)) j

/-- Spectral quadratic energy equals the concrete core Gram energy. -/
lemma dutSpectralEnergy_coreSpectrum_eq
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    dutSpectralEnergy (dutCoreSixGramSpectrumD Z T P i hi)
      =
      dutGramEnergy (dutCoreSixGramMatrixD Z T P i hi) := by
  unfold dutCoreSixGramSpectrumD
  exact
    dutSpectralEnergy_eq_dutGramEnergy
      (dutCoreSixGramMatrixD Z T P i hi)
      (dutCoreSixGramMatrixD_posSemidef Z T P i hi).1

/-- **Core-block certificate from actual Gram energy.**

Once the actual interior-core Gram matrix has the certified energy, Lean
derives the verified rotation, Pmat invariance, and both c=2/c=3 savings. -/
theorem dutCoreSix_certificate_of_gram_energy
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (span : ℝ) (hspan : 0 ≤ span)
    (henergy :
      dutCertificateRhs span ≤
        dutGramEnergy (dutCoreSixGramMatrixD Z T P i hi)) :
    let v := dutCoreSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  dsimp only
  let v := dutCoreSixVhatD Z T P i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  let vr := columns (gramEigenRotateMatrix W)

  have htrace : (∑ j, xsq v j) ≤ 6 := by
    simpa [v] using
      sum_xsq_dutCoreSixVhatD_le_six
        Z T P hP h8 h4pi i hi

  have hrot2 := fin6_rotated_charge_and_P v htrace
  have hrot3 := fin6_rotated_charge3_and_P v htrace

  have hspecEnergy :
      dutCertificateRhs span ≤
        dutSpectralEnergy
          (dutCoreSixGramSpectrumD Z T P i hi) := by
    rw [dutSpectralEnergy_coreSpectrum_eq]
    exact henergy

  have hcert2 :
      dutCertificateRhs span ≤
        ∑ j, dutDefect2
          (dutCoreSixGramSpectrumD Z T P i hi j) :=
    dutDefect2_ge_certificate_of_energy
      (dutCoreSixGramSpectrumD Z T P i hi)
      (dutCoreSixGramSpectrumD_nonneg Z T P i hi)
      hspan hspecEnergy

  have hcert3 :
      dutCertificateRhs span ≤
        ∑ j, dutDefect3
          (dutCoreSixGramSpectrumD Z T P i hi j) :=
    dutDefect3_ge_certificate_of_energy
      (dutCoreSixGramSpectrumD Z T P i hi)
      (dutCoreSixGramSpectrumD_nonneg Z T P i hi)
      hspan hspecEnergy

  have hdef2 :
      (∑ j, dutDefect2 (xsq vr j))
        =
      ∑ j, dutDefect2
        (dutCoreSixGramSpectrumD Z T P i hi j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [xsq_dutCoreSix_rotated_eq_spectrum Z T P i hi j]

  have hdef3 :
      (∑ j, dutDefect3 (xsq vr j))
        =
      ∑ j, dutDefect3
        (dutCoreSixGramSpectrumD Z T P i hi j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [xsq_dutCoreSix_rotated_eq_spectrum Z T P i hi j]

  constructor
  · simpa [v, W, vr] using hrot2.1
  constructor
  · have hrot2' :
        (∑ j, kc 2 (xsq vr j))
          ≤ 18 - ∑ j, dutDefect2 (xsq vr j) := by
      simpa [v, W, vr] using hrot2.2
    rw [hdef2] at hrot2'
    linarith
  · have hrot3' :
        (∑ j, kc 3 (xsq vr j))
          ≤ 30 - ∑ j, dutDefect3 (xsq vr j) := by
      simpa [v, W, vr] using hrot3.2
    rw [hdef3] at hrot3'
    linarith

/-- Explicit matrix-transfer loss used to transport the sharp certificate to
the actual finite core Gram matrix. -/
noncomputable def dutCoreSixTransferLoss
    (T : ℝ) (P : Params) : ℝ :=
  36 * dutCoreSixEntryError T P *
      (9 + dutCoreSixEntryError T P)
    + 12 * dutCoreSixEntryError T P

/-- **Main local splice.**

If the ideal sharp six-point matrix beats the corrected certificate by the
explicit finite-grid/kernel-transfer loss, then the actual interior-core block
already satisfies both DUT charge savings. -/
theorem dutCoreSix_certificate_of_sharp_margin
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 : 0 < D0 T - 2 * (P.atD T).hgrid T)
    (hδ : 0 ≤ dutCoreSixEntryError T P)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (span : ℝ) (hspan : 0 ≤ span)
    (hsharp :
      dutCertificateRhs span + dutCoreSixTransferLoss T P
        ≤ dutGramEnergy (dutCoreSixSharpMatrix Z T P i hi)) :
    let v := dutCoreSixVhatD Z T P i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  have h8 : 8 * P.w ≤ P.L T := by
    have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
    linarith

  have htransfer :=
    dutCoreSix_energy_transfer_from_sharp
      Z T P hP hT h16 h4pi hgap2 hδ i hi

  have henergy :
      dutCertificateRhs span ≤
        dutGramEnergy (dutCoreSixGramMatrixD Z T P i hi) := by
    unfold dutCoreSixTransferLoss at hsharp
    linarith

  exact
    dutCoreSix_certificate_of_gram_energy
      Z T P hP h8 h4pi i hi span hspan henergy

end Zeta23.ZeroSide.RankTraceMult
