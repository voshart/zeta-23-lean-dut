/-
DUTGramEnergy.lean

Eliminate the spectral-eigenvalue presentation from the remaining DUT
certificate seam.

For a Hermitian 6x6 matrix B with eigenvalues lambda_j,

  sum_j (lambda_j - 1)^2 = ||B||_F^2 - 2 Re tr(B) + 6.

Thus the external/analytic fixed-block transfer does not need to reason about
eigenvalues at all: it may prove a lower bound directly for a concrete Gram
matrix energy.  The existing kernel-checked certificate interface then turns
that bound into both c=2 and c=3 DUT charge savings.

Intended location:
  Zeta23/ZeroSide/DUTGramEnergy.lean
-/

import Zeta23.ZeroSide.DUTCertifiedBlocks

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Matrix-side version of the six-point quadratic energy.  For Hermitian
`B`, this equals `sum_j (lambda_j(B)-1)^2`. -/
def dutGramEnergy {𝕜 : Type*} [RCLike 𝕜]
    (B : Matrix (Fin 6) (Fin 6) 𝕜) : ℝ :=
  frobSq B - 2 * rtrace B + 6

/-- The spectral energy used by `DUTCertificateInterface` is exactly the
concrete Frobenius/trace energy of a Hermitian six-by-six matrix. -/
lemma dutSpectralEnergy_eq_dutGramEnergy
    {𝕜 : Type*} [RCLike 𝕜]
    (B : Matrix (Fin 6) (Fin 6) 𝕜) (hB : B.IsHermitian) :
    dutSpectralEnergy hB.eigenvalues = dutGramEnergy B := by
  unfold dutSpectralEnergy dutGramEnergy
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hB,
      rtrace_eq_sum_eigenvalues hB]
  calc
    (∑ j, (hB.eigenvalues j - 1) ^ 2)
        = ∑ j, ((hB.eigenvalues j) ^ 2 - 2 * hB.eigenvalues j + 1) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j, (hB.eigenvalues j) ^ 2)
          - 2 * (∑ j, hB.eigenvalues j) + 6 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            norm_num

/-- The actual six-by-six column Gram matrix of six consecutive normalized
upstream simple-zero evaluation vectors. -/
noncomputable def dutSixGramMatrix
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) : Matrix (Fin 6) (Fin 6) ℂ :=
  let v := dutSixVhat Z T P hconj i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  Wᴴ * W

lemma dutSixGramMatrix_posSemidef
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    (dutSixGramMatrix Z T P hconj i hi).PosSemidef := by
  unfold dutSixGramMatrix
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- For an actual consecutive six-zero block, the spectral energy in the
certificate interface is exactly its concrete Gram-matrix energy. -/
lemma dutSpectralEnergy_dutSixGramSpectrum_eq
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    dutSpectralEnergy (dutSixGramSpectrum Z T P hconj i hi) =
      dutGramEnergy (dutSixGramMatrix Z T P hconj i hi) := by
  unfold dutSixGramSpectrum dutSixGramMatrix
  exact dutSpectralEnergy_eq_dutGramEnergy _
    (Matrix.posSemidef_conjTranspose_mul_self _).1

/-- Concrete certificate theorem with **no eigenvalues in the external
hypothesis**.  It is enough to establish the certified lower bound for the
Frobenius/trace energy of the actual six-zero Gram matrix. -/
theorem dut_consecutive_six_certificate_of_gram_energy
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T)
    (span : ℝ) (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤
      dutGramEnergy (dutSixGramMatrix Z T P hconj i hi)) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤ 18 - dutCertificateRhs span
      ∧
    (∑ j, kc 3 (xsq vr j)) ≤ 30 - dutCertificateRhs span := by
  have henergy' : dutCertificateRhs span ≤
      dutSpectralEnergy (dutSixGramSpectrum Z T P hconj i hi) := by
    rw [dutSpectralEnergy_dutSixGramSpectrum_eq]
    exact henergy
  exact dut_consecutive_six_certificate_both
    Z T P hconj hreal hPois hc i hi span hspan henergy'

end Zeta23.ZeroSide.RankTraceMult
