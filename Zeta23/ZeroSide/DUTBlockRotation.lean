/-
DUTBlockRotation_draft.lean

Formalization draft for the one genuinely new finite-dimensional seam in DUT:
right-unitary mixing of a block of simple-zero columns preserves WWᴴ, while
choosing the eigenvector unitary of WᴴW makes the new column squared norms equal
to the Gram eigenvalues.

IMPORTANT: drafted against the Anthropic zeta-23-lean API inspected 2026-08-11,
but NOT kernel-checked in this runtime (Lean is unavailable here).
-/

import Zeta23.ZeroSide.DUTRankTrace

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable [Fintype ι] [DecidableEq ι]

/-- The unitary eigenbasis of the column Gram matrix `Wᴴ W`. -/
noncomputable def gramEigenU (W : Matrix n ι 𝕜) : Matrix.unitaryGroup ι 𝕜 :=
  (Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvectorUnitary

/-- Rotate the columns of `W` into an eigenbasis of `Wᴴ W`. -/
noncomputable def gramEigenRotateMatrix (W : Matrix n ι 𝕜) : Matrix n ι 𝕜 :=
  W * (gramEigenU W : Matrix ι ι 𝕜)

/-- Right multiplication by a unitary preserves the positive matrix `W Wᴴ`. -/
lemma mul_unitary_mul_conjTranspose_eq
    (W : Matrix n ι 𝕜) (U : Matrix.unitaryGroup ι 𝕜) :
    (W * (U : Matrix ι ι 𝕜)) * (W * (U : Matrix ι ι 𝕜))ᴴ = W * Wᴴ := by
  rw [Matrix.conjTranspose_mul]
  have hUU : (U : Matrix ι ι 𝕜) * star (U : Matrix ι ι 𝕜) = 1 := U.property.2
  calc
    (W * (U : Matrix ι ι 𝕜)) *
        ((U : Matrix ι ι 𝕜)ᴴ * Wᴴ)
        = W * ((U : Matrix ι ι 𝕜) * star (U : Matrix ι ι 𝕜)) * Wᴴ := by
            simp only [Matrix.star_eq_conjTranspose]
            simp only [Matrix.mul_assoc]
    _ = W * Wᴴ := by rw [hUU]; simp

/-- The rotated column Gram matrix is diagonal with the eigenvalues of `WᴴW`. -/
lemma gramEigenRotate_gram_eq_diagonal (W : Matrix n ι 𝕜) :
    (gramEigenRotateMatrix W)ᴴ * gramEigenRotateMatrix W =
      Matrix.diagonal (RCLike.ofReal ∘
        (Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues) := by
  let hM : (Wᴴ * W).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self W
  let U : Matrix.unitaryGroup ι 𝕜 := hM.1.eigenvectorUnitary
  let D : Matrix ι ι 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues)
  have hspec : Wᴴ * W = (U : Matrix ι ι 𝕜) * D * star (U : Matrix ι ι 𝕜) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.mul_assoc] using hM.1.spectral_theorem
  have hUstarU : star (U : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜) = 1 := U.property.1
  change (W * (U : Matrix ι ι 𝕜))ᴴ * (W * (U : Matrix ι ι 𝕜)) = D
  rw [Matrix.conjTranspose_mul]
  calc
    ((U : Matrix ι ι 𝕜)ᴴ * Wᴴ) * (W * (U : Matrix ι ι 𝕜))
        = (U : Matrix ι ι 𝕜)ᴴ * (Wᴴ * W) *
            (U : Matrix ι ι 𝕜) := by
              simp only [Matrix.mul_assoc]
    _ = (U : Matrix ι ι 𝕜)ᴴ *
          ((U : Matrix ι ι 𝕜) * D * star (U : Matrix ι ι 𝕜)) *
          (U : Matrix ι ι 𝕜) := by
            rw [hspec]
    _ = star (U : Matrix ι ι 𝕜) *
          ((U : Matrix ι ι 𝕜) * D * star (U : Matrix ι ι 𝕜)) *
          (U : Matrix ι ι 𝕜) := by
            simp only [Matrix.star_eq_conjTranspose]
    _ = (star (U : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜)) * D *
          (star (U : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜)) := by
            simp only [Matrix.mul_assoc]
    _ = D := by
          rw [hUstarU]
          simp

/-- View a matrix as a family of column vectors. -/
def columns (W : Matrix n ι 𝕜) : ι → n → 𝕜 := fun j a => W a j

@[simp] lemma Wmat_one_columns (W : Matrix n ι 𝕜) :
    Wmat (fun _ : ι => (1 : ℝ)) (columns W) = W := by
  ext a j
  simp [Wmat, columns]

/-- Squared norms of the eigen-rotated columns are exactly the Gram eigenvalues. -/
lemma xsq_columns_gramEigenRotateMatrix (W : Matrix n ι 𝕜) (j : ι) :
    xsq (columns (gramEigenRotateMatrix W)) j =
      (Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j := by
  let V := gramEigenRotateMatrix W
  have hdiag := gramEigenRotate_gram_eq_diagonal W
  have hrd := re_gram_diag
    (m := fun _ : ι => (1 : ℝ))
    (fun _ => by norm_num)
    (columns V) j
  rw [Wmat_one_columns] at hrd
  have hj := congrArg (fun M : Matrix ι ι 𝕜 => M j j) hdiag
  change Vᴴ * V = _ at hdiag
  rw [hdiag] at hrd
  simpa [Matrix.diagonal] using hrd.symm

/-- Rotating all columns by the Gram eigenbasis leaves `Pmat` unchanged. -/
lemma Pmat_one_gramEigenRotate_eq (v : ι → n → 𝕜) :
    Pmat (fun _ : ι => (1 : ℝ))
      (columns (gramEigenRotateMatrix (Wmat (fun _ : ι => (1 : ℝ)) v)))
      = Pmat (fun _ : ι => (1 : ℝ)) v := by
  let W := Wmat (fun _ : ι => (1 : ℝ)) v
  unfold Pmat
  rw [Wmat_one_columns]
  exact mul_unitary_mul_conjTranspose_eq W (gramEigenU W)

/-- Six-column specialization: after the Gram eigen-rotation, the exact c=2
charge is bounded by `18 - spectral defect`, while the represented positive
matrix is unchanged.  This is the local algebraic bridge needed by DUT. -/
theorem fin6_rotated_charge_and_P
    (v : Fin 6 → n → 𝕜)
    (htrace : (∑ j, xsq v j) ≤ 6) :
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤
      18 - ∑ j, dutDefect2 (xsq vr j) := by
  dsimp only
  constructor
  · exact Pmat_one_gramEigenRotate_eq v
  · apply sum_kc_two_fin6_le
    -- Unitariy rotation preserves the sum of column squared norms.  Using the
    -- eigenvalue identification plus trace of WᴴW avoids a coordinate proof.
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    have hM : (Wᴴ * W).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self W
    calc
      (∑ j, xsq (columns (gramEigenRotateMatrix W)) j)
          = ∑ j, hM.1.eigenvalues j := by
              apply Finset.sum_congr rfl
              intro j _
              exact xsq_columns_gramEigenRotateMatrix W j
      _ = rtrace (Wᴴ * W) := by
              rw [rtrace_eq_sum_eigenvalues hM.1]
      _ = rtrace (W * Wᴴ) := by
              unfold rtrace
              rw [trace_mul_comm]
      _ = ∑ j, xsq v j := by
              have hp := rtrace_Pmat
                (m := fun _ : Fin 6 => (1 : ℝ))
                (fun _ => by norm_num) v
              simpa [Pmat, W] using hp
      _ ≤ 6 := htrace

end Zeta23.ZeroSide.RankTraceMult
