/-
DUTMatrixTransfer.lean

Matrix-level transfer from the entrywise sharp-kernel estimate proved in
DUTCoreGramBridge.

For the actual 6x6 core Gram matrix A and the ideal sharp matrix K, if every
entry satisfies

    ‖A_ij - K_ij‖ ≤ δ,

and every sharp entry satisfies ‖K_ij‖ ≤ 9/2, then

    |rtrace A - rtrace K| ≤ 6 δ,

    |frobSq A - frobSq K| ≤ 36 δ (9 + δ).

The constants are intentionally loose.  Since the previously proved
δ = normalized-tail-budget + 40 w / L tends to zero, these bounds are fully
adequate for the eventual-in-T DUT transfer.

Intended location:
  Zeta23/ZeroSide/DUTMatrixTransfer.lean
-/

import Zeta23.ZeroSide.DUTCoreGramBridge
import Zeta23.ZeroSide.DUTEnergyTransfer

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Ideal 6x6 sharp-cosine matrix on the actual six core ordinates. -/
noncomputable def dutCoreSixSharpMatrix
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  fun j l =>
    (dutDSharpKernel P T
      (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im) : ℂ)

/-- Uniform scalar error budget from actual finite Gram entry to sharp kernel. -/
noncomputable def dutCoreSixEntryError
    (T : ℝ) (P : Params) : ℝ :=
  dutCoreSixNormalizedTailBudget T P + 40 * P.w / P.L T

lemma dutCoreSixGram_entry_close_sharpMatrix
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 : 0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    ‖dutCoreSixGramMatrixD Z T P i hi j l
        - dutCoreSixSharpMatrix Z T P i hi j l‖
      ≤ dutCoreSixEntryError T P := by
  simpa [dutCoreSixSharpMatrix, dutCoreSixEntryError] using
    dutCoreSixGramMatrixD_entry_close_sharp
      Z T P hP hT h16 h4pi hgap2 i hi j l

/-- The normalized sharp kernel is uniformly bounded by `9/2`. -/
lemma dutDSharpKernel_abs_le_nine_halves
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (x : ℝ) :
    |dutDSharpKernel P T x| ≤ 9 / 2 := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have haStar :
      1 / 4 ≤ ThmD.aStar P.lam :=
    dutD_aStar_ge_quarter P hP h16 h4pi
  have hden :
      P.L T / 4 ≤ ThmD.aStar P.lam * P.L T := by
    have h :=
      mul_le_mul_of_nonneg_right haStar hL.le
    nlinarith
  have hdenpos :
      0 < ThmD.aStar P.lam * P.L T := by
    have : 0 < P.L T / 4 := by positivity
    linarith
  have hraw :=
    dutDSharpKernelRaw_abs_le P hP h16 x
  unfold dutDSharpKernel
  rw [abs_div, abs_of_pos hdenpos]
  rw [div_le_iff₀ hdenpos]
  have h1 := mul_le_mul_of_nonneg_right hraw hdenpos.le
  have h2 := mul_le_mul_of_nonneg_left hden (by norm_num : 0 ≤ (9 : ℝ) / 2)
  nlinarith

lemma dutCoreSixSharpMatrix_entry_norm_le
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    ‖dutCoreSixSharpMatrix Z T P i hi j l‖ ≤ 9 / 2 := by
  unfold dutCoreSixSharpMatrix
  simpa [Complex.norm_real, Real.norm_eq_abs] using
    dutDSharpKernel_abs_le_nine_halves
      P hP h16 h4pi
      (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)

/-- Squared Frobenius norm as the sum of squared entry norms. -/
private lemma dut_frobSq_eq_sum_norm_sq
    (A : Matrix (Fin 6) (Fin 6) ℂ) :
    frobSq A = ∑ i : Fin 6, ∑ j : Fin 6, ‖A j i‖ ^ 2 := by
  unfold frobSq
  change
    Complex.reCLM
      (∑ i : Fin 6, (Aᴴ * A) i i)
      =
      ∑ i : Fin 6, ∑ j : Fin 6, ‖A j i‖ ^ 2
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.reCLM_apply, Matrix.conjTranspose_apply]
  rw [RCLike.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_re (‖A j i‖ ^ 2)

/-- Generic 6x6 real-trace perturbation from a uniform entrywise norm bound. -/
private lemma dut_abs_rtrace_sub_le
    (A K : Matrix (Fin 6) (Fin 6) ℂ)
    {δ : ℝ}
    (hentry : ∀ i j, ‖A i j - K i j‖ ≤ δ) :
    |rtrace A - rtrace K| ≤ 6 * δ := by
  rw [← rtrace_sub]
  unfold rtrace
  change
    |∑ i : Fin 6, (A i i - K i i).re| ≤ 6 * δ
  calc
    |∑ i : Fin 6, (A i i - K i i).re|
        ≤ ∑ i : Fin 6, |(A i i - K i i).re| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun i : Fin 6 => (A i i - K i i).re)
              Finset.univ)
    _ ≤ ∑ i : Fin 6, ‖A i i - K i i‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact Complex.abs_re_le_norm _
    _ ≤ ∑ _i : Fin 6, δ := by
          apply Finset.sum_le_sum
          intro i hi
          exact hentry i i
    _ = 6 * δ := by
          simp

/-- Generic 6x6 Frobenius-square perturbation from a uniform entrywise error
and a uniform bound on the comparison matrix. -/
private lemma dut_abs_frobSq_sub_le
    (A K : Matrix (Fin 6) (Fin 6) ℂ)
    {δ B : ℝ}
    (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hentry : ∀ i j, ‖A i j - K i j‖ ≤ δ)
    (hK : ∀ i j, ‖K i j‖ ≤ B) :
    |frobSq A - frobSq K| ≤ 36 * δ * (2 * B + δ) := by
  rw [dut_frobSq_eq_sum_norm_sq, dut_frobSq_eq_sum_norm_sq]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin 6, ∑ j : Fin 6,
        (‖A j i‖ ^ 2 - ‖K j i‖ ^ 2)|
      ≤ ∑ i : Fin 6, |∑ j : Fin 6,
          (‖A j i‖ ^ 2 - ‖K j i‖ ^ 2)| := by
        exact
          Finset.abs_sum_le_sum_abs
            (fun i : Fin 6 =>
              ∑ j : Fin 6, (‖A j i‖ ^ 2 - ‖K j i‖ ^ 2))
            Finset.univ
    _ ≤ ∑ i : Fin 6, ∑ j : Fin 6,
          |‖A j i‖ ^ 2 - ‖K j i‖ ^ 2| := by
        apply Finset.sum_le_sum
        intro i hi
        exact
          Finset.abs_sum_le_sum_abs
            (fun j : Fin 6 => ‖A j i‖ ^ 2 - ‖K j i‖ ^ 2)
            Finset.univ
    _ ≤ ∑ i : Fin 6, ∑ _j : Fin 6,
          δ * (2 * B + δ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hdiff :
            |‖A j i‖ - ‖K j i‖| ≤ δ := by
          exact
            (abs_norm_sub_norm_le (A j i) (K j i)).trans
              (hentry j i)
        have hAnorm :
            ‖A j i‖ ≤ B + δ := by
          calc
            ‖A j i‖
                ≤ ‖A j i - K j i‖ + ‖K j i‖ := by
                  have h :=
                    norm_add_le (A j i - K j i) (K j i)
                  simpa using h
            _ ≤ δ + B := add_le_add (hentry j i) (hK j i)
            _ = B + δ := by ring
        have hsum :
            ‖A j i‖ + ‖K j i‖ ≤ 2 * B + δ := by
          linarith [hK j i]
        have hsum_nonneg :
            0 ≤ ‖A j i‖ + ‖K j i‖ := by positivity
        have hR_nonneg : 0 ≤ 2 * B + δ := by
          linarith
        rw [sq_sub_sq, abs_mul, abs_of_nonneg hsum_nonneg]
        calc
          (‖A j i‖ + ‖K j i‖) *
              |‖A j i‖ - ‖K j i‖|
              ≤ (‖A j i‖ + ‖K j i‖) * δ :=
            mul_le_mul_of_nonneg_left hdiff hsum_nonneg
          _ ≤ (2 * B + δ) * δ :=
            mul_le_mul_of_nonneg_right hsum hδ
          _ = δ * (2 * B + δ) := by ring
    _ = 36 * δ * (2 * B + δ) := by
        simp
        ring

/-- **Matrix-level truncation/kernel transfer.** -/
theorem dutCoreSix_matrix_transfer
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 : 0 < D0 T - 2 * (P.atD T).hgrid T)
    (hδ : 0 ≤ dutCoreSixEntryError T P)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    |frobSq (dutCoreSixGramMatrixD Z T P i hi)
        - frobSq (dutCoreSixSharpMatrix Z T P i hi)|
      ≤
      36 * dutCoreSixEntryError T P *
        (9 + dutCoreSixEntryError T P)
    ∧
    |rtrace (dutCoreSixGramMatrixD Z T P i hi)
        - rtrace (dutCoreSixSharpMatrix Z T P i hi)|
      ≤ 6 * dutCoreSixEntryError T P := by
  have hentry :
      ∀ j l,
        ‖dutCoreSixGramMatrixD Z T P i hi j l
          - dutCoreSixSharpMatrix Z T P i hi j l‖
          ≤ dutCoreSixEntryError T P :=
    dutCoreSixGram_entry_close_sharpMatrix
      Z T P hP hT h16 h4pi hgap2 i hi
  have hK :
      ∀ j l, ‖dutCoreSixSharpMatrix Z T P i hi j l‖ ≤ 9 / 2 :=
    dutCoreSixSharpMatrix_entry_norm_le
      Z T P hP h16 h4pi i hi
  constructor
  · have h :=
      dut_abs_frobSq_sub_le
        (dutCoreSixGramMatrixD Z T P i hi)
        (dutCoreSixSharpMatrix Z T P i hi)
        hδ (by norm_num : 0 ≤ (9 : ℝ) / 2)
        hentry hK
    norm_num at h ⊢
    exact h
  · exact
      dut_abs_rtrace_sub_le
        (dutCoreSixGramMatrixD Z T P i hi)
        (dutCoreSixSharpMatrix Z T P i hi)
        hentry

/-- Direct energy-transfer corollary using the matrix-level bounds above. -/
theorem dutCoreSix_energy_transfer_from_sharp
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 : 0 < D0 T - 2 * (P.atD T).hgrid T)
    (hδ : 0 ≤ dutCoreSixEntryError T P)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    dutGramEnergy (dutCoreSixSharpMatrix Z T P i hi)
      -
      (36 * dutCoreSixEntryError T P *
          (9 + dutCoreSixEntryError T P)
        + 12 * dutCoreSixEntryError T P)
      ≤
      dutGramEnergy (dutCoreSixGramMatrixD Z T P i hi) := by
  rcases
    dutCoreSix_matrix_transfer
      Z T P hP hT h16 h4pi hgap2 hδ i hi
    with ⟨hfrob, htrace⟩
  have h :=
    dutGramEnergy_transfer_lower
      (dutCoreSixGramMatrixD Z T P i hi)
      (dutCoreSixSharpMatrix Z T P i hi)
      hfrob htrace
  convert h using 1 <;> ring

end Zeta23.ZeroSide.RankTraceMult
