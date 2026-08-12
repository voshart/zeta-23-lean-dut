/-
DUTTailProduct.lean

Absolute product-tail bounds for interior-core DUT six-zero blocks.

Because both Fourier samples in a Gram entry satisfy the same pointwise
r^{-2} estimate, their product is directly bounded by an r^{-4} majorant.
This avoids introducing a separate Cauchy--Schwarz theorem.

For the omitted left lattice:
  |sum' phi_j phi_l|
    <= 2 C^2 / (D0(T)^2 h^2).

For the omitted right lattice, assuming D0(T) > 2h:
  |sum' phi_j phi_l|
    <= 2 C^2 / ((D0(T)-2h)^2 h^2).

Here C = cDT / w and h = hgrid.

Intended location:
  Zeta23/ZeroSide/DUTTailProduct.lean
-/

import Zeta23.ZeroSide.DUTTailSum
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Generic absolute product-tail estimate from a common affine `r^-2`
pointwise majorant. -/
private lemma dut_abs_tsum_product_of_affine_distance
    {f g : ℕ → ℝ} {A D h : ℝ}
    (hA : 0 ≤ A) (hD : 0 < D) (hh : 0 < h)
    (hf :
      ∀ n : ℕ,
        |f n| ≤ A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2)
    (hg :
      ∀ n : ℕ,
        |g n| ≤ A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2) :
    |∑' n : ℕ, f n * g n|
      ≤ 2 * A ^ 2 / (D ^ 2 * h ^ 2) := by
  let b : ℕ → ℝ :=
    fun n => 1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4

  have hsb : Summable b := by
    dsimp [b]
    exact dut_summable_inv_four_affine hD hh

  have hmajor :
      ∀ n : ℕ, ‖f n * g n‖ ≤ A ^ 2 * b n := by
    intro n
    have hq :
        0 < D + ((n + 1 : ℕ) : ℝ) * h := by
      have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      positivity
    have hf' := hf n
    have hg' := hg n
    have hB :
        0 ≤ A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2 := by
      exact div_nonneg hA (sq_nonneg _)
    have hprod :
        |f n| * |g n|
          ≤ (A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2)
              * (A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2) := by
      exact mul_le_mul hf' hg' (abs_nonneg _) hB
    calc
      ‖f n * g n‖ = |f n| * |g n| := by
        simp [Real.norm_eq_abs]
      _ ≤ (A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2)
            * (A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2) := hprod
      _ = A ^ 2 * b n := by
        dsimp [b]
        field_simp [hq.ne']

  have hsmajor : Summable (fun n => A ^ 2 * b n) :=
    hsb.mul_left _

  have hbound :
      |∑' n : ℕ, f n * g n|
        ≤ A ^ 2 * (∑' n : ℕ, b n) := by
    have hHas :
        HasSum (fun n : ℕ => A ^ 2 * b n)
          (A ^ 2 * (∑' n : ℕ, b n)) := by
      simpa using hsb.hasSum.mul_left (A ^ 2)
    simpa [Real.norm_eq_abs] using
      (tsum_of_norm_bounded hHas hmajor)

  calc
    |∑' n : ℕ, f n * g n|
        ≤ A ^ 2 * (∑' n : ℕ, b n) := hbound
    _ ≤ A ^ 2 * (2 / (D ^ 2 * h ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · dsimp [b]
        exact dut_tsum_inv_four_affine_le hD hh
      · exact sq_nonneg A
    _ = 2 * A ^ 2 / (D ^ 2 * h ^ 2) := by
      ring

/-- **Absolute left omitted-grid Gram-product tail.** -/
theorem dutCoreSix_phiHatR_left_product_tsum_abs_le
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T) (h8 : 8 * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    |∑' n : ℕ,
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutLeftTailIndex n))
      *
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutLeftTailIndex n))|
      ≤
      2 * (dutDTailConst P) ^ 2 /
        ((D0 T) ^ 2 * ((P.atD T).hgrid T) ^ 2) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hh : 0 < (P.atD T).hgrid T := by
    have hhP : 0 < P.hgrid T := by
      unfold Params.hgrid
      positivity
    simpa using hhP
  have hD : 0 < D0 T := Real.sqrt_pos.2 hT
  have hA : 0 ≤ dutDTailConst P :=
    dutDTailConst_nonneg P hP h8

  apply dut_abs_tsum_product_of_affine_distance hA hD hh
  · intro n
    let q : ℝ :=
      D0 T + ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hdist :
        q ≤
          |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutLeftTailIndex n)| := by
      simpa [q] using
        dutCoreSix_left_progressive_distance Z T P hL i hi j n
    simpa [dutDTailConst, q] using
      dutD_phiHatR_le_of_distance P hP h8 hq hdist
  · intro n
    let q : ℝ :=
      D0 T + ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hdist :
        q ≤
          |((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutLeftTailIndex n)| := by
      simpa [q] using
        dutCoreSix_left_progressive_distance Z T P hL i hi l n
    simpa [dutDTailConst, q] using
      dutD_phiHatR_le_of_distance P hP h8 hq hdist

/-- **Absolute right omitted-grid Gram-product tail.** -/
theorem dutCoreSix_phiHatR_right_product_tsum_abs_le
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 ≤ T) (h8 : 8 * P.w ≤ P.L T)
    (hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    |∑' n : ℕ,
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutRightTailIndex P T n))
      *
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutRightTailIndex P T n))|
      ≤
      2 * (dutDTailConst P) ^ 2 /
        ((D0 T - 2 * (P.atD T).hgrid T) ^ 2
          * ((P.atD T).hgrid T) ^ 2) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hh : 0 < (P.atD T).hgrid T := by
    have hhP : 0 < P.hgrid T := by
      unfold Params.hgrid
      positivity
    simpa using hhP
  have hA : 0 ≤ dutDTailConst P :=
    dutDTailConst_nonneg P hP h8

  apply dut_abs_tsum_product_of_affine_distance hA hgap2 hh
  · intro n
    let D : ℝ :=
      D0 T - 2 * (P.atD T).hgrid T
    let q : ℝ :=
      D + ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hq_eq :
        q =
          (D0 T - (P.atD T).hgrid T)
            + (n : ℝ) * (P.atD T).hgrid T := by
      dsimp [q, D]
      push_cast
      ring
    have hdist :
        q ≤
          |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutRightTailIndex P T n)| := by
      rw [hq_eq]
      exact
        dutCoreSix_right_progressive_distance
          Z T P hT hL i hi j n
    simpa [dutDTailConst, q, D] using
      dutD_phiHatR_le_of_distance P hP h8 hq hdist
  · intro n
    let D : ℝ :=
      D0 T - 2 * (P.atD T).hgrid T
    let q : ℝ :=
      D + ((n + 1 : ℕ) : ℝ) * (P.atD T).hgrid T
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hq_eq :
        q =
          (D0 T - (P.atD T).hgrid T)
            + (n : ℝ) * (P.atD T).hgrid T := by
      dsimp [q, D]
      push_cast
      ring
    have hdist :
        q ≤
          |((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutRightTailIndex P T n)| := by
      rw [hq_eq]
      exact
        dutCoreSix_right_progressive_distance
          Z T P hT hL i hi l n
    simpa [dutDTailConst, q, D] using
      dutD_phiHatR_le_of_distance P hP h8 hq hdist

end Zeta23.ZeroSide.RankTraceMult
