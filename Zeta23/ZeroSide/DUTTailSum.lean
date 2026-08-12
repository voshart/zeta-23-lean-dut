/-
DUTTailSum.lean

Summed omitted-grid Fourier tails for interior-core DUT six-zero blocks.

This is the first module that produces an actual quantitative truncation
estimate rather than pointwise decay.

Using:
  * `DUTTailPointwise`: |phiHatR(r)| <= C / distance^2;
  * `DUTTailLattice`:   sum' 1/(D+(n+1)h)^4 <= 2/(D^2 h^2);

we prove, for every actual interior-core simple zero in a six-block,

  left tail  <= 2 C^2 / (D0(T)^2 h^2),

and, under `D0(T) > 2h`,

  right tail <= 2 C^2 / ((D0(T)-2h)^2 h^2),

where C = cDT / w and h = hgrid.

These are UNNORMALIZED sums of squares of the real Fourier samples.
The next module will use Cauchy--Schwarz to turn these scalar norm tails into
entrywise Gram truncation error.

Intended location:
  Zeta23/ZeroSide/DUTTailSum.lean
-/

import Zeta23.ZeroSide.DUTTailLattice

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Squaring a nonnegative reciprocal-square majorant gives the corresponding
scaled reciprocal-fourth-power majorant. -/
private lemma dut_sq_le_scaled_inv_four
    {x A q : ℝ}
    (hA : 0 ≤ A) (hq : 0 < q)
    (habs : |x| ≤ A / q ^ 2) :
    x ^ 2 ≤ A ^ 2 * (1 / q ^ 4) := by
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hrhs : 0 ≤ A / q ^ 2 := div_nonneg hA hq2.le
  have hprod :
      0 ≤ (A / q ^ 2 - |x|) * (A / q ^ 2 + |x|) :=
    mul_nonneg (sub_nonneg.mpr habs) (add_nonneg hrhs (abs_nonneg x))
  have hsqabs : |x| ^ 2 ≤ (A / q ^ 2) ^ 2 := by
    nlinarith
  calc
    x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ (A / q ^ 2) ^ 2 := hsqabs
    _ = A ^ 2 * (1 / q ^ 4) := by
      field_simp [hq.ne']

/-- The affine reciprocal-fourth-power majorant is summable. -/
lemma dut_summable_inv_four_affine
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    Summable (fun n : ℕ =>
      1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4) := by
  have hmaj :
      ∀ n : ℕ,
        1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4
          ≤ (1 / (D ^ 2 * h ^ 2)) *
              (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) :=
    dut_inv_four_affine_le_inv_sq_majorant hD hh
  have hsmaj :
      Summable
        (fun n : ℕ =>
          (1 / (D ^ 2 * h ^ 2)) *
            (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2))) :=
    dut_summable_inv_sq_succ.mul_left _
  exact
    Summable.of_nonneg_of_le
      (fun n => by positivity)
      hmaj
      hsmaj

/-- Generic summed-square consequence of a pointwise affine distance bound. -/
private lemma dut_tsum_sq_of_affine_distance
    {f : ℕ → ℝ} {A D h : ℝ}
    (hA : 0 ≤ A) (hD : 0 < D) (hh : 0 < h)
    (hf :
      ∀ n : ℕ,
        |f n| ≤ A / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 2) :
    (∑' n : ℕ, (f n) ^ 2)
      ≤ 2 * A ^ 2 / (D ^ 2 * h ^ 2) := by
  let g : ℕ → ℝ :=
    fun n => 1 / (D + ((n + 1 : ℕ) : ℝ) * h) ^ 4

  have hpoint :
      ∀ n : ℕ, (f n) ^ 2 ≤ A ^ 2 * g n := by
    intro n
    have hq :
        0 < D + ((n + 1 : ℕ) : ℝ) * h := by
      have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      positivity
    exact dut_sq_le_scaled_inv_four hA hq (hf n)

  have hsg : Summable g := by
    dsimp [g]
    exact dut_summable_inv_four_affine hD hh

  have hsmaj : Summable (fun n => A ^ 2 * g n) :=
    hsg.mul_left _

  have hsf : Summable (fun n => (f n) ^ 2) :=
    Summable.of_nonneg_of_le
      (fun n => sq_nonneg (f n))
      hpoint
      hsmaj

  have hsum :=
    Summable.tsum_le_tsum hpoint hsf hsmaj

  calc
    (∑' n : ℕ, (f n) ^ 2)
        ≤ ∑' n : ℕ, A ^ 2 * g n := hsum
    _ = A ^ 2 * (∑' n : ℕ, g n) := by
      rw [tsum_mul_left]
    _ ≤ A ^ 2 * (2 / (D ^ 2 * h ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · dsimp [g]
        exact dut_tsum_inv_four_affine_le hD hh
      · exact sq_nonneg A
    _ = 2 * A ^ 2 / (D ^ 2 * h ^ 2) := by
      ring

/-- The concrete Theorem-D decay constant divided by the ramp width. -/
noncomputable def dutDTailConst (P : Params) : ℝ :=
  ThmD.cDT P.ϱ P.lam / P.w

lemma dutDTailConst_nonneg
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    0 ≤ dutDTailConst P := by
  have hW := ThmD.admWindow_params hP h8
  unfold dutDTailConst
  exact div_nonneg hW.c_nonneg hW.w_pos.le

/-- **Summed left omitted-grid tail.**

For an interior-core zero, the omitted samples `k=-1,-2,...` have total
squared Fourier mass bounded explicitly by
`2 C^2 / (D0(T)^2 h^2)`. -/
theorem dutCoreSix_phiHatR_left_sq_tsum_le
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T) (h8 : 8 * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    (∑' n : ℕ,
      ((P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutLeftTailIndex n))) ^ 2)
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

  apply dut_tsum_sq_of_affine_distance hA hD hh
  intro n

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
      dutCoreSix_left_progressive_distance
        Z T P hL i hi j n

  simpa [dutDTailConst, q] using
    dutD_phiHatR_le_of_distance
      P hP h8 hq hdist

/-- **Summed right omitted-grid tail.**

If the interior width dominates two grid steps, then the omitted samples
`k=d,d+1,...` have total squared Fourier mass bounded by the same affine-tail
formula with effective starting distance `D0(T)-2h`.

The slightly stronger `D0 > 2h` hypothesis lets the right progression fit
the exact `(D+(n+1)h)` form used by `DUTTailLattice`. -/
theorem dutCoreSix_phiHatR_right_sq_tsum_le
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 ≤ T) (h8 : 8 * P.w ≤ P.L T)
    (hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    (∑' n : ℕ,
      ((P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutRightTailIndex P T n))) ^ 2)
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

  apply dut_tsum_sq_of_affine_distance hA hgap2 hh
  intro n

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
    dutD_phiHatR_le_of_distance
      P hP h8 hq hdist

end Zeta23.ZeroSide.RankTraceMult
