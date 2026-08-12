/-
DUTTailSeries.lean

Elementary reciprocal-series bounds used by the DUT finite-grid truncation.

The goal is to avoid any dependence on the exact value zeta(2).  Mathlib
already proves:
  * summability of the p-series for exponent 2;
  * finite inverse-square interval estimates.

From these we derive the deliberately loose but convenient bound

  sum' n, 1 / (n+1)^2 <= 2.

We then use the elementary inequality

  (m+n)^4 >= m^2 (n+1)^2    (m >= 1)

to obtain

  sum' n, 1 / (m+n)^4 <= 2 / m^2.

This is strong enough for the DUT grid tail: after taking
m ~ distance / hgrid, the resulting bound is O(hgrid^-2 distance^-2),
which still tends to zero on the sqrt(T) interior core.

Intended location:
  Zeta23/ZeroSide/DUTTailSeries.lean
-/

import Zeta23.ZeroSide.DUTTailPointwise
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Classical

/-- The shifted inverse-square series is summable. -/
lemma dut_summable_inv_sq_succ :
    Summable (fun n : ℕ => 1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
  have h :=
    summable_pow_div_add (1 : ℝ) 2 1 (by omega)
  simpa [Real.norm_eq_abs, abs_of_nonneg, one_div] using h

/-- A deliberately loose rational upper bound for the shifted inverse-square
series.  We only need a simple certified constant, not `π^2 / 6`. -/
lemma dut_tsum_inv_sq_succ_le_two :
    (∑' n : ℕ, 1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) ≤ 2 := by
  apply dut_summable_inv_sq_succ.tsum_le_of_sum_range_le
  intro N
  have h :=
    sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
  have hset :
      Finset.Ioo 0 (N + 1) = Finset.Ico 1 (N + 1) := by
    ext k
    simp
    omega
  rw [hset] at h
  rw [Finset.sum_Ico_eq_sum_range
      (fun k : ℕ => (((k : ℝ) ^ 2)⁻¹)) 1 (N + 1)] at h
  simpa [one_div, add_comm, add_left_comm, add_assoc] using h

/-- Pointwise comparison turning a fourth-power shifted tail into the universal
shifted inverse-square majorant. -/
lemma dut_inv_four_add_le_inv_sq_majorant
    {m n : ℕ} (hm : 1 ≤ m) :
    1 / ((((m + n : ℕ) : ℝ)) ^ 4)
      ≤ (1 / (((m : ℝ) ^ 2))) *
          (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hmn_pos : 0 < ((m + n : ℕ) : ℝ) := by positivity
  have hm_pos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmR
  have hnp_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity

  have h1 : (m : ℝ) ≤ (m + n : ℕ) := by
    norm_num
  have h2 : ((n + 1 : ℕ) : ℝ) ≤ (m + n : ℕ) := by
    exact_mod_cast (by omega : n + 1 ≤ m + n)

  have hsq1 : (m : ℝ) ^ 2 ≤ (((m + n : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  have hsq2 : (((n + 1 : ℕ) : ℝ)) ^ 2 ≤ (((m + n : ℕ) : ℝ)) ^ 2 := by
    nlinarith

  have hprod :
      (m : ℝ) ^ 2 * (((n + 1 : ℕ) : ℝ)) ^ 2
        ≤ (((m + n : ℕ) : ℝ)) ^ 4 := by
    have hmul :=
      mul_le_mul hsq1 hsq2 (sq_nonneg _) (sq_nonneg _)
    nlinarith

  have hden_left :
      0 < (m : ℝ) ^ 2 * (((n + 1 : ℕ) : ℝ)) ^ 2 := by positivity

  calc
    1 / ((((m + n : ℕ) : ℝ)) ^ 4)
        ≤ 1 / ((m : ℝ) ^ 2 * (((n + 1 : ℕ) : ℝ)) ^ 2) :=
      one_div_le_one_div_of_le hden_left hprod
    _ =
        (1 / ((m : ℝ) ^ 2)) *
          (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
      field_simp [ne_of_gt hm_pos, ne_of_gt hnp_pos]

/-- The fourth-power tail beginning at an integer `m >= 1` is at most
`2 / m^2`.  This coarse estimate is enough for the later `sqrt(T)` core. -/
lemma dut_tsum_inv_four_nat_add_le
    {m : ℕ} (hm : 1 ≤ m) :
    (∑' n : ℕ, 1 / ((((m + n : ℕ) : ℝ)) ^ 4))
      ≤ 2 / (m : ℝ) ^ 2 := by
  have hmaj :
      ∀ n : ℕ,
        1 / ((((m + n : ℕ) : ℝ)) ^ 4)
          ≤ (1 / ((m : ℝ) ^ 2)) *
              (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) :=
    fun n => dut_inv_four_add_le_inv_sq_majorant (m := m) (n := n) hm

  have hsmaj :
      Summable
        (fun n : ℕ =>
          (1 / ((m : ℝ) ^ 2)) *
            (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2))) :=
    dut_summable_inv_sq_succ.mul_left _

  have hsum :=
    Summable.tsum_le_tsum
      hmaj
      (Summable.of_nonneg_of_le
        (fun n => by positivity)
        hmaj
        hsmaj)
      hsmaj

  calc
    (∑' n : ℕ, 1 / ((((m + n : ℕ) : ℝ)) ^ 4))
        ≤ ∑' n : ℕ,
            (1 / ((m : ℝ) ^ 2)) *
              (1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := hsum
    _ = (1 / ((m : ℝ) ^ 2)) *
          (∑' n : ℕ, 1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
      rw [tsum_mul_left]
    _ ≤ (1 / ((m : ℝ) ^ 2)) * 2 := by
      exact
        mul_le_mul_of_nonneg_left
          dut_tsum_inv_sq_succ_le_two
          (by positivity)
    _ = 2 / (m : ℝ) ^ 2 := by ring

end Zeta23.ZeroSide.RankTraceMult
