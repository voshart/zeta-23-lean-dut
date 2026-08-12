/-
DUTPhase.lean

Finite six-phase bookkeeping for the Defect-Utilizing Tightening (DUT)
refinement.  This module is deliberately independent of the analytic
Gabor-to-kernel transfer: it formalizes only the exact combinatorics used to
pass from six disjoint phase decompositions to all consecutive six-windows.

Intended location:
  Zeta23/ZeroSide/DUTPhase.lean

Intended dependency:
  Zeta23.ZeroSide.DUTBlockRotation
-/

import Zeta23.ZeroSide.DUTBlockRotation

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

/-- Contribution of the consecutive six-windows whose starting index has
residue `r` modulo six.  With zero-based indexing, valid six-window starts are
`0, ..., s-6`, i.e. `Finset.range (s - 5)`. -/
def dutPhaseContribution (delta : ℕ → ℝ) (s r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (s - 5), if r = i % 6 then delta i else 0

/-- Summing the six phase contributions counts every consecutive six-window
exactly once. -/
lemma dut_phase_partition_sum (delta : ℕ → ℝ) (s : ℕ) :
    (∑ r ∈ Finset.range 6, dutPhaseContribution delta s r)
      = ∑ i ∈ Finset.range (s - 5), delta i := by
  classical
  unfold dutPhaseContribution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hmod : i % 6 ∈ Finset.range 6 := by
    simp only [Finset.mem_range]
    exact Nat.mod_lt _ (by norm_num)
  simpa [hmod] using
    (Finset.sum_ite_eq' (Finset.range 6) (i % 6) (fun _ => delta i))

/-- If every phase separately gives the same counting lower bound with its own
saving, averaging the six inequalities gives coefficient `1/6` on the total
saving. -/
lemma dut_six_phase_average
    {simple L : ℝ} (Delta : ℕ → ℝ)
    (hphase : ∀ r ∈ Finset.range 6, L + Delta r ≤ simple) :
    L + (1 / 6 : ℝ) * (∑ r ∈ Finset.range 6, Delta r) ≤ simple := by
  have hsum :
      (∑ r ∈ Finset.range 6, (L + Delta r))
        ≤ ∑ _r ∈ Finset.range 6, simple :=
    Finset.sum_le_sum hphase
  norm_num [Finset.sum_add_distrib] at hsum
  linarith

/-- The manuscript's six-phase averaging statement, expressed directly in
terms of consecutive six-window savings. -/
lemma dut_phase_averaged_counting
    {simple L : ℝ} (delta : ℕ → ℝ) (s : ℕ)
    (hphase : ∀ r ∈ Finset.range 6,
      L + dutPhaseContribution delta s r ≤ simple) :
    L + (1 / 6 : ℝ) * (∑ i ∈ Finset.range (s - 5), delta i) ≤ simple := by
  have h := dut_six_phase_average
    (Delta := fun r => dutPhaseContribution delta s r) hphase
  rw [dut_phase_partition_sum] at h
  exact h

/-- Exact telescoping identity for the spans of all consecutive six-windows.
For zero-based ordinates `y 0, ..., y (s-1)`, the six-window span starting at
`i` is `y (i+5) - y i`.

This is the zero-based version of
`sum_{i=1}^{s-5} (y_{i+5}-y_i)
 = sum_{j=s-4}^s y_j - sum_{j=1}^5 y_j`. -/
lemma sum_six_spans_eq_edges
    (y : ℕ → ℝ) {s : ℕ} (hs : 5 ≤ s) :
    (∑ i ∈ Finset.range (s - 5), (y (i + 5) - y i))
      = (∑ j ∈ Finset.Ico (s - 5) s, y j)
          - ∑ j ∈ Finset.range 5, y j := by
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ i ∈ Finset.range (s - 5), y (i + 5))
        = ∑ j ∈ Finset.Ico 5 s, y j := by
    symm
    rw [Finset.sum_Ico_eq_sum_range y 5 s]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  rw [hshift]
  rw [Finset.sum_Ico_eq_sub y hs]
  rw [Finset.sum_Ico_eq_sub y (Nat.sub_le s 5)]
  ring

/-- For an increasing sequence of ordinates, the sum of all consecutive
six-window spans is at most five times the full interval length. -/
lemma sum_six_spans_le_five_total
    (y : ℕ → ℝ) {s : ℕ} (hs : 6 ≤ s) (hmono : Monotone y) :
    (∑ i ∈ Finset.range (s - 5), (y (i + 5) - y i))
      ≤ 5 * (y (s - 1) - y 0) := by
  have hs5 : 5 ≤ s := by omega
  rw [sum_six_spans_eq_edges y hs5]

  have hlast :
      (∑ j ∈ Finset.Ico (s - 5) s, y j) ≤ 5 * y (s - 1) := by
    calc
      (∑ j ∈ Finset.Ico (s - 5) s, y j)
          ≤ ∑ _j ∈ Finset.Ico (s - 5) s, y (s - 1) := by
              apply Finset.sum_le_sum
              intro j hj
              have hjlt : j < s := (Finset.mem_Ico.mp hj).2
              exact hmono (by omega)
      _ = 5 * y (s - 1) := by
              have hcard : (Finset.Ico (s - 5) s).card = 5 := by
                simp only [Nat.card_Ico]
                omega
              rw [Finset.sum_const, hcard]
              norm_num

  have hfirst :
      5 * y 0 ≤ ∑ j ∈ Finset.range 5, y j := by
    calc
      5 * y 0 = ∑ _j ∈ Finset.range 5, y 0 := by norm_num
      _ ≤ ∑ j ∈ Finset.range 5, y j := by
            apply Finset.sum_le_sum
            intro j hj
            exact hmono (Nat.zero_le j)

  linarith

/-- A local certificate of the form
`delta_i >= eta * (R - span_i)_+`, together with the five-endpoint span bound,
gives an exact finite lower bound for the total saving.  No Jensen theorem is
needed: `(R-S)_+ >= R-S` pointwise. -/
lemma dut_window_saving_sum_lower
    (delta span : ℕ → ℝ) (s : ℕ) {eta R length : ℝ}
    (heta : 0 ≤ eta)
    (hlocal : ∀ i ∈ Finset.range (s - 5),
      eta * max (R - span i) 0 ≤ delta i)
    (hspan : (∑ i ∈ Finset.range (s - 5), span i) ≤ 5 * length) :
    eta * (R * ((s - 5 : ℕ) : ℝ) - 5 * length)
      ≤ ∑ i ∈ Finset.range (s - 5), delta i := by
  have hpoint : ∀ i ∈ Finset.range (s - 5),
      eta * (R - span i) ≤ delta i := by
    intro i hi
    calc
      eta * (R - span i)
          ≤ eta * max (R - span i) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) heta
      _ ≤ delta i := hlocal i hi

  have hsum :
      (∑ i ∈ Finset.range (s - 5), eta * (R - span i))
        ≤ ∑ i ∈ Finset.range (s - 5), delta i :=
    Finset.sum_le_sum hpoint

  have hsum' :
      eta * (R * ((s - 5 : ℕ) : ℝ)
        - ∑ i ∈ Finset.range (s - 5), span i)
        ≤ ∑ i ∈ Finset.range (s - 5), delta i := by
    calc
      eta * (R * ((s - 5 : ℕ) : ℝ)
          - ∑ i ∈ Finset.range (s - 5), span i)
          = eta * (∑ i ∈ Finset.range (s - 5), (R - span i)) := by
              congr 1
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      _ = ∑ i ∈ Finset.range (s - 5), eta * (R - span i) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (s - 5), delta i := hsum

  have hbase :
      R * ((s - 5 : ℕ) : ℝ) - 5 * length
        ≤ R * ((s - 5 : ℕ) : ℝ)
            - ∑ i ∈ Finset.range (s - 5), span i := by
    exact sub_le_sub_left hspan _
  exact (mul_le_mul_of_nonneg_left hbase heta).trans hsum'

/-- Specialization to actual six-window spans of an increasing sequence. -/
lemma dut_six_window_saving_lower_of_monotone
    (delta : ℕ → ℝ) (y : ℕ → ℝ) {s : ℕ} {eta R : ℝ}
    (hs : 6 ≤ s) (hmono : Monotone y) (heta : 0 ≤ eta)
    (hlocal : ∀ i ∈ Finset.range (s - 5),
      eta * max (R - (y (i + 5) - y i)) 0 ≤ delta i) :
    eta * (R * ((s - 5 : ℕ) : ℝ) - 5 * (y (s - 1) - y 0))
      ≤ ∑ i ∈ Finset.range (s - 5), delta i := by
  apply dut_window_saving_sum_lower
    (delta := delta)
    (span := fun i => y (i + 5) - y i)
    (s := s)
    (eta := eta)
    (R := R)
    (length := y (s - 1) - y 0)
    heta
    hlocal
  exact sum_six_spans_le_five_total y hs hmono

end Zeta23.ZeroSide.RankTraceMult
