/-
DUTPhaseCertificate.lean

Global six-phase consequence of the corrected local DUT certificate.

This module is purely finite/combinatorial.  It combines the already checked
DUTPhase telescoping/averaging lemmas with the buffered certificate

  dutCertificateRhs(span) = dutEta * max (dutR - span) 0.

For any monotone ordinate sequence y_0,...,y_{s-1}, the sum of all consecutive
six-window certificate savings is at least

  dutEta * (dutR * (s-5) - 5 * (y_{s-1} - y_0)).

Averaging the six disjoint phase decompositions therefore contributes one sixth
of this total saving to the global counting inequality.

The next module specializes y to the normalized ordinates of the actual
interior-core simple zeros.

Intended location:
  Zeta23/ZeroSide/DUTPhaseCertificate.lean
-/

import Zeta23.ZeroSide.DUTLocalEventually
import Zeta23.ZeroSide.DUTPhase

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

/-- Total corrected DUT certificate saving over all consecutive six-windows of
a monotone real sequence. -/
lemma dut_certificate_sum_all_six_windows
    (y : ℕ → ℝ) {s : ℕ}
    (hs : 6 ≤ s) (hmono : Monotone y) :
    dutEta *
        (dutR * ((s - 5 : ℕ) : ℝ)
          - 5 * (y (s - 1) - y 0))
      ≤
      ∑ i ∈ Finset.range (s - 5),
        dutCertificateRhs (y (i + 5) - y i) := by
  apply
    dut_six_window_saving_lower_of_monotone
      (delta := fun i =>
        dutCertificateRhs (y (i + 5) - y i))
      (y := y)
      (s := s)
      (eta := dutEta)
      (R := dutR)
      hs hmono dutEta_nonneg
  intro i hi
  simp [dutCertificateRhs]

/-- The exact six-phase averaged counting consequence of the corrected
certificate.

`L` denotes the common non-DUT part of each phase inequality and `simple` the
quantity being bounded below. -/
lemma dut_certificate_phase_averaged_counting
    {simple L : ℝ}
    (y : ℕ → ℝ) {s : ℕ}
    (hs : 6 ≤ s) (hmono : Monotone y)
    (hphase :
      ∀ r ∈ Finset.range 6,
        L
          + dutPhaseContribution
              (fun i =>
                dutCertificateRhs (y (i + 5) - y i))
              s r
          ≤ simple) :
    L
      + (dutEta / 6) *
          (dutR * ((s - 5 : ℕ) : ℝ)
            - 5 * (y (s - 1) - y 0))
      ≤ simple := by
  have havg :
      L
        + (1 / 6 : ℝ) *
            (∑ i ∈ Finset.range (s - 5),
              dutCertificateRhs (y (i + 5) - y i))
        ≤ simple := by
    exact
      dut_phase_averaged_counting
        (delta := fun i =>
          dutCertificateRhs (y (i + 5) - y i))
        (s := s)
        hphase

  have hsave :=
    dut_certificate_sum_all_six_windows
      y hs hmono

  have hscale :
      (1 / 6 : ℝ) *
          (dutEta *
            (dutR * ((s - 5 : ℕ) : ℝ)
              - 5 * (y (s - 1) - y 0)))
        ≤
      (1 / 6 : ℝ) *
          (∑ i ∈ Finset.range (s - 5),
            dutCertificateRhs (y (i + 5) - y i)) := by
    exact
      mul_le_mul_of_nonneg_left hsave
        (by norm_num : (0 : ℝ) ≤ 1 / 6)

  have hreassoc :
      (1 / 6 : ℝ) *
          (dutEta *
            (dutR * ((s - 5 : ℕ) : ℝ)
              - 5 * (y (s - 1) - y 0)))
        =
      (dutEta / 6) *
          (dutR * ((s - 5 : ℕ) : ℝ)
            - 5 * (y (s - 1) - y 0)) := by
    ring

  rw [hreassoc] at hscale
  linarith

end Zeta23.ZeroSide.RankTraceMult
