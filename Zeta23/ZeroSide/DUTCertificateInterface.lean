/-
DUTCertificateInterface.lean

Lean-side interface for the corrected Theorem-D DUT six-point certificate with a buffered cutoff.

The interval/integer verifier is an external computer-assisted input.  This
module does NOT formalize that computation.  Instead it proves the exact
spectral implication consumed by the Lean proof:

  verifier-certified six-point quadratic energy
      >= eta * (R_verifier - span)_+

implies the same lower bound for both the c=2 and c=3 DUT spectral defects.

The key observation is that eta*R < 1.  If every eigenvalue is below the
relevant charge cutoff, the defect equals (lambda-1)^2 termwise.  If an
eigenvalue crosses the cutoff, one defect term alone is already >= 1, which is
larger than the entire certified right-hand side.

Intended location:
  Zeta23/ZeroSide/DUTCertificateInterface.lean
-/

import Zeta23.ZeroSide.DUTCharge3

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

/-- Certified slope in the corrected Theorem-D DUT six-point inequality. -/
def dutEta : ℝ := 27 / 20000

/-- Cutoff actually certified by the external interval/integer verifier. -/
def dutVerifierR : ℝ := 189 / 20

/-- Slightly buffered cutoff consumed by the Lean endgame.

Using `9.40` instead of the verifier's `9.45` creates a fixed positive margin
that can absorb the finite-grid/sharp transfer loss while changing the final
percentage only negligibly. -/
def dutR : ℝ := 47 / 5

/-- Fixed transfer budget created by the `9.45 -> 9.40` cutoff buffer. -/
def dutCertificateTransferSlack : ℝ := 27 / 400000

/-- The local lower bound consumed by the Lean proof. -/
def dutCertificateRhs (span : ℝ) : ℝ :=
  dutEta * max (dutR - span) 0

/-- The stronger local lower bound supplied by the external verifier. -/
def dutVerifierCertificateRhs (span : ℝ) : ℝ :=
  dutEta * max (dutVerifierR - span) 0

lemma dutEta_nonneg : 0 ≤ dutEta := by
  norm_num [dutEta]

lemma dutR_nonneg : 0 ≤ dutR := by
  norm_num [dutR]

lemma dutVerifierR_nonneg : 0 ≤ dutVerifierR := by
  norm_num [dutVerifierR]

lemma dutR_lt_verifierR : dutR < dutVerifierR := by
  norm_num [dutR, dutVerifierR]

lemma dutCertificateTransferSlack_nonneg :
    0 ≤ dutCertificateTransferSlack := by
  norm_num [dutCertificateTransferSlack]

lemma dutEta_mul_dutR_lt_one : dutEta * dutR < 1 := by
  norm_num [dutEta, dutR]

lemma dutCertificateRhs_nonneg (span : ℝ) :
    0 ≤ dutCertificateRhs span := by
  unfold dutCertificateRhs
  exact mul_nonneg dutEta_nonneg (le_max_right _ _)

/-- For nonnegative spans, the Lean-side certified local saving is strictly
below one. -/
lemma dutCertificateRhs_lt_one {span : ℝ} (hspan : 0 ≤ span) :
    dutCertificateRhs span < 1 := by
  have hmax : max (dutR - span) 0 ≤ dutR := by
    apply max_le
    · linarith [dutR_nonneg]
    · exact dutR_nonneg
  calc
    dutCertificateRhs span
        ≤ dutEta * dutR := by
            unfold dutCertificateRhs
            exact mul_le_mul_of_nonneg_left hmax dutEta_nonneg
    _ < 1 := dutEta_mul_dutR_lt_one

/-- Below the buffered Lean cutoff, the verifier RHS exceeds the Lean RHS by
exactly the fixed transfer slack. -/
lemma dutCertificateRhs_add_slack_le_verifierRhs
    {span : ℝ} (hspan : span < dutR) :
    dutCertificateRhs span + dutCertificateTransferSlack
      ≤ dutVerifierCertificateRhs span := by
  have hlean : 0 ≤ dutR - span := by linarith
  have hver : 0 ≤ dutVerifierR - span := by
    linarith [dutR_lt_verifierR]
  rw [dutCertificateRhs, dutVerifierCertificateRhs]
  rw [max_eq_left hlean, max_eq_left hver]
  norm_num [dutEta, dutR, dutVerifierR, dutCertificateTransferSlack]
  linarith

/-- At and beyond the buffered Lean cutoff, the Lean target saving vanishes. -/
lemma dutCertificateRhs_eq_zero_of_ge
    {span : ℝ} (hspan : dutR ≤ span) :
    dutCertificateRhs span = 0 := by
  unfold dutCertificateRhs
  rw [max_eq_right]
  · ring
  · linarith

/-- Quadratic spectral energy appearing for a 6x6 Gram matrix with unit
ideal diagonal. -/
def dutSpectralEnergy (lam : Fin 6 → ℝ) : ℝ :=
  ∑ j, (lam j - 1) ^ 2

/-- If a nonnegative six-spectrum has enough quadratic energy to meet the
certificate RHS, then its c=2 DUT defect has at least the same saving. -/
lemma dutDefect2_ge_certificate_of_energy
    (lam : Fin 6 → ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    {span : ℝ} (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤ dutSpectralEnergy lam) :
    dutCertificateRhs span ≤ ∑ j, dutDefect2 (lam j) := by
  by_cases hlarge : ∃ j, 2 ≤ lam j
  · rcases hlarge with ⟨j, hj⟩
    have hdefj : 1 ≤ dutDefect2 (lam j) := by
      rw [dutDefect2_of_ge hj]
      linarith
    have hsumj : dutDefect2 (lam j) ≤ ∑ k, dutDefect2 (lam k) := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 6)))
          (f := fun k => dutDefect2 (lam k))
          (fun k _ => dutDefect2_nonneg (hlam k))
          (by simp : j ∈ (Finset.univ : Finset (Fin 6))))
    have hrhs : dutCertificateRhs span ≤ 1 :=
      le_of_lt (dutCertificateRhs_lt_one hspan)
    exact hrhs.trans (hdefj.trans hsumj)
  · have hsmall : ∀ j, lam j ≤ 2 := by
      intro j
      exact le_of_not_ge (not_exists.mp hlarge j)
    have hdefeq : (∑ j, dutDefect2 (lam j)) = dutSpectralEnergy lam := by
      unfold dutSpectralEnergy
      apply Finset.sum_congr rfl
      intro j hj
      exact dutDefect2_of_le (hsmall j)
    rw [hdefeq]
    exact henergy

/-- The same spectral-energy certificate implies the c=3 DUT defect saving. -/
lemma dutDefect3_ge_certificate_of_energy
    (lam : Fin 6 → ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    {span : ℝ} (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤ dutSpectralEnergy lam) :
    dutCertificateRhs span ≤ ∑ j, dutDefect3 (lam j) := by
  by_cases hlarge : ∃ j, 3 ≤ lam j
  · rcases hlarge with ⟨j, hj⟩
    have hdefj : 1 ≤ dutDefect3 (lam j) := by
      rw [dutDefect3_of_ge hj]
      linarith
    have hsumj : dutDefect3 (lam j) ≤ ∑ k, dutDefect3 (lam k) := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 6)))
          (f := fun k => dutDefect3 (lam k))
          (fun k _ => dutDefect3_nonneg (hlam k))
          (by simp : j ∈ (Finset.univ : Finset (Fin 6))))
    have hrhs : dutCertificateRhs span ≤ 1 :=
      le_of_lt (dutCertificateRhs_lt_one hspan)
    exact hrhs.trans (hdefj.trans hsumj)
  · have hsmall : ∀ j, lam j ≤ 3 := by
      intro j
      exact le_of_not_ge (not_exists.mp hlarge j)
    have hdefeq : (∑ j, dutDefect3 (lam j)) = dutSpectralEnergy lam := by
      unfold dutSpectralEnergy
      apply Finset.sum_congr rfl
      intro j hj
      exact dutDefect3_of_le (hsmall j)
    rw [hdefeq]
    exact henergy

/-- Combined c=2/c=3 certificate interface.  This is the theorem an external
or future formally verified six-point energy certificate can feed directly. -/
theorem dut_certificate_energy_gives_both_defects
    (lam : Fin 6 → ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    {span : ℝ} (hspan : 0 ≤ span)
    (henergy : dutCertificateRhs span ≤ dutSpectralEnergy lam) :
    dutCertificateRhs span ≤ ∑ j, dutDefect2 (lam j)
      ∧ dutCertificateRhs span ≤ ∑ j, dutDefect3 (lam j) := by
  constructor
  · exact dutDefect2_ge_certificate_of_energy lam hlam hspan henergy
  · exact dutDefect3_ge_certificate_of_energy lam hlam hspan henergy

end Zeta23.ZeroSide.RankTraceMult
