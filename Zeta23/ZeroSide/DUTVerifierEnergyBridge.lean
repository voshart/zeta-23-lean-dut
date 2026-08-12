/-
DUTVerifierEnergyBridge.lean

Close the final algebraic matching seam between the matrix energy used by Lean

  dutGramEnergy (dutScaleFreeSharpMatrix lam x)

and the exact 15-pair scalar energy evaluated by verify_dut_six.py

  2 * sum_{0 <= i < j <= 5} k_lam(x_j-x_i)^2.

No external numerical assertion occurs here.
-/

import Zeta23.ZeroSide.DUTVerifierCertificateBridge
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The scale-free sinc kernel is even. -/
theorem dutScaleFreeKernel_neg
    (lam y : ℝ) :
    dutScaleFreeKernel lam (-y) = dutScaleFreeKernel lam y := by
  unfold dutScaleFreeKernel
  have hminus :
      Real.pi * (-y) - ThmD.theta lam
        = -(Real.pi * y + ThmD.theta lam) := by
    ring
  have hplus :
      Real.pi * (-y) + ThmD.theta lam
        = -(Real.pi * y - ThmD.theta lam) := by
    ring
  rw [hminus, hplus, Real.sinc_neg, Real.sinc_neg]
  ring

/-- At parameters where the normalizing sinc is nonzero, the normalized
kernel has diagonal value one. -/
theorem dutScaleFreeKernel_zero
    {lam : ℝ}
    (hsinc : Real.sinc (ThmD.theta lam) ≠ 0) :
    dutScaleFreeKernel lam 0 = 1 := by
  unfold dutScaleFreeKernel
  simp only [mul_zero, zero_sub, zero_add, Real.sinc_neg]
  field_simp [hsinc]
  norm_num

/-- Exact scalar energy used by the Python verifier: twice the 15 unordered
off-diagonal pair squares for six points. -/
noncomputable def dutScaleFreePairEnergy
    (lam : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  2 * (
      dutScaleFreeKernel lam (x 1 - x 0) ^ 2
    + dutScaleFreeKernel lam (x 2 - x 0) ^ 2
    + dutScaleFreeKernel lam (x 2 - x 1) ^ 2
    + dutScaleFreeKernel lam (x 3 - x 0) ^ 2
    + dutScaleFreeKernel lam (x 3 - x 1) ^ 2
    + dutScaleFreeKernel lam (x 3 - x 2) ^ 2
    + dutScaleFreeKernel lam (x 4 - x 0) ^ 2
    + dutScaleFreeKernel lam (x 4 - x 1) ^ 2
    + dutScaleFreeKernel lam (x 4 - x 2) ^ 2
    + dutScaleFreeKernel lam (x 4 - x 3) ^ 2
    + dutScaleFreeKernel lam (x 5 - x 0) ^ 2
    + dutScaleFreeKernel lam (x 5 - x 1) ^ 2
    + dutScaleFreeKernel lam (x 5 - x 2) ^ 2
    + dutScaleFreeKernel lam (x 5 - x 3) ^ 2
    + dutScaleFreeKernel lam (x 5 - x 4) ^ 2)

/-- Frobenius square of the scale-free matrix is the sum of all 36 entry
squares. -/
private theorem dutScaleFree_frobSq_eq_sum_sq
    (lam : ℝ) (x : Fin 6 → ℝ) :
    frobSq (dutScaleFreeSharpMatrix lam x)
      =
    ∑ i : Fin 6, ∑ j : Fin 6,
      dutScaleFreeKernel lam (x j - x i) ^ 2 := by
  simp [RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply,
    dutScaleFreeSharpMatrix, pow_two]

/-- The trace of the normalized scale-free matrix is exactly six. -/
private theorem dutScaleFree_rtrace_eq_six
    {lam : ℝ} (x : Fin 6 → ℝ)
    (hsinc : Real.sinc (ThmD.theta lam) ≠ 0) :
    rtrace (dutScaleFreeSharpMatrix lam x) = 6 := by
  simp [RHLinalg.rtrace, Matrix.trace, dutScaleFreeSharpMatrix,
    dutScaleFreeKernel_zero hsinc]

/-- Exact identity matching Lean's Gram energy to the scalar 15-pair energy
used by the external verifier. -/
theorem dutGramEnergy_scaleFree_eq_pairEnergy
    {lam : ℝ} (x : Fin 6 → ℝ)
    (hsinc : Real.sinc (ThmD.theta lam) ≠ 0) :
    dutGramEnergy (dutScaleFreeSharpMatrix lam x)
      =
    dutScaleFreePairEnergy lam x := by
  have hfrob :=
    dutScaleFree_frobSq_eq_sum_sq lam x
  have htrace :=
    dutScaleFree_rtrace_eq_six x hsinc

  have h01 :
      dutScaleFreeKernel lam (x 0 - x 1) ^ 2
        = dutScaleFreeKernel lam (x 1 - x 0) ^ 2 := by
    rw [show x 0 - x 1 = -(x 1 - x 0) by ring,
      dutScaleFreeKernel_neg]
  have h02 :
      dutScaleFreeKernel lam (x 0 - x 2) ^ 2
        = dutScaleFreeKernel lam (x 2 - x 0) ^ 2 := by
    rw [show x 0 - x 2 = -(x 2 - x 0) by ring,
      dutScaleFreeKernel_neg]
  have h03 :
      dutScaleFreeKernel lam (x 0 - x 3) ^ 2
        = dutScaleFreeKernel lam (x 3 - x 0) ^ 2 := by
    rw [show x 0 - x 3 = -(x 3 - x 0) by ring,
      dutScaleFreeKernel_neg]
  have h04 :
      dutScaleFreeKernel lam (x 0 - x 4) ^ 2
        = dutScaleFreeKernel lam (x 4 - x 0) ^ 2 := by
    rw [show x 0 - x 4 = -(x 4 - x 0) by ring,
      dutScaleFreeKernel_neg]
  have h05 :
      dutScaleFreeKernel lam (x 0 - x 5) ^ 2
        = dutScaleFreeKernel lam (x 5 - x 0) ^ 2 := by
    rw [show x 0 - x 5 = -(x 5 - x 0) by ring,
      dutScaleFreeKernel_neg]

  have h12 :
      dutScaleFreeKernel lam (x 1 - x 2) ^ 2
        = dutScaleFreeKernel lam (x 2 - x 1) ^ 2 := by
    rw [show x 1 - x 2 = -(x 2 - x 1) by ring,
      dutScaleFreeKernel_neg]
  have h13 :
      dutScaleFreeKernel lam (x 1 - x 3) ^ 2
        = dutScaleFreeKernel lam (x 3 - x 1) ^ 2 := by
    rw [show x 1 - x 3 = -(x 3 - x 1) by ring,
      dutScaleFreeKernel_neg]
  have h14 :
      dutScaleFreeKernel lam (x 1 - x 4) ^ 2
        = dutScaleFreeKernel lam (x 4 - x 1) ^ 2 := by
    rw [show x 1 - x 4 = -(x 4 - x 1) by ring,
      dutScaleFreeKernel_neg]
  have h15 :
      dutScaleFreeKernel lam (x 1 - x 5) ^ 2
        = dutScaleFreeKernel lam (x 5 - x 1) ^ 2 := by
    rw [show x 1 - x 5 = -(x 5 - x 1) by ring,
      dutScaleFreeKernel_neg]

  have h23 :
      dutScaleFreeKernel lam (x 2 - x 3) ^ 2
        = dutScaleFreeKernel lam (x 3 - x 2) ^ 2 := by
    rw [show x 2 - x 3 = -(x 3 - x 2) by ring,
      dutScaleFreeKernel_neg]
  have h24 :
      dutScaleFreeKernel lam (x 2 - x 4) ^ 2
        = dutScaleFreeKernel lam (x 4 - x 2) ^ 2 := by
    rw [show x 2 - x 4 = -(x 4 - x 2) by ring,
      dutScaleFreeKernel_neg]
  have h25 :
      dutScaleFreeKernel lam (x 2 - x 5) ^ 2
        = dutScaleFreeKernel lam (x 5 - x 2) ^ 2 := by
    rw [show x 2 - x 5 = -(x 5 - x 2) by ring,
      dutScaleFreeKernel_neg]

  have h34 :
      dutScaleFreeKernel lam (x 3 - x 4) ^ 2
        = dutScaleFreeKernel lam (x 4 - x 3) ^ 2 := by
    rw [show x 3 - x 4 = -(x 4 - x 3) by ring,
      dutScaleFreeKernel_neg]
  have h35 :
      dutScaleFreeKernel lam (x 3 - x 5) ^ 2
        = dutScaleFreeKernel lam (x 5 - x 3) ^ 2 := by
    rw [show x 3 - x 5 = -(x 5 - x 3) by ring,
      dutScaleFreeKernel_neg]

  have h45 :
      dutScaleFreeKernel lam (x 4 - x 5) ^ 2
        = dutScaleFreeKernel lam (x 5 - x 4) ^ 2 := by
    rw [show x 4 - x 5 = -(x 5 - x 4) by ring,
      dutScaleFreeKernel_neg]

  rw [dutGramEnergy, hfrob, htrace]
  simp only [Fin.sum_univ_six]
  simp only [sub_self, dutScaleFreeKernel_zero hsinc, one_pow]
  rw [h01, h02, h03, h04, h05,
      h12, h13, h14, h15,
      h23, h24, h25,
      h34, h35, h45]
  unfold dutScaleFreePairEnergy
  ring

/-- Scalar certificate phrased exactly in terms of the 15 pair squares that
the external verifier evaluates. -/
def DUTScaleFreePairCertificate (lam : ℝ) : Prop :=
  ∀ x : Fin 6 → ℝ, StrictMono x →
    dutVerifierCertificateRhs (x 5 - x 0)
      ≤ dutScaleFreePairEnergy lam x

/-- The scalar 15-pair certificate and the matrix-form Lean certificate are
identical whenever the kernel normalization is nonzero. -/
theorem dutScaleFreePairCertificate_iff
    {lam : ℝ}
    (hsinc : Real.sinc (ThmD.theta lam) ≠ 0) :
    DUTScaleFreePairCertificate lam
      ↔ DUTScaleFreeSharpCertificate lam := by
  constructor
  · intro h x hx
    rw [dutGramEnergy_scaleFree_eq_pairEnergy x hsinc]
    exact h x hx
  · intro h x hx
    rw [← dutGramEnergy_scaleFree_eq_pairEnergy x hsinc]
    exact h x hx

/-- The normalizing sinc is nonzero at the concrete verifier parameter. -/
theorem dutVerifierLam_sinc_ne :
    Real.sinc (ThmD.theta dutVerifierLam) ≠ 0 := by
  have h0 : 0 < dutVerifierLam := by
    linarith [dutVerifierLam_half_le]
  have htheta : 0 < ThmD.theta dutVerifierLam :=
    ThmD.theta_pos h0
  rw [Real.sinc_of_ne_zero htheta.ne']
  exact (div_pos
    (ThmD.sin_theta_pos h0 dutVerifierLam_lt_one.le)
    htheta).ne'

/-- Concrete scalar certificate implies the exact matrix proposition used by
the already-built final bridge. -/
theorem dutFixedScaleFreeSharpCertificate_of_pair
    (hcert : DUTScaleFreePairCertificate dutVerifierLam) :
    DUTFixedScaleFreeSharpCertificate := by
  unfold DUTFixedScaleFreeSharpCertificate
  exact
    (dutScaleFreePairCertificate_iff dutVerifierLam_sinc_ne).mp hcert

/-- Final headline with the external boundary now written literally as the
15-pair scalar energy checked by the Python/Arb verifier. -/
theorem dut_thmD₀_simple_6727918_of_pair_certificate
    (hcert : DUTScaleFreePairCertificate dutVerifierLam) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3363959 : ℝ) / 5000000 - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  exact
    dut_thmD₀_simple_6727918_of_scaleFree_certificate
      (dutFixedScaleFreeSharpCertificate_of_pair hcert)

end Zeta23.ZeroSide.RankTraceMult
