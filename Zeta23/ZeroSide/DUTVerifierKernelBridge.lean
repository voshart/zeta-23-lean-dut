/-
DUTVerifierKernelBridge.lean

Exact Lean bridge between the physical sharp Fourier kernel used by the DUT
formalization and the dimensionless sinc kernel used by verify_dut_six.py.

No external numerical assertion occurs in this file.
-/

import Zeta23.ZeroSide.DUTVerifierScaleFreePrelude
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Elementary Fourier integral of one cosine over a symmetric interval,
written in the removable-singularity-safe sinc form. -/
private theorem dut_integral_cos_scaled_sinc
    {L c : ℝ} (hL : 0 < L) :
    (∫ u in (-(L / 2))..(L / 2), Real.cos (c * u))
      =
    L * Real.sinc (c * L / 2) := by
  by_cases hc : c = 0
  · subst c
    simp [intervalIntegral.integral_const]
  · have hcL : c * L / 2 ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero hc hL.ne'
      · norm_num
    rw [intervalIntegral.integral_comp_mul_left Real.cos hc,
      integral_cos, smul_eq_mul]
    rw [Real.sinc_of_ne_zero hcL]
    have hneg :
        c * (-(L / 2)) = -(c * L / 2) := by ring
    have hpos :
        c * (L / 2) = c * L / 2 := by ring
    rw [hneg, hpos, Real.sin_neg]
    field_simp [hc, hL.ne']
    ring

/-- Symmetric integral of the cosine product occurring in the real part of
the sharp-window Fourier transform. -/
private theorem dut_integral_cos_product_sinc
    {L a x : ℝ} (hL : 0 < L) :
    (∫ u in (-(L / 2))..(L / 2),
        Real.cos (a * u) * Real.cos (x * u))
      =
    (L / 2) *
      (Real.sinc ((x - a) * L / 2)
        + Real.sinc ((x + a) * L / 2)) := by
  have hpoint :
      ∀ u : ℝ,
        Real.cos (a * u) * Real.cos (x * u)
          =
        (Real.cos ((x - a) * u)
            + Real.cos ((x + a) * u)) / 2 := by
    intro u
    have htrig := Real.two_mul_cos_mul_cos (x * u) (a * u)
    have hsub :
        x * u - a * u = (x - a) * u := by ring
    have hadd :
        x * u + a * u = (x + a) * u := by ring
    rw [hsub, hadd] at htrig
    nlinarith [htrig]

  rw [intervalIntegral.integral_congr
    (fun u _ => hpoint u)]

  have hminus :
      IntervalIntegrable
        (fun u : ℝ => Real.cos ((x - a) * u))
        MeasureTheory.volume (-(L / 2)) (L / 2) :=
    (by fun_prop : Continuous
      (fun u : ℝ => Real.cos ((x - a) * u))).intervalIntegrable _ _

  have hplus :
      IntervalIntegrable
        (fun u : ℝ => Real.cos ((x + a) * u))
        MeasureTheory.volume (-(L / 2)) (L / 2) :=
    (by fun_prop : Continuous
      (fun u : ℝ => Real.cos ((x + a) * u))).intervalIntegrable _ _

  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add hminus hplus,
    dut_integral_cos_scaled_sinc hL,
    dut_integral_cos_scaled_sinc hL]
  ring

/-- Raw closed form for Anthropic's paper-Fourier transform of the hard
cutoff cosine window. -/
theorem dutDSharpKernelRaw_eq_sinc
    {lam L x : ℝ}
    (hlam : 0 < lam) (hL : 0 < L) :
    (paperFT
      (fun u => (ThmD.sharpW lam L u : ℂ))
      x).re
      =
    (L / 2) *
      (Real.sinc (x * L / 2 - ThmD.theta lam)
        + Real.sinc (x * L / 2 + ThmD.theta lam)) := by
  let g : ℝ → ℂ :=
    fun u =>
      (ThmD.vStar lam (u / L) : ℂ)
        * cexp (I * (x : ℂ) * u)

  have hind :
      ∀ u : ℝ,
        (ThmD.sharpW lam L u : ℂ)
            * cexp (I * (x : ℂ) * u)
          =
        (Set.Icc (-(L / 2)) (L / 2)).indicator g u := by
    intro u
    unfold ThmD.sharpW
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · simp [g, hu]
    · simp [g, hu]

  have hgcont : Continuous g := by
    unfold g ThmD.vStar
    fun_prop

  have hgint :
      IntervalIntegrable g MeasureTheory.volume
        (-(L / 2)) (L / 2) :=
    hgcont.intervalIntegrable _ _

  rw [paperFT_def]
  rw [MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_of_all _ hind),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by linarith : -(L / 2) ≤ L / 2)]

  have hre :
      (∫ u in (-(L / 2))..(L / 2), g u).re
        =
      ∫ u in (-(L / 2))..(L / 2), (g u).re := by
    symm
    exact intervalIntegral.intervalIntegral_re hgint

  rw [hre]

  have hreal :
      ∀ u : ℝ,
        (g u).re
          =
        Real.cos (Real.sqrt 2 * lam / L * u)
          * Real.cos (x * u) := by
    intro u
    have hexp :
        (cexp (I * (x : ℂ) * u)).re
          = Real.cos (x * u) := by
      have harg :
          I * (x : ℂ) * (u : ℂ)
            = ((x * u : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [harg, Complex.exp_ofReal_mul_I_re]
    unfold g ThmD.vStar
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hexp]
    congr 2
    field_simp [hL.ne']

  rw [intervalIntegral.integral_congr
    (fun u _ => hreal u)]

  rw [dut_integral_cos_product_sinc hL]

  have htheta :
      Real.sqrt 2 * lam / L * L / 2
        = ThmD.theta lam := by
    have hs := ThmD.sqrt2_mul_half (lam := lam)
    field_simp [hL.ne'] at ⊢
    nlinarith [hs]

  have hminus :
      (x - Real.sqrt 2 * lam / L) * L / 2
        = x * L / 2 - ThmD.theta lam := by
    rw [← htheta]
    field_simp [hL.ne']

  have hplus :
      (x + Real.sqrt 2 * lam / L) * L / 2
        = x * L / 2 + ThmD.theta lam := by
    rw [← htheta]
    field_simp [hL.ne']

  rw [hminus, hplus]

/-- Project wrapper of the raw closed form. -/
theorem dutDSharpKernelRaw_closedForm
    (P : Params) (hP : P.Valid)
    {T x : ℝ} (hL : 0 < P.L T) :
    dutDSharpKernelRaw P T x
      =
    (P.L T / 2) *
      (Real.sinc (x * P.L T / 2 - ThmD.theta P.lam)
        + Real.sinc (x * P.L T / 2 + ThmD.theta P.lam)) := by
  unfold dutDSharpKernelRaw
  exact dutDSharpKernelRaw_eq_sinc hP.lam_pos hL

/-- The physical frequency `x` and verifier coordinate differ exactly by the
paper Fourier scale `L/(2*pi)`. -/
private theorem dut_pi_mul_verifierCoord
    {L x : ℝ} :
    Real.pi * dutVerifierCoord L x = x * L / 2 := by
  unfold dutVerifierCoord
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

/-- Exact identity between the normalized physical sharp kernel and the
dimensionless sinc kernel evaluated by the external verifier. -/
theorem dutDSharpKernel_eq_scaleFree
    (P : Params) (hP : P.Valid)
    {T x : ℝ} (hL : 0 < P.L T) :
    dutDSharpKernel P T x
      =
    dutScaleFreeKernel P.lam
      (dutVerifierCoord (P.L T) x) := by
  have htheta : ThmD.theta P.lam ≠ 0 :=
    ne_of_gt (ThmD.theta_pos hP.lam_pos)

  have hsinc_pos :
      0 < Real.sinc (ThmD.theta P.lam) := by
    rw [Real.sinc_of_ne_zero htheta]
    exact div_pos
      (ThmD.sin_theta_pos hP.lam_pos hP.lam_le_one)
      (ThmD.theta_pos hP.lam_pos)

  have hsinc_ne :
      Real.sinc (ThmD.theta P.lam) ≠ 0 :=
    ne_of_gt hsinc_pos

  rw [dutDSharpKernel]
  rw [dutDSharpKernelRaw_closedForm P hP hL]
  rw [dut_aStar_eq_sinc hP.lam_pos]
  unfold dutScaleFreeKernel
  rw [dut_pi_mul_verifierCoord]
  field_simp [hL.ne', hsinc_ne]

end Zeta23.ZeroSide.RankTraceMult
