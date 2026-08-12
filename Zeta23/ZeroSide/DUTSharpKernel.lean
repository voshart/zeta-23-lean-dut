/-
DUTSharpKernel.lean

Uniform raw-kernel comparison for Anthropic's concrete Theorem-D window.

Anthropic already proves the endpoint-taper estimate

  ∫ |phiD(u)^2 - sharpW(u)| du <= 2 w,

where

  sharpW(u) = 1_{[-L/2,L/2]}(u) * cos(sqrt(2) * lam * u/L).

This file pushes that L1 estimate through the paper Fourier transform.  Since
the transform at a real frequency has a unit-modulus exponential factor, the
raw full-Poisson kernel and the raw sharp cosine kernel differ by at most 2 w,
uniformly in frequency.

This is the second arrow in

  finite six-zero Gram
      -> full Poisson kernel
      -> sharp cosine kernel.

It does NOT yet normalize by a_D L / a*_lam L and does NOT yet control the
finite-grid truncation.

Intended location:
  Zeta23/ZeroSide/DUTSharpKernel.lean
-/

import Zeta23.ZeroSide.DUTFullPoissonKernel

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Fourier transform of the hard-cutoff cosine profile, restricted to real
frequencies and taking the real part. -/
noncomputable def dutDSharpKernelRaw (P : Params) (T x : ℝ) : ℝ :=
  (paperFT
    (fun u => (ThmD.sharpW P.lam (P.L T) u : ℂ))
    x).re

/-- The complexified squared Theorem-D window is integrable. -/
private lemma dutD_phiDsq_integrable
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    Integrable (fun u => (((P.phiD T u) ^ 2 : ℝ) : ℂ)) := by
  have hW := ThmD.admWindow_params hP h8
  exact hW.vSqC_continuous.integrable_of_hasCompactSupport hW.vSqC_hasCompactSupport

/-- The complexified hard-cutoff cosine profile is integrable. -/
private lemma dutD_sharp_integrable
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    Integrable (fun u => (ThmD.sharpW P.lam (P.L T) u : ℂ)) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hr : Integrable (ThmD.sharpW P.lam (P.L T)) := by
    unfold ThmD.sharpW
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (((by
          unfold ThmD.vStar
          fun_prop :
          Continuous fun u : ℝ => ThmD.vStar P.lam (u / P.L T)).continuousOn).integrableOn_compact
        isCompact_Icc)
  exact hr.ofReal

/-- Outside the common support interval, the difference of the squared smooth
window and the sharp profile vanishes. -/
private lemma dutD_sq_sub_sharp_support
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    ∀ u,
      ((((P.phiD T u) ^ 2 - ThmD.sharpW P.lam (P.L T) u : ℝ) : ℂ) ≠ 0) →
      |u| ≤ P.L T / 2 := by
  have hW := ThmD.admWindow_params hP h8
  intro u hu
  by_contra hout
  have hout' : P.L T / 2 < |u| := lt_of_not_ge hout
  have hphi : P.phiD T u = 0 := hW.support u (le_of_lt hout')
  have hsharp : ThmD.sharpW P.lam (P.L T) u = 0 := by
    unfold ThmD.sharpW
    apply Set.indicator_of_notMem
    intro hm
    have habs : |u| ≤ P.L T / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
    linarith
  apply hu
  simp [hphi, hsharp]

/-- The complex-valued difference between the squared smooth window and
the hard-cutoff cosine profile.  Keeping the subtraction in `ℂ` avoids
coercion/pointwise-subtraction mismatches in the Bochner integral API. -/
private noncomputable def dutDWindowDiff (P : Params) (T : ℝ) (u : ℝ) : ℂ :=
  (((P.phiD T u) ^ 2 : ℝ) : ℂ) -
    (ThmD.sharpW P.lam (P.L T) u : ℂ)

/-- The complex difference is integrable. -/
private lemma dutDWindowDiff_integrable
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    Integrable (dutDWindowDiff P T) := by
  exact
    (dutD_phiDsq_integrable P hP h8).sub'
      (dutD_sharp_integrable P hP h8)

/-- The complex difference is supported in the same interval. -/
private lemma dutDWindowDiff_support
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    ∀ u, dutDWindowDiff P T u ≠ 0 → |u| ≤ P.L T / 2 := by
  have hW := ThmD.admWindow_params hP h8
  intro u hu
  by_contra hout
  have hout' : P.L T / 2 < |u| := lt_of_not_ge hout
  have hphi : P.phiD T u = 0 := hW.support u (le_of_lt hout')
  have hsharp : ThmD.sharpW P.lam (P.L T) u = 0 := by
    unfold ThmD.sharpW
    apply Set.indicator_of_notMem
    intro hm
    have habs : |u| ≤ P.L T / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
    linarith
  apply hu
  simp [dutDWindowDiff, hphi, hsharp]

/-- Linearity identity needed to compare the two real Fourier kernels. -/
private lemma dutD_paperFT_sq_sub_sharp
    (P : Params) (hP : P.Valid) {T x : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    paperFT (dutDWindowDiff P T) x
      =
      AdmWindow.VPhi (P.phiD T) x
        - paperFT (fun u => (ThmD.sharpW P.lam (P.L T) u : ℂ)) x := by
  have hphi := dutD_phiDsq_integrable P hP h8
  have hsharp := dutD_sharp_integrable P hP h8
  have hexp_meas :
      AEStronglyMeasurable
        (fun u : ℝ => cexp (I * (x : ℂ) * u))
        MeasureTheory.volume :=
    (by fun_prop : Continuous fun u : ℝ => cexp (I * (x : ℂ) * u)).aestronglyMeasurable
  have hexp_le :
      ∀ᵐ u : ℝ ∂MeasureTheory.volume, ‖cexp (I * (x : ℂ) * u)‖ ≤ 1 :=
    MeasureTheory.ae_of_all _ fun u => by
      rw [Zeta23.norm_cexp_I_mul]
      simp
  have hphi_exp :
      Integrable
        (fun u : ℝ =>
          (((P.phiD T u) ^ 2 : ℝ) : ℂ) * cexp (I * (x : ℂ) * u)) :=
    hphi.mul_bdd hexp_meas hexp_le
  have hsharp_exp :
      Integrable
        (fun u : ℝ =>
          (ThmD.sharpW P.lam (P.L T) u : ℂ) * cexp (I * (x : ℂ) * u)) :=
    hsharp.mul_bdd hexp_meas hexp_le
  unfold AdmWindow.VPhi dutDWindowDiff
  rw [paperFT_def, paperFT_def, paperFT_def]
  simp only [sub_mul]
  exact MeasureTheory.integral_sub hphi_exp hsharp_exp

/-- **Uniform endpoint-taper Fourier error.**

At every real frequency `x`, the raw full-Poisson kernel of the concrete
Theorem-D window differs from the raw hard-cutoff cosine kernel by at most
`2 * w`.  This is exactly the Fourier-side consequence of Anthropic's
`integral_abs_phiDsq_sub_sharp`. -/
theorem dutDFullKernelRaw_close_sharp
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (x : ℝ) :
    |dutDFullKernelRaw P T x - dutDSharpKernelRaw P T x| ≤ 2 * P.w := by
  have hdiff : Integrable (dutDWindowDiff P T) :=
    dutDWindowDiff_integrable P hP h8
  have hsupp := dutDWindowDiff_support P hP h8
  have hFT := norm_paperFT_le hdiff hsupp (x : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at hFT

  have hl1 :
      ∫ u,
        |(P.phiD T u) ^ 2 - ThmD.sharpW P.lam (P.L T) u|
        ≤ 2 * P.w := by
    simpa [Params.phiD] using
      (ThmD.integral_abs_phiDsq_sub_sharp
        hP.taper hP.lam_pos hP.lam_le_one
        (by linarith [hP.one_le_w] : 0 < P.w)
        (by linarith [hP.one_le_w, h8] : 2 * P.w ≤ P.L T))

  have hlin := dutD_paperFT_sq_sub_sharp P hP (T := T) (x := x) h8
  have hre0 := congrArg Complex.re hlin
  have hre :
      dutDFullKernelRaw P T x - dutDSharpKernelRaw P T x
        = (paperFT (dutDWindowDiff P T) x).re := by
    unfold dutDFullKernelRaw dutDSharpKernelRaw AdmWindow.VPhiR
    simpa [Complex.sub_re] using hre0.symm

  rw [hre]
  calc
    |(paperFT (dutDWindowDiff P T) x).re|
        ≤ ‖paperFT (dutDWindowDiff P T) x‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∫ u, ‖dutDWindowDiff P T u‖ := hFT
    _ = ∫ u,
          |(P.phiD T u) ^ 2 - ThmD.sharpW P.lam (P.L T) u| := by
      apply MeasureTheory.integral_congr_ae
      apply MeasureTheory.ae_of_all
      intro u
      change
        ‖dutDWindowDiff P T u‖ =
          |(P.phiD T u) ^ 2 - ThmD.sharpW P.lam (P.L T) u|
      have hcoe :
          dutDWindowDiff P T u =
            (((P.phiD T u) ^ 2 - ThmD.sharpW P.lam (P.L T) u : ℝ) : ℂ) := by
        simp [dutDWindowDiff]
      rw [hcoe, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * P.w := hl1

end Zeta23.ZeroSide.RankTraceMult
