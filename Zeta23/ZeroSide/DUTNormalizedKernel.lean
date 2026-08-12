/-
DUTNormalizedKernel.lean

Normalized full-Poisson -> sharp-cosine kernel comparison for the concrete
Theorem-D window.

Built on:
  * DUTSharpKernel: raw Fourier error <= 2 w;
  * ThmD.aD_close: |a_D - a*_lam| <= 4 w / L;
  * ThmD.aD_range_of: 1/2 <= a_D <= 1;
  * AdmWindow.abs_VPhiR_le_L: the raw smooth kernel is bounded by L.

We deliberately use a loose constant.  Under 16 w <= L (and the existing
4 pi w <= L condition needed for a_D >= 1/2),

  | K_full(x) - K_sharp(x) | <= 40 w / L,

where
  K_full  = VPhiR(phiD)(x) / (a_D L),
  K_sharp = sharpFT(x)     / (a*_lam L).

The constant 40 is not intended to be sharp.  Its role is to make the
normalization error explicit and O(w/L), which is enough for the later
eventual-in-T certificate transfer.

Intended location:
  Zeta23/ZeroSide/DUTNormalizedKernel.lean
-/

import Zeta23.ZeroSide.DUTSharpKernel

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The normalized hard-cutoff cosine kernel corresponding to the scale-free
Theorem-D profile `vStar`. -/
noncomputable def dutDSharpKernel (P : Params) (T x : ℝ) : ℝ :=
  dutDSharpKernelRaw P T x / (ThmD.aStar P.lam * P.L T)

/-- Abstract real quotient perturbation estimate used by the concrete kernel
comparison below.  The constants are chosen to match:
  d >= L/2, c >= L/4,
  |A-K| <= 2w, |d-c| <= 4w, |K| <= 9L/8.
-/
private lemma dut_quotient_close_40
    {A K d c L w : ℝ}
    (hL : 0 < L) (hw : 0 ≤ w) (h16 : 16 * w ≤ L)
    (hd : L / 2 ≤ d) (hc : L / 4 ≤ c)
    (hAK : |A - K| ≤ 2 * w)
    (hK : |K| ≤ 9 * L / 8)
    (hdc : |d - c| ≤ 4 * w) :
    |A / d - K / c| ≤ 40 * w / L := by
  have hd0 : 0 < d := lt_of_lt_of_le (by linarith) hd
  have hc0 : 0 < c := lt_of_lt_of_le (by linarith) hc

  have hsplit :
      A / d - K / c =
        (A - K) / d + K * (c - d) / (d * c) := by
    field_simp [hd0.ne', hc0.ne']
    ring

  have hterm1 : |(A - K) / d| ≤ 4 * w / L := by
    rw [abs_div, abs_of_pos hd0]
    rw [div_le_div_iff₀ hd0 hL]
    have h1 := mul_le_mul_of_nonneg_right hAK hL.le
    have h2 := mul_le_mul_of_nonneg_left hd hw
    nlinarith

  have hdc' : |c - d| ≤ 4 * w := by
    simpa [abs_sub_comm] using hdc

  have hden : L ^ 2 / 8 ≤ d * c := by
    have hmul :=
      mul_le_mul hd hc (by positivity : 0 ≤ L / 4) (le_trans (by positivity : 0 ≤ L / 2) hd)
    nlinarith

  have hnum : |K| * |c - d| ≤ (9 * L / 8) * (4 * w) :=
    mul_le_mul hK hdc' (abs_nonneg _) (by positivity)

  have hterm2 : |K * (c - d) / (d * c)| ≤ 36 * w / L := by
    have hdcpos : 0 < d * c := mul_pos hd0 hc0
    rw [abs_div, abs_mul, abs_of_pos hdcpos]
    rw [div_le_div_iff₀ hdcpos hL]
    have hnumL := mul_le_mul_of_nonneg_right hnum hL.le
    have hdenW := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 36 * w)
    nlinarith

  rw [hsplit]
  calc
    |(A - K) / d + K * (c - d) / (d * c)|
        ≤ |(A - K) / d| + |K * (c - d) / (d * c)| := abs_add_le _ _
    _ ≤ 4 * w / L + 36 * w / L := add_le_add hterm1 hterm2
    _ = 40 * w / L := by ring

/-- The concrete D-window normalization `a_D` is close to the scale-free
sharp normalization `a*_lam`. -/
lemma dutD_a_close_aStar
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    |(P.atD T).a T - ThmD.aStar P.lam| ≤ 4 * P.w / P.L T := by
  rw [ThmD.atD_a_eq_av hP T]
  unfold AdmWindow.av
  simpa [Params.phiD] using
    (ThmD.aD_close
      hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8)

/-- After multiplying by `L`, the two normalization denominators differ by
at most `4w`. -/
lemma dutD_denominator_close
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    |(P.atD T).a T * P.L T - ThmD.aStar P.lam * P.L T| ≤ 4 * P.w := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have h := dutD_a_close_aStar P hP h8
  rw [← sub_mul, abs_mul, abs_of_pos hL]
  calc
    |(P.atD T).a T - ThmD.aStar P.lam| * P.L T
        ≤ (4 * P.w / P.L T) * P.L T :=
      mul_le_mul_of_nonneg_right h hL.le
    _ = 4 * P.w := by
      exact div_mul_cancel₀ (4 * P.w) hL.ne'

/-- Under `16w <= L`, the sharp normalization stays uniformly positive:
`a*_lam >= 1/4`.  This is obtained from `a_D >= 1/2` and the `aD_close`
estimate rather than from a separate trigonometric integral bound. -/
lemma dutD_aStar_ge_quarter
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T) :
    1 / 4 ≤ ThmD.aStar P.lam := by
  have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
  have h8 : 8 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have haD : 1 / 2 ≤ (P.atD T).a T :=
    (ThmD.aD_range_of hP h8 h4pi).1
  have hclose := dutD_a_close_aStar P hP h8
  have herr : 4 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]
    nlinarith
  have hright := (abs_le.mp hclose).2
  linarith

/-- The raw sharp kernel is bounded by `9L/8` under `16w <= L`.  We get this
without separately integrating the sharp profile: the smooth raw kernel is
bounded by `L`, and the raw comparison costs `2w`. -/
lemma dutDSharpKernelRaw_abs_le
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h16 : 16 * P.w ≤ P.L T) (x : ℝ) :
    |dutDSharpKernelRaw P T x| ≤ 9 * P.L T / 8 := by
  have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
  have h8 : 8 * P.w ≤ P.L T := by linarith
  have hW := ThmD.admWindow_params hP h8
  have hfull : |dutDFullKernelRaw P T x| ≤ P.L T := by
    simpa [dutDFullKernelRaw] using hW.abs_VPhiR_le_L x
  have hclose := dutDFullKernelRaw_close_sharp P hP h8 x
  have htri :
      |dutDSharpKernelRaw P T x|
        ≤ |dutDFullKernelRaw P T x|
          + |dutDFullKernelRaw P T x - dutDSharpKernelRaw P T x| := by
    calc
      |dutDSharpKernelRaw P T x|
          =
          |dutDFullKernelRaw P T x
            + (dutDSharpKernelRaw P T x - dutDFullKernelRaw P T x)| := by
              congr 1
              ring
      _ ≤ |dutDFullKernelRaw P T x|
            + |dutDSharpKernelRaw P T x - dutDFullKernelRaw P T x| :=
          abs_add_le _ _
      _ =
          |dutDFullKernelRaw P T x|
            + |dutDFullKernelRaw P T x - dutDSharpKernelRaw P T x| := by
          rw [abs_sub_comm]
  calc
    |dutDSharpKernelRaw P T x|
        ≤ |dutDFullKernelRaw P T x|
          + |dutDFullKernelRaw P T x - dutDSharpKernelRaw P T x| := htri
    _ ≤ P.L T + 2 * P.w := add_le_add hfull hclose
    _ ≤ 9 * P.L T / 8 := by nlinarith

/-- **Normalized full-Poisson to sharp-cosine comparison.**

For the concrete Theorem-D window, once `L` is large relative to the fixed
ramp width `w`, the normalized exact full-grid kernel differs uniformly from
the normalized hard-cutoff cosine kernel by at most `40 w / L`.

The constant is intentionally loose; the important feature for the DUT
endgame is the explicit `O(w/L)` decay. -/
theorem dutDFullKernel_close_sharp
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (x : ℝ) :
    |dutDFullKernel P T x - dutDSharpKernel P T x|
      ≤ 40 * P.w / P.L T := by
  have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
  have h8 : 8 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have haD : 1 / 2 ≤ (P.atD T).a T :=
    (ThmD.aD_range_of hP h8 h4pi).1
  have haStar : 1 / 4 ≤ ThmD.aStar P.lam :=
    dutD_aStar_ge_quarter P hP h16 h4pi
  have hd :
      P.L T / 2 ≤ (P.atD T).a T * P.L T := by
    have := mul_le_mul_of_nonneg_right haD hL.le
    nlinarith
  have hc :
      P.L T / 4 ≤ ThmD.aStar P.lam * P.L T := by
    have := mul_le_mul_of_nonneg_right haStar hL.le
    nlinarith
  have hraw :=
    dutDFullKernelRaw_close_sharp P hP h8 x
  have hsharp :=
    dutDSharpKernelRaw_abs_le P hP h16 x
  have hden :=
    dutD_denominator_close P hP h8

  unfold dutDFullKernel dutDSharpKernel
  exact
    dut_quotient_close_40
      hL hw0 h16 hd hc hraw hsharp hden

end Zeta23.ZeroSide.RankTraceMult
