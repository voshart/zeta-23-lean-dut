/-
DUTHeadlineNumeric.lean

Kernel-checked rational lower bound for the exact DUT headline rate.

No floating-point computation is trusted here.  We bound sin/cos at
u = 1/sqrt(2) by:
  * applying Mathlib's polynomial `Complex.sin_bound` / `Complex.cos_bound`
    at x0 = u/16, where x0^2 = 1/512;
  * propagating a rational interval enclosure through four exact
    double-angle steps.

The resulting rational enclosure is strong enough to prove

  0.6727918 < dutHeadlineRate.

Intended location:
  Zeta23/ZeroSide/DUTHeadlineNumeric.lean
-/

import Zeta23.ZeroSide.DUTFinalHeadline
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
set_option linter.unusedSectionVars false

open Filter Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

private structure DUTTrigState where
  q : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/-- Initial rational enclosure coefficients at x0 = 1/(16 sqrt 2).
The meanings are
  x0*a ≤ sin x0 ≤ x0*b
and
  c ≤ cos x0 ≤ d,
with x0^2 = q = 1/512.
-/
private def dutTrigInit : DUTTrigState where
  q := 1 / 512
  a := 78617597 / 78643200
  b := 78617603 / 78643200
  c := 25141243 / 25165824
  d := 25141253 / 25165824

/-- Exact interval propagation under x ↦ 2x. -/
private def dutTrigStep (s : DUTTrigState) : DUTTrigState where
  q := 4 * s.q
  a := s.a * s.c
  b := s.b * s.d
  c := 1 - 2 * s.q * s.b ^ 2
  d := 1 - 2 * s.q * s.a ^ 2

private structure DUTTrigBox (x : ℝ) (s : DUTTrigState) : Prop where
  hx0 : 0 ≤ x
  hx2 : x ^ 2 = s.q
  hq0 : 0 ≤ s.q
  ha0 : 0 ≤ s.a
  hb0 : 0 ≤ s.b
  hc0 : 0 ≤ s.c
  sin_lo : x * s.a ≤ Real.sin x
  sin_hi : Real.sin x ≤ x * s.b
  cos_lo : s.c ≤ Real.cos x
  cos_hi : Real.cos x ≤ s.d

private lemma dutTrigBox_double
    {x : ℝ} {s : DUTTrigState}
    (h : DUTTrigBox x s)
    (hcnext : 0 ≤ (dutTrigStep s).c) :
    DUTTrigBox (2 * x) (dutTrigStep s) := by
  have hsin0 : 0 ≤ Real.sin x :=
    le_trans (mul_nonneg h.hx0 h.ha0) h.sin_lo
  have hcos0 : 0 ≤ Real.cos x :=
    le_trans h.hc0 h.cos_lo
  have hd0 : 0 ≤ s.d :=
    hcos0.trans h.cos_hi

  have hprod_lo :
      (x * s.a) * s.c ≤ Real.sin x * Real.cos x :=
    mul_le_mul h.sin_lo h.cos_lo h.hc0 hsin0

  have hprod_hi :
      Real.sin x * Real.cos x ≤ (x * s.b) * s.d :=
    mul_le_mul h.sin_hi h.cos_hi hcos0
      (mul_nonneg h.hx0 h.hb0)

  have hsin_sq_hi :
      Real.sin x ^ 2 ≤ (x * s.b) ^ 2 :=
    pow_le_pow_left₀ hsin0 h.sin_hi 2

  have hsin_sq_lo :
      (x * s.a) ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h.hx0 h.ha0) h.sin_lo 2

  have hxb_sq :
      (x * s.b) ^ 2 = s.q * s.b ^ 2 := by
    rw [mul_pow, h.hx2]

  have hxa_sq :
      (x * s.a) ^ 2 = s.q * s.a ^ 2 := by
    rw [mul_pow, h.hx2]

  have hsin_sq_hi_q :
      Real.sin x ^ 2 ≤ s.q * s.b ^ 2 := by
    rw [← hxb_sq]
    exact hsin_sq_hi

  have hsin_sq_lo_q :
      s.q * s.a ^ 2 ≤ Real.sin x ^ 2 := by
    rw [← hxa_sq]
    exact hsin_sq_lo

  refine {
    hx0 := by
      exact mul_nonneg (by norm_num) h.hx0
    hx2 := by
      change (2 * x) ^ 2 = 4 * s.q
      nlinarith [h.hx2]
    hq0 := by
      change 0 ≤ 4 * s.q
      exact mul_nonneg (by norm_num) h.hq0
    ha0 := by
      change 0 ≤ s.a * s.c
      exact mul_nonneg h.ha0 h.hc0
    hb0 := by
      change 0 ≤ s.b * s.d
      exact mul_nonneg h.hb0 hd0
    hc0 := hcnext
    sin_lo := by
      change (2 * x) * (s.a * s.c) ≤ Real.sin (2 * x)
      rw [Real.sin_two_mul]
      nlinarith [hprod_lo]
    sin_hi := by
      change Real.sin (2 * x) ≤ (2 * x) * (s.b * s.d)
      rw [Real.sin_two_mul]
      nlinarith [hprod_hi]
    cos_lo := by
      change 1 - 2 * s.q * s.b ^ 2 ≤ Real.cos (2 * x)
      rw [Real.cos_two_mul_eq_one_sub]
      nlinarith [hsin_sq_hi_q]
    cos_hi := by
      change Real.cos (2 * x) ≤ 1 - 2 * s.q * s.a ^ 2
      rw [Real.cos_two_mul_eq_one_sub]
      nlinarith [hsin_sq_lo_q]
  }

/-- Exact certified numerical lower bound:
`dutHeadlineRate > 0.6727918`. -/
theorem dutHeadlineRate_gt_6727918 :
    (3363959 : ℝ) / 5000000 < dutHeadlineRate := by
  let u : ℝ := (Real.sqrt 2)⁻¹
  let x0 : ℝ := u / 16

  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hu0 : 0 < u := by
    dsimp [u]
    positivity

  have hu2 : u ^ 2 = (1 : ℝ) / 2 := by
    dsimp [u]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

  have hx0pos : 0 < x0 := by
    dsimp [x0]
    positivity

  have hx02 : x0 ^ 2 = (1 : ℝ) / 512 := by
    dsimp [x0]
    rw [div_pow, hu2]
    norm_num

  have hx0le1 : x0 ≤ 1 := by
    have hx0nonneg := hx0pos.le
    nlinarith [hx02, sq_nonneg (x0 - 1)]

  have hnorm : ‖(x0 : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hx0pos.le] using hx0le1

  have hsBoundC :=
    Complex.sin_bound (x := (x0 : ℂ)) hnorm
  have hcBoundC :=
    Complex.cos_bound (x := (x0 : ℂ)) hnorm

  have hnormx0 : ‖(x0 : ℂ)‖ = x0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0pos.le]

  have hre3 : ((x0 : ℂ) ^ 3).re = x0 ^ 3 := by
    simp [pow_succ]

  have hsRe :
      |Real.sin x0 - (x0 - x0 ^ 3 / 6)|
        ≤ ‖Complex.sin (x0 : ℂ) - ((x0 : ℂ) - (x0 : ℂ) ^ 3 / 6)‖ := by
    have h := Complex.abs_re_le_norm
      (Complex.sin (x0 : ℂ) - ((x0 : ℂ) - (x0 : ℂ) ^ 3 / 6))
    simpa [Complex.sin_ofReal_re, hre3] using h

  have hsBound :
      |Real.sin x0 - (x0 - x0 ^ 3 / 6)|
        ≤ x0 ^ 5 / 100 := by
    calc
      |Real.sin x0 - (x0 - x0 ^ 3 / 6)|
          ≤ ‖Complex.sin (x0 : ℂ) -
              ((x0 : ℂ) - (x0 : ℂ) ^ 3 / 6)‖ := hsRe
      _ ≤ ‖(x0 : ℂ)‖ ^ 5 / 100 := hsBoundC
      _ = x0 ^ 5 / 100 := by rw [hnormx0]

  have hre2 : ((x0 : ℂ) ^ 2).re = x0 ^ 2 := by
    simp [pow_succ]

  have hcRe :
      |Real.cos x0 - (1 - x0 ^ 2 / 2)|
        ≤ ‖Complex.cos (x0 : ℂ) - (1 - (x0 : ℂ) ^ 2 / 2)‖ := by
    have h := Complex.abs_re_le_norm
      (Complex.cos (x0 : ℂ) - (1 - (x0 : ℂ) ^ 2 / 2))
    simpa [Complex.cos_ofReal_re, hre2] using h

  have hcBound :
      |Real.cos x0 - (1 - x0 ^ 2 / 2)|
        ≤ x0 ^ 4 * (5 / 96) := by
    calc
      |Real.cos x0 - (1 - x0 ^ 2 / 2)|
          ≤ ‖Complex.cos (x0 : ℂ) -
              (1 - (x0 : ℂ) ^ 2 / 2)‖ := hcRe
      _ ≤ ‖(x0 : ℂ)‖ ^ 4 * (5 / 96) := hcBoundC
      _ = x0 ^ 4 * (5 / 96) := by rw [hnormx0]

  have hx03 : x0 ^ 3 = x0 * ((1 : ℝ) / 512) := by
    calc
      x0 ^ 3 = x0 * x0 ^ 2 := by ring
      _ = x0 * ((1 : ℝ) / 512) := by rw [hx02]

  have hx04 : x0 ^ 4 = ((1 : ℝ) / 512) ^ 2 := by
    calc
      x0 ^ 4 = (x0 ^ 2) ^ 2 := by ring
      _ = ((1 : ℝ) / 512) ^ 2 := by rw [hx02]

  have hx05 : x0 ^ 5 = x0 * (((1 : ℝ) / 512) ^ 2) := by
    calc
      x0 ^ 5 = x0 * (x0 ^ 2) ^ 2 := by ring
      _ = x0 * (((1 : ℝ) / 512) ^ 2) := by rw [hx02]

  have hslo0 :
      x0 * dutTrigInit.a ≤ Real.sin x0 := by
    have h := (abs_le.mp hsBound).1
    have heq :
        x0 * dutTrigInit.a
          = x0 - x0 ^ 3 / 6 - x0 ^ 5 / 100 := by
      rw [hx03, hx05]
      norm_num [dutTrigInit]
      ring
    rw [heq]
    linarith

  have hshi0 :
      Real.sin x0 ≤ x0 * dutTrigInit.b := by
    have h := (abs_le.mp hsBound).2
    have heq :
        x0 * dutTrigInit.b
          = x0 - x0 ^ 3 / 6 + x0 ^ 5 / 100 := by
      rw [hx03, hx05]
      norm_num [dutTrigInit]
      ring
    rw [heq]
    linarith

  have hclo0 :
      dutTrigInit.c ≤ Real.cos x0 := by
    have h := (abs_le.mp hcBound).1
    have heq :
        dutTrigInit.c
          = 1 - x0 ^ 2 / 2 - x0 ^ 4 * (5 / 96) := by
      rw [hx02, hx04]
      norm_num [dutTrigInit]
    rw [heq]
    linarith

  have hchi0 :
      Real.cos x0 ≤ dutTrigInit.d := by
    have h := (abs_le.mp hcBound).2
    have heq :
        dutTrigInit.d
          = 1 - x0 ^ 2 / 2 + x0 ^ 4 * (5 / 96) := by
      rw [hx02, hx04]
      norm_num [dutTrigInit]
    rw [heq]
    linarith

  have h0 : DUTTrigBox x0 dutTrigInit := by
    refine {
      hx0 := hx0pos.le
      hx2 := by simpa [dutTrigInit] using hx02
      hq0 := by norm_num [dutTrigInit]
      ha0 := by norm_num [dutTrigInit]
      hb0 := by norm_num [dutTrigInit]
      hc0 := by norm_num [dutTrigInit]
      sin_lo := hslo0
      sin_hi := hshi0
      cos_lo := hclo0
      cos_hi := hchi0
    }

  have h1 :
      DUTTrigBox (2 * x0) (dutTrigStep dutTrigInit) :=
    dutTrigBox_double h0 (by norm_num [dutTrigStep, dutTrigInit])

  have h2 :
      DUTTrigBox (2 * (2 * x0))
        (dutTrigStep (dutTrigStep dutTrigInit)) := by
    exact dutTrigBox_double h1
      (by norm_num [dutTrigStep, dutTrigInit])

  have h3 :
      DUTTrigBox (2 * (2 * (2 * x0)))
        (dutTrigStep (dutTrigStep (dutTrigStep dutTrigInit))) := by
    exact dutTrigBox_double h2
      (by norm_num [dutTrigStep, dutTrigInit])

  have h4 :
      DUTTrigBox (2 * (2 * (2 * (2 * x0))))
        (dutTrigStep
          (dutTrigStep
            (dutTrigStep
              (dutTrigStep dutTrigInit)))) := by
    exact dutTrigBox_double h3
      (by norm_num [dutTrigStep, dutTrigInit])

  let s4 :=
    dutTrigStep
      (dutTrigStep
        (dutTrigStep
          (dutTrigStep dutTrigInit)))

  have hx4 : 2 * (2 * (2 * (2 * x0))) = u := by
    dsimp [x0]
    ring

  have hsin :
      u * s4.a ≤ Real.sin u := by
    have hh := h4.sin_lo
    rw [hx4] at hh
    simpa [s4] using hh

  have hcos :
      Real.cos u ≤ s4.d := by
    have hh := h4.cos_hi
    rw [hx4] at hh
    simpa [s4] using hh

  have ha4pos : 0 < s4.a := by
    norm_num [s4, dutTrigStep, dutTrigInit]

  have hsinpos : 0 < Real.sin u :=
    lt_of_lt_of_le (mul_pos hu0 ha4pos) hsin

  let req : ℝ := 672493845343 / 1000000000000

  have hrat :
      s4.d < (3 / 2 - req) * s4.a := by
    norm_num [s4, dutTrigStep, dutTrigInit, req]

  have hcoef : 0 < 3 / 2 - req := by
    norm_num [req]

  have hcross :
      u * Real.cos u
        < (3 / 2 - req) * Real.sin u := by
    calc
      u * Real.cos u
          ≤ u * s4.d :=
        mul_le_mul_of_nonneg_left hcos hu0.le
      _ < u * ((3 / 2 - req) * s4.a) :=
        mul_lt_mul_of_pos_left hrat hu0
      _ = (3 / 2 - req) * (u * s4.a) := by ring
      _ ≤ (3 / 2 - req) * Real.sin u :=
        mul_le_mul_of_nonneg_left hsin hcoef.le

  have hratio :
      u * (Real.cos u / Real.sin u) < 3 / 2 - req := by
    calc
      u * (Real.cos u / Real.sin u)
          = (u * Real.cos u) / Real.sin u := by ring
      _ < 3 / 2 - req :=
        (div_lt_iff₀ hsinpos).2 hcross

  have hHD : req < ThmD.HD 1 := by
    rw [ThmD.HD_one]
    change req <
      3 / 2
        - u * (Real.cos u / Real.sin u)
    linarith

  have hrate :
      dutHeadlineRate
        =
      (ThmD.HD 1 - 9 / 8000)
        / (199577 / 200000) := by
    simp only [
      dutHeadlineRate, dutRate, dutNumer, dutDen, dutQ, dutBeta,
      dutEta, dutR, ThmD.HD, one_div
    ]
    ring

  rw [hrate]
  have hden : (0 : ℝ) < 199577 / 200000 := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num [req] at hHD ⊢
  linarith

/-- Fully explicit dyadic headline at 67.27918%, conditional only on the
uniform external DUT verifier contract. -/
theorem dut_thmD₀_simple_6727918
    (hcert :
      ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
        DUTSharpVerifierCertificate
          (paramsOf stdProfile lam)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3363959 : ℝ) / 5000000 - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    dut_thmD₀_simple hcert ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hmain := hT₀ T hT
  have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) :=
    Nat.cast_nonneg _
  have hcoef :
      (3363959 : ℝ) / 5000000 - ε
        ≤ dutHeadlineRate - ε := by
    linarith [dutHeadlineRate_gt_6727918]
  exact
    (mul_le_mul_of_nonneg_right hcoef hN0).trans hmain

end Zeta23.ZeroSide.RankTraceMult
