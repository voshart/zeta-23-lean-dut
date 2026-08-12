/-
DUTCoreBoundaryAsymptotic.lean

Asymptotic closure of the two interior boundary strips removed by the DUT core.

From DUTCoreBoundary:
  boundary(T)
    <= NII(T + sqrt T) + NII(2T).

Using Tail.NII_le at the two shifted heights and deliberately coarse scale
comparisons, eventually

  boundary(T) <= 72 A0 * sqrt(T) * l(T).

The exact constant is irrelevant.  Upstream Assembly already proves
  sqrt(T) * l(T) = o(T*l(T))
and
  o(T*l(T)) ⊆ o(N(T,2T))
under Riemann--von Mangoldt.  Therefore the discarded DUT boundary is o(N).

Intended location:
  Zeta23/ZeroSide/DUTCoreBoundaryAsymptotic.lean
-/

import Zeta23.ZeroSide.DUTCoreBoundary

noncomputable section
set_option linter.unusedSectionVars false

open Filter
open scoped Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Coarse comparison for the scale `sqrt(U) * l(U)` when `T <= U <= 2T`. -/
private lemma dut_sqrt_mul_l_shift_le
    {T U : ℝ}
    (hT1 : 1 ≤ T)
    (hl1 : 1 ≤ l T)
    (hlogT : Real.log T ≤ 2 * l T)
    (hTU : T ≤ U)
    (hU2 : U ≤ 2 * T) :
    Real.sqrt U * l U
      ≤ 6 * (Real.sqrt T * l T) := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hU : 0 < U := lt_of_lt_of_le hT hTU

  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hsU : 0 ≤ Real.sqrt U := Real.sqrt_nonneg U
  have hsT2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have hsU2 : Real.sqrt U ^ 2 = U := Real.sq_sqrt hU.le

  have hsqrt :
      Real.sqrt U ≤ 2 * Real.sqrt T := by
    nlinarith [sq_nonneg (Real.sqrt U - 2 * Real.sqrt T)]

  have hlog2pi :
      0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]

  have hlU_logU :
      l U ≤ Real.log U := by
    rw [l, Real.log_div hU.ne' (by positivity)]
    linarith

  have hlogU2 :
      Real.log U ≤ Real.log (2 * T) := by
    exact Real.log_le_log hU hU2

  have hlog2 :
      Real.log 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]

  have hlog2T :
      Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne']

  have hlU :
      l U ≤ 3 * l T := by
    rw [hlog2T] at hlogU2
    linarith

  calc
    Real.sqrt U * l U
        ≤ Real.sqrt U * (3 * l T) :=
      mul_le_mul_of_nonneg_left hlU hsU
    _ ≤ (2 * Real.sqrt T) * (3 * l T) := by
      exact
        mul_le_mul_of_nonneg_right hsqrt
          (by linarith : 0 ≤ 3 * l T)
    _ = 6 * (Real.sqrt T * l T) := by ring

/-- `T + sqrt(T)` lies between `T` and `2T` for `T >= 1`. -/
private lemma dut_shift1_between
    {T : ℝ} (hT1 : 1 ≤ T) :
    T ≤ T + D0 T ∧ T + D0 T ≤ 2 * T := by
  have hT : 0 ≤ T := by linarith
  have hD0 : 0 ≤ D0 T := by simp [D0]
  have hDsq : D0 T ^ 2 = T := by
    simp [D0, Real.sq_sqrt hT]
  have hD1 : 1 ≤ D0 T := by
    unfold D0
    rw [Real.le_sqrt (by norm_num) hT]
    norm_num
    exact hT1
  have hDle : D0 T ≤ T := by
    nlinarith
  constructor <;> linarith

/-- Both shifted boundary scales are eventually bounded by six times the
unshifted `sqrt(T) * l(T)` scale. -/
private lemma dut_shifted_boundary_scales_eventually :
    ∀ᶠ T : ℝ in atTop,
      Real.sqrt (T + D0 T) * l (T + D0 T)
          ≤ 6 * (Real.sqrt T * l T)
      ∧
      Real.sqrt (2 * T) * l (2 * T)
          ≤ 6 * (Real.sqrt T * l T) := by
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    Assembly.eventually_one_le_l,
    Assembly.eventually_log_le_two_l
  ] with T hT1 hl1 hlogT
  have hbetween := dut_shift1_between hT1
  constructor
  · exact
      dut_sqrt_mul_l_shift_le
        hT1 hl1 hlogT hbetween.1 hbetween.2
  · exact
      dut_sqrt_mul_l_shift_le
        hT1 hl1 hlogT
        (by linarith)
        le_rfl

/-- Explicit eventual big-O bound for the two discarded core strips. -/
theorem dutCoreBoundaryN_eventually_le
    (Z : ZeroConfig) (H : PaperInputs Z) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ᶠ T : ℝ in atTop,
        (dutCoreBoundaryN Z T : ℝ)
          ≤ 72 * A₀ * Real.sqrt T * l T := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  refine ⟨A₀, hA₀, ?_⟩

  filter_upwards [
    eventually_ge_atTop (Tail.T₀ : ℝ),
    Assembly.eventually_one_le_l,
    Assembly.eventually_log_le_two_l,
    dut_shifted_boundary_scales_eventually
  ] with T hTT0 hl1 hlogT hscale

  have hT0 : 0 ≤ T := by
    have hp := Tail.T₀_pos
    linarith

  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ Tail.T₀ := by norm_num [Tail.T₀]
    linarith

  have hbetween := dut_shift1_between hT1

  let U₁ : ℝ := T + D0 T
  let U₂ : ℝ := 2 * T

  have hU1T0 : Tail.T₀ ≤ U₁ := by
    dsimp [U₁]
    exact hTT0.trans hbetween.1

  have hU2T0 : Tail.T₀ ≤ U₂ := by
    dsimp [U₂]
    linarith

  have hN1 :=
    Tail.NII_le Z hA₀ hloc hU1T0
  have hN2 :=
    Tail.NII_le Z hA₀ hloc hU2T0

  have hlog1 :=
    Tail.log_four_mul_le_two_mul_l hU1T0
  have hlog2 :=
    Tail.log_four_mul_le_two_mul_l hU2T0

  have hA0nonneg : 0 ≤ A₀ := by linarith

  have hN1' :
      (Assembly.NII Z U₁ : ℝ)
        ≤ 6 * A₀ * (Real.sqrt U₁ * l U₁) := by
    have hfac : 0 ≤ 3 * A₀ * Real.sqrt U₁ := by
      positivity
    dsimp only [U₁] at hN1 hlog1 ⊢
    nlinarith

  have hN2' :
      (Assembly.NII Z U₂ : ℝ)
        ≤ 6 * A₀ * (Real.sqrt U₂ * l U₂) := by
    have hfac : 0 ≤ 3 * A₀ * Real.sqrt U₂ := by
      positivity
    dsimp only [U₂] at hN2 hlog2 ⊢
    nlinarith

  have hscale1 :
      Real.sqrt U₁ * l U₁
        ≤ 6 * (Real.sqrt T * l T) := by
    simpa [U₁] using hscale.1

  have hscale2 :
      Real.sqrt U₂ * l U₂
        ≤ 6 * (Real.sqrt T * l T) := by
    simpa [U₂] using hscale.2

  have hN1'' :
      (Assembly.NII Z U₁ : ℝ)
        ≤ 36 * A₀ * (Real.sqrt T * l T) := by
    calc
      (Assembly.NII Z U₁ : ℝ)
          ≤ 6 * A₀ * (Real.sqrt U₁ * l U₁) := hN1'
      _ ≤ 6 * A₀ * (6 * (Real.sqrt T * l T)) := by
        exact
          mul_le_mul_of_nonneg_left hscale1
            (by positivity : 0 ≤ 6 * A₀)
      _ = 36 * A₀ * (Real.sqrt T * l T) := by ring

  have hN2'' :
      (Assembly.NII Z U₂ : ℝ)
        ≤ 36 * A₀ * (Real.sqrt T * l T) := by
    calc
      (Assembly.NII Z U₂ : ℝ)
          ≤ 6 * A₀ * (Real.sqrt U₂ * l U₂) := hN2'
      _ ≤ 6 * A₀ * (6 * (Real.sqrt T * l T)) := by
        exact
          mul_le_mul_of_nonneg_left hscale2
            (by positivity : 0 ≤ 6 * A₀)
      _ = 36 * A₀ * (Real.sqrt T * l T) := by ring

  have hboundaryNat :=
    dutCoreBoundaryN_le_shifted_NII Z T hT0

  have hboundary :
      (dutCoreBoundaryN Z T : ℝ)
        ≤ (Assembly.NII Z U₁ : ℝ)
          + (Assembly.NII Z U₂ : ℝ) := by
    dsimp [U₁, U₂]
    exact_mod_cast hboundaryNat

  linarith

/-- The two discarded `sqrt(T)` strips are negligible compared with the main
dyadic zero count. -/
theorem dutCoreBoundaryN_isLittleO_N
    (Z : ZeroConfig) (H : PaperInputs Z) :
    (fun T : ℝ => (dutCoreBoundaryN Z T : ℝ))
      =o[atTop]
    (fun T : ℝ => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hbound⟩ :=
    dutCoreBoundaryN_eventually_le Z H

  have hbig :
      (fun T : ℝ => (dutCoreBoundaryN Z T : ℝ))
        =O[atTop]
      (fun T : ℝ => Real.sqrt T * l T) := by
    refine Asymptotics.IsBigO.of_bound (72 * A₀) ?_
    filter_upwards [
      hbound,
      eventually_ge_atTop (0 : ℝ),
      Assembly.eventually_l_pos
    ] with T hb hT hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hboundary0 :
        0 ≤ (dutCoreBoundaryN Z T : ℝ) :=
      Nat.cast_nonneg _
    have hscale0 :
        0 ≤ Real.sqrt T * l T := by positivity
    rw [abs_of_nonneg hboundary0, abs_of_nonneg hscale0]
    simpa [mul_assoc] using hb

  have hTl :
      (fun T : ℝ => (dutCoreBoundaryN Z T : ℝ))
        =o[atTop]
      (fun T : ℝ => T * l T) :=
    hbig.trans_isLittleO Assembly.isLittleO_sqrt_mul_l_Tl

  exact
    Assembly.isLittleO_N_of_isLittleO_Tl
      Z H.RvM hTl

end Zeta23.ZeroSide.RankTraceMult
