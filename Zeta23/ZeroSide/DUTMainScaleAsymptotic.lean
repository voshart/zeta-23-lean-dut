/-
DUTMainScaleAsymptotic.lean

Asymptotic conversion of the deterministic DUT span term.

The global DUT saving contains
  (P.L T / (2*pi)) * T.
Since P.L T = P.lam * l T and Riemann--von Mangoldt gives
  N(T,2T) = T/(2*pi) * ell1(T) + O(log T),
with ell1(T) = l(T) + O(1), we have

  (P.L T / (2*pi)) * T - P.lam * N(T,2T) = o(N(T,2T)).

This is the exact scale conversion needed by the final DUT endgame.

Intended location:
  Zeta23/ZeroSide/DUTMainScaleAsymptotic.lean
-/

import Zeta23.Assembly
import Zeta23.ZeroSide.DUTCoreBoundaryAsymptotic

noncomputable section
set_option linter.unusedSectionVars false

open Filter Asymptotics Topology Real
open scoped Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- `T = o(T l(T))`. -/
private lemma dut_isLittleO_T_Tl :
    (fun T : ℝ => T)
      =o[atTop]
    (fun T : ℝ => T * l T) := by
  have hlTop : Tendsto (fun T : ℝ => l T) atTop atTop := by
    have hlog :
        Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_id.atTop_div_const (by positivity))
    exact hlog.congr fun T => by simp [l]
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [
    hlTop.eventually_ge_atTop c⁻¹,
    eventually_gt_atTop (0 : ℝ)
  ] with T hl hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hT, abs_of_pos (mul_pos hT (lt_of_lt_of_le (inv_pos.mpr hc) hl))]
  have h1 : 1 ≤ c * l T := by
    have h :=
      mul_le_mul_of_nonneg_left hl hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at h
  nlinarith [mul_nonneg hT.le (sub_nonneg.mpr h1)]

/-- The Riemann--von Mangoldt residual is `o(N)`. -/
private lemma dut_rvmResidual_isLittleO_N
    (Z : ZeroConfig) (H : PaperInputs Z) :
    (fun T : ℝ =>
        (Z.N T (2 * T) : ℝ)
          - T / (2 * Real.pi) * ell1 T)
      =o[atTop]
    (fun T : ℝ => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main

  have hO :
      (fun T : ℝ =>
          (Z.N T (2 * T) : ℝ)
            - T / (2 * Real.pi) * ell1 T)
        =O[atTop]
      Real.log := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards [
      eventually_ge_atTop T₀,
      Assembly.eventually_log_nonneg
    ] with T hT hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hlog]
    exact
      (hRvM T hT).trans
        (mul_le_mul_of_nonneg_right
          (le_abs_self C) hlog)

  exact
    hO.trans_isLittleO
      (Assembly.isLittleO_N_of_isLittleO_Tl
        Z H.RvM Assembly.isLittleO_log_Tl)

/-- The deterministic length scale differs from `λ N(T,2T)` by `o(N)`:
`(L/(2π))T = λ N + o(N)`. -/
theorem dutMainLength_sub_lamN_isLittleO_N
    (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) :
    (fun T : ℝ =>
        (P.L T / (2 * Real.pi)) * T
          - P.lam * (Z.N T (2 * T) : ℝ))
      =o[atTop]
    (fun T : ℝ => (Z.N T (2 * T) : ℝ)) := by
  let N : ℝ → ℝ :=
    fun T => (Z.N T (2 * T) : ℝ)

  have hres :
      (fun T : ℝ =>
          (Z.N T (2 * T) : ℝ)
            - T / (2 * Real.pi) * ell1 T)
        =o[atTop] N := by
    simpa [N] using
      dut_rvmResidual_isLittleO_N Z H

  have hTN :
      (fun T : ℝ => T)
        =o[atTop] N := by
    exact
      Assembly.isLittleO_N_of_isLittleO_Tl
        Z H.RvM dut_isLittleO_T_Tl

  have hcorr :
      (fun T : ℝ =>
          ((1 - 2 * Real.log 2) / (2 * Real.pi)) * T)
        =o[atTop] N :=
    hTN.const_mul_left
      ((1 - 2 * Real.log 2) / (2 * Real.pi))

  have hneg :
      (fun T : ℝ =>
          -((Z.N T (2 * T) : ℝ)
              - T / (2 * Real.pi) * ell1 T))
        =o[atTop] N := by
    have hh := hres.const_mul_left (-1 : ℝ)
    simpa only [neg_mul, one_mul] using hh

  have hsum :
      (fun T : ℝ =>
          -((Z.N T (2 * T) : ℝ)
              - T / (2 * Real.pi) * ell1 T)
            + ((1 - 2 * Real.log 2) / (2 * Real.pi)) * T)
        =o[atTop] N :=
    hneg.add hcorr

  have hlam :=
    hsum.const_mul_left P.lam

  refine
    (hlam.congr_left ?_).congr_right ?_
  · intro T
    simp only [Params.L, Assembly.ell1_eq, Assembly.c₀]
    ring
  · intro T
    rfl

end Zeta23.ZeroSide.RankTraceMult
