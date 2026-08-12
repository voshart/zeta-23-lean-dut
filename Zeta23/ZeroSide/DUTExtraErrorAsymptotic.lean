/-
DUTExtraErrorAsymptotic.lean

Package the three DUT-only error terms in the global self-bootstrap:

  dutQ * boundary(T)
  + 5 * dutQ
  + 5 * dutBeta * ((L(T)/(2*pi))*T - lam*N(T,2T)).

The boundary and main-scale drift were proved separately; the fixed constant
is o(N) because N(T,2T) -> infinity.

Intended location:
  Zeta23/ZeroSide/DUTExtraErrorAsymptotic.lean
-/

import Zeta23.ZeroSide.DUTSelfBootstrap
import Zeta23.ZeroSide.DUTMainScaleAsymptotic

noncomputable section
set_option linter.unusedSectionVars false

open Filter Asymptotics Topology Real
open scoped Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Any fixed real constant is `o(N)` once `N -> +∞`. -/
private lemma dut_const_isLittleO_of_tendsto_atTop
    (N : ℝ → ℝ)
    (hNtop : Tendsto N atTop atTop)
    (C : ℝ) :
    (fun _ : ℝ => C) =o[atTop] N := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [
    hNtop.eventually_ge_atTop (|C| / c)
  ] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hquot0 : 0 ≤ |C| / c :=
    div_nonneg (abs_nonneg C) hc.le
  have hN0 : 0 ≤ N T := hquot0.trans hT
  rw [abs_of_nonneg hN0]
  calc
    |C| = c * (|C| / c) := by
      field_simp [hc.ne']
    _ ≤ c * N T :=
      mul_le_mul_of_nonneg_left hT hc.le

/-- All error terms introduced specifically by the DUT self-bootstrap are
negligible compared with the main dyadic zero count. -/
theorem dutExtraError_isLittleO_N
    (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) :
    (fun T : ℝ =>
        dutQ * (dutCoreBoundaryN Z T : ℝ)
          + 5 * dutQ
          + 5 * dutBeta *
              ((P.L T / (2 * Real.pi)) * T
                - P.lam * (Z.N T (2 * T) : ℝ)))
      =o[atTop]
    (fun T : ℝ => (Z.N T (2 * T) : ℝ)) := by
  let N : ℝ → ℝ :=
    fun T => (Z.N T (2 * T) : ℝ)

  have hNtop : Tendsto N atTop atTop := by
    simpa [N] using
      Assembly.tendsto_N_atTop Z H.RvM

  have hboundary :
      (fun T : ℝ =>
          dutQ * (dutCoreBoundaryN Z T : ℝ))
        =o[atTop] N := by
    have h :=
      (dutCoreBoundaryN_isLittleO_N Z H).const_mul_left dutQ
    simpa [N] using h

  have hconst :
      (fun _ : ℝ => 5 * dutQ)
        =o[atTop] N :=
    dut_const_isLittleO_of_tendsto_atTop
      N hNtop (5 * dutQ)

  have hlength :
      (fun T : ℝ =>
          5 * dutBeta *
            ((P.L T / (2 * Real.pi)) * T
              - P.lam * (Z.N T (2 * T) : ℝ)))
        =o[atTop] N := by
    have h :=
      (dutMainLength_sub_lamN_isLittleO_N Z H P).const_mul_left
        (5 * dutBeta)
    simpa [N] using h

  exact (hboundary.add hconst).add hlength

end Zeta23.ZeroSide.RankTraceMult
