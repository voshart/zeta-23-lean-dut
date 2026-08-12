/-
DUTAssemblySeamAllCore.lean

All-core strengthened Assembly seam.

This is the same tail/counting splice as DUTAssemblySeam, but its zero-side
input is `dut_hatAz_mult2_all_core`, so there is no hypothesis
`6 ≤ dutCoreCount Z T`.

Intended location:
  Zeta23/ZeroSide/DUTAssemblySeamAllCore.lean
-/

import Zeta23.Assembly
import Zeta23.ZeroSide.DUTCoreFallback

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Strengthened concrete Assembly seam for simple critical-line zeros,
valid for every core size. -/
theorem dut_seamA_N0s_all_core
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hP : P.Valid)
    (hT : 0 ≤ T)
    {θ₀ : ℝ}
    (hTl : Assembly.TailInputs Z (P.atD T) T θ₀)
    (ha : 0 < (P.atD T).a T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hrep :
      ∀ r ∈ Finset.range 6,
        DUTPhaseReplacementResult Z T P r) :
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
      - frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
      - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / ((P.atD T).a T * (P.atD T).L T) *
          (4 + 2 * Real.sqrt
            (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
            + θ₀ / ((P.atD T).a T * (P.atD T).L T))
      + dutCoreAveragedSaving Z T P
      ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hL : 0 < P.L T := by
    have hw : 0 < P.w := by
      linarith [hP.one_le_w]
    have h8w : 0 < 8 * P.w := by positivity
    linarith

  have hL' : 0 < (P.atD T).L T := by
    simpa using hL

  have hcore :=
    dut_hatAz_mult2_all_core
      Z T P hP hT h8 h4pi hrep

  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat

  have hGAE :
      (P.atD T).hat T (Z.Gz (P.atD T) T)
        = (P.atD T).hat T (Z.Az (P.atD T) T)
          + (P.atD T).hat T (Z.Ez (P.atD T) T) := by
    rw [← Assembly.hat_add]
    congr 1
    simp only [ZeroConfig.Ez]
    abel

  have hB₀ :
      0 ≤ θ₀ / ((P.atD T).a T * (P.atD T).L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL').le

  have hpert :=
    Assembly.four_tr_sub_frobSq_perturb
      hGAE hB₀ (htrE.trans hBle)
      (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))

  have hcount :
      (Z.s1 T : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ)
          + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.s1_le Z hT

  have hNI :
      (Z.NIprime T : ℝ)
        = (Z.N T (2 * T) : ℝ)
          + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT

  rw [hNI] at hcore
  linarith [hcore, hpert, hcount]

end Zeta23.ZeroSide.RankTraceMult
