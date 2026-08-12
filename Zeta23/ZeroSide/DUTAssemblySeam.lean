/-
DUTAssemblySeam.lean

Carry the averaged DUT saving from the concrete hat(A_z) inequality through
Anthropic's existing tail perturbation and window-counting seam.

The c=2 DUT inequality lands in s1, so the natural global target is the
simple critical-line count N0s(T,2T), using Assembly.s1_le.

No new analytic estimate occurs here: the DUT saving is transported additively
through Assembly.four_tr_sub_frobSq_perturb, while NIprime and the boundary
strip are handled by the existing Assembly bookkeeping.

Intended location:
  Zeta23/ZeroSide/DUTAssemblySeam.lean
-/

import Zeta23.Assembly
import Zeta23.ZeroSide.DUTHatAzPhase

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/--
Strengthened concrete Assembly seam for simple critical-line zeros.

This is the DUT analogue of `Assembly.seamA`, but it starts from the stronger
c=2 inequality

  4 tr Â - ||Â||_F^2 - 2 N(I') + dutCoreAveragedSaving <= s1,

and therefore closes against `Assembly.s1_le` to `N0s(T,2T)`.
-/
theorem dut_seamA_N0s
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT : 0 ≤ T)
    {θ₀ : ℝ}
    (hTl : Assembly.TailInputs Z (P.atD T) T θ₀)
    (ha : 0 < (P.atD T).a T)
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (hcNorm : 0 < dutPhaseNormC T P)
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
  have hL' : 0 < (P.atD T).L T := by
    simpa using hL

  have hcore :=
    dut_hatAz_mult2_of_phase_average
      Z T P (dutD_phiHatConj P T)
      hL hs6 hcNorm hrep

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
