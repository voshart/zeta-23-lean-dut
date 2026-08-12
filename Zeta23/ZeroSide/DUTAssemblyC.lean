/-
DUTAssemblyC.lean

Window-general fixed-T algebra for the strengthened DUT Assembly seam.

This is the simple-zero/DUT-saving analogue of
  Zeta23.ThmD.N0star_lower_c.

It is the correct algebraic interface for the Montgomery--Taylor endgame:
the coefficient `cinv` will later be instantiated by

  (ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹.

No asymptotics occur here.

Intended location:
  Zeta23/ZeroSide/DUTAssemblyC.lean
-/

import Zeta23.ZeroSide.DUTAssemblyBootstrap
import Zeta23.ThmD.AssemblyD

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Strengthened window-general fixed-T rank-trace algebra.

Compared with `ThmD.N0star_lower_c`, the target is an arbitrary `N0s`
and an additive saving `S` is preserved unchanged. -/
theorem dut_N0s_lower_c_with_saving
    {N0s N NII trGh frGh B cinv R₁ R₂ S : ℝ}
    (hB : 0 ≤ B)
    (h0 :
      4 * trGh - frGh - 2 * N - 3 * NII
        - B * (4 + 2 * Real.sqrt frGh + B)
        + S
        ≤ N0s)
    (htr : |trGh - N| ≤ R₁)
    (hfr : frGh ≤ cinv * N + R₂) :
    (2 - cinv) * N
        - (4 * R₁ + R₂ + 3 * NII
          + B * (4 + 2 * Real.sqrt (cinv * N + R₂) + B))
        + S
      ≤ N0s := by
  have h1 : N - R₁ ≤ trGh := by
    have := (abs_le.mp htr).1
    linarith
  have h2 :
      Real.sqrt frGh ≤ Real.sqrt (cinv * N + R₂) :=
    Real.sqrt_le_sqrt hfr
  nlinarith [
    h0, h1, h2, hB,
    mul_le_mul_of_nonneg_left h2 hB
  ]

end Zeta23.ZeroSide.RankTraceMult
