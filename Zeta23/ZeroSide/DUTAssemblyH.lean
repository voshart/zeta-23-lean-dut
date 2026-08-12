/-
DUTAssemblyH.lean

Pure fixed-T H(lambda_1) algebra for the strengthened DUT Assembly seam.

This mirrors Assembly.N0star_lower_H, but preserves an arbitrary additive
saving term S on the zero-side inequality.  Keeping this lemma abstract makes
the next splice small: DUTAssemblyBootstrap supplies S, while the existing
Assembly.seamB supplies the trace/Frobenius estimates.

Intended location:
  Zeta23/ZeroSide/DUTAssemblyH.lean
-/

import Zeta23.ZeroSide.DUTAssemblyBootstrap

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Strengthened version of `Assembly.N0star_lower_H` with an arbitrary
additive saving term `S` carried unchanged through the trace algebra. -/
theorem dut_N0s_lower_H_with_saving
    {N0s N NII trGh frGh B lam₁ R₁ R₂ S : ℝ}
    (hB : 0 ≤ B)
    (h0 :
      4 * trGh - frGh - 2 * N - 3 * NII
        - B * (4 + 2 * Real.sqrt frGh + B)
        + S
        ≤ N0s)
    (htr : |trGh - N| ≤ R₁)
    (hfr :
      frGh
        ≤ (1 / lam₁ + lam₁ / 3) * N + R₂) :
    Hfun lam₁ * N
        - (4 * R₁ + R₂ + 3 * NII
          + B * (4 + 2 * Real.sqrt
              ((1 / lam₁ + lam₁ / 3) * N + R₂) + B))
        + S
      ≤ N0s := by
  have h1 : N - R₁ ≤ trGh := by
    have := (abs_le.mp htr).1
    linarith
  have h2 :
      Real.sqrt frGh
        ≤ Real.sqrt ((1 / lam₁ + lam₁ / 3) * N + R₂) :=
    Real.sqrt_le_sqrt hfr
  have h3 :
      Hfun lam₁ * N
        = 4 * N - (1 / lam₁ + lam₁ / 3) * N - 2 * N := by
    simp only [Hfun]
    ring
  nlinarith [
    h0, h1, h2, h3, hB,
    mul_le_mul_of_nonneg_left h2 hB
  ]

end Zeta23.ZeroSide.RankTraceMult
