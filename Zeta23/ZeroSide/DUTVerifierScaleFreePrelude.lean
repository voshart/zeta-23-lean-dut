/-
DUTVerifierScaleFreePrelude.lean

Lean-side vocabulary for the successful external DUT six-point verifier.

The verifier was run at

  lambda = 999999999 / 1000000000

with the dimensionless kernel

  k_lambda(y) =
    (sinc(pi*y - theta(lambda)) + sinc(pi*y + theta(lambda)))
      / (2*sinc(theta(lambda)))

where theta(lambda) = lambda/sqrt(2).

This file deliberately does NOT assert the external computation as an axiom.
It only fixes the exact Lean-side formula and proves the normalization
aStar(lambda) = sinc(theta(lambda)).

Next module:
  prove that dutDSharpKernel at physical frequency x equals
  dutScaleFreeKernel at y = L*x/(2*pi).
-/

import Zeta23.ZeroSide.DUTFixedLambdaNumeric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Exact dimensionless kernel evaluated by the Arb verifier. -/
noncomputable def dutScaleFreeKernel (lam y : ℝ) : ℝ :=
  (Real.sinc (Real.pi * y - ThmD.theta lam)
      + Real.sinc (Real.pi * y + ThmD.theta lam))
    / (2 * Real.sinc (ThmD.theta lam))

/-- Anthropic's scale-free window normalization is exactly the sinc
normalization used by the verifier. -/
theorem dut_aStar_eq_sinc
    {lam : ℝ} (hlam : 0 < lam) :
    ThmD.aStar lam = Real.sinc (ThmD.theta lam) := by
  have htheta : ThmD.theta lam ≠ 0 :=
    ne_of_gt (ThmD.theta_pos hlam)
  rw [ThmD.aStar_eq hlam, Real.sinc_of_ne_zero htheta]
  unfold ThmD.theta
  have hsqrt : Real.sqrt 2 ≠ 0 := by
    positivity
  field_simp [hlam.ne', hsqrt]

/-- Scale a physical ordinate to the verifier's dimensionless coordinate. -/
noncomputable def dutVerifierCoord (L x : ℝ) : ℝ :=
  (L / (2 * Real.pi)) * x

/-- The scale-free sharp matrix corresponding to six dimensionless
ordinates. -/
noncomputable def dutScaleFreeSharpMatrix
    (lam : ℝ) (x : Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  fun j l => (dutScaleFreeKernel lam (x j - x l) : ℂ)

/-- Exact matrix-form statement that the external finite computation is
intended to establish.

No theorem of this proposition is asserted here: it remains the explicit
external-computation boundary until a Lean certificate checker is supplied. -/
def DUTScaleFreeSharpCertificate (lam : ℝ) : Prop :=
  ∀ x : Fin 6 → ℝ, StrictMono x →
    dutVerifierCertificateRhs (x 5 - x 0)
      ≤ dutGramEnergy (dutScaleFreeSharpMatrix lam x)

/-- The concrete scale-free proposition associated with the successful
fixed-lambda verifier run. -/
def DUTFixedScaleFreeSharpCertificate : Prop :=
  DUTScaleFreeSharpCertificate dutVerifierLam

end Zeta23.ZeroSide.RankTraceMult
