/-
DUTVerifierFinalSeam.lean

Final logical seam matching the actual external search domain.

The Arb verifier searches only six-point configurations whose normalized
span is at most dutVerifierR = 9.45.  Lean's pair certificate is stated for
all strictly increasing six-tuples using

  dutEta * max (dutVerifierR - span) 0.

This module proves these formulations equivalent: beyond the verifier cutoff
the RHS vanishes and the 15-pair square energy is automatically nonnegative.

No external numerical assertion occurs here.
-/

import Zeta23.ZeroSide.DUTVerifierEnergyBridge

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The scalar 15-pair energy is nonnegative. -/
theorem dutScaleFreePairEnergy_nonneg
    (lam : ℝ) (x : Fin 6 → ℝ) :
    0 ≤ dutScaleFreePairEnergy lam x := by
  unfold dutScaleFreePairEnergy
  positivity

/-- Exact span-restricted statement searched by the external verifier after
passing from five nonnegative consecutive gaps to the associated ordered
six-tuple.

Only configurations with span at most `dutVerifierR` need computation. -/
def DUTScaleFreeSpanCertificate (lam : ℝ) : Prop :=
  ∀ x : Fin 6 → ℝ, StrictMono x →
    x 5 - x 0 ≤ dutVerifierR →
      dutEta * (x 5 - x 0)
          + dutScaleFreePairEnergy lam x
        ≥ dutEta * dutVerifierR

/-- The span-restricted external-search statement is exactly equivalent to
Lean's all-span positive-part certificate. -/
theorem dutScaleFreeSpanCertificate_iff_pairCertificate
    (lam : ℝ) :
    DUTScaleFreeSpanCertificate lam
      ↔ DUTScaleFreePairCertificate lam := by
  constructor
  · intro hspanCert x hx
    by_cases hcut : x 5 - x 0 ≤ dutVerifierR
    · have h := hspanCert x hx hcut
      rw [dutVerifierCertificateRhs]
      rw [max_eq_left (by linarith)]
      linarith
    · have hge : dutVerifierR ≤ x 5 - x 0 := le_of_not_ge hcut
      rw [dutVerifierCertificateRhs]
      rw [max_eq_right (by linarith)]
      simp only [mul_zero]
      exact dutScaleFreePairEnergy_nonneg lam x
  · intro hpair x hx hcut
    have h := hpair x hx
    rw [dutVerifierCertificateRhs] at h
    rw [max_eq_left (by linarith)] at h
    linarith

/-- Concrete fixed-lambda form of the exact span-domain proposition searched
by the successful Arb run. -/
def DUTFixedScaleFreeSpanCertificate : Prop :=
  DUTScaleFreeSpanCertificate dutVerifierLam

/-- The exact external search-domain proposition supplies the scalar pair
certificate used by the already-built energy bridge. -/
theorem dutFixedPairCertificate_of_spanCertificate
    (hcert : DUTFixedScaleFreeSpanCertificate) :
    DUTScaleFreePairCertificate dutVerifierLam := by
  exact
    (dutScaleFreeSpanCertificate_iff_pairCertificate
      dutVerifierLam).mp hcert

/-- Final DUT headline with the external boundary expressed in the same
span-restricted form used by the Arb branch-and-bound search. -/
theorem dut_thmD₀_simple_6727918_of_span_certificate
    (hcert : DUTFixedScaleFreeSpanCertificate) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3363959 : ℝ) / 5000000 - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  exact
    dut_thmD₀_simple_6727918_of_pair_certificate
      (dutFixedPairCertificate_of_spanCertificate hcert)

end Zeta23.ZeroSide.RankTraceMult
