/-
DUTFinalOneCertificate.lean

Minimal finish-line interfaces for the DUT theorem.

The previous lambda->1 headline theorem asked for verifier certificates
uniformly for every lambda in [1/2,1).  That is much stronger than needed.

This file exposes two weaker interfaces:

1. `DUTHeadlineVerifierApproach`: certificates only along values of lambda
   whose DUT rates approach the headline rate.

2. For any explicit target q, a *single* lambda/certificate suffices as soon
   as Lean proves q < dutRate (cStar lambda) lambda.

In particular, 67.27918% needs only one suitable certified lambda.

Intended location:
  Zeta23/ZeroSide/DUTFinalOneCertificate.lean
-/

import Zeta23.ZeroSide.DUTFinalLam
import Zeta23.ZeroSide.DUTHeadlineNumeric

noncomputable section
set_option linter.unusedSectionVars false

open Filter Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Minimal asymptotic certificate interface: for every requested rate
accuracy, it is enough to have one admissible lambda carrying a verifier
certificate and whose DUT rate is that close to the limiting headline rate. -/
def DUTHeadlineVerifierApproach : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ lam : ℝ,
      1 / 2 ≤ lam ∧
      lam < 1 ∧
      dutHeadlineRate - δ
        ≤ dutRate (ThmD.cStar lam) lam ∧
      DUTSharpVerifierCertificate
        (paramsOf stdProfile lam)

/-- The exact lambda->1 headline theorem needs certificates only along an
approaching family, not uniformly for every lambda in [1/2,1). -/
theorem dut_thmD₀_simple_of_approaching_certificates
    (hcert : DUTHeadlineVerifierApproach) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (dutHeadlineRate - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨lam, hlam, hlt, hrate, hcertlam⟩ :=
    hcert (ε / 2) (by linarith)

  have h0 : 0 < lam := by
    linarith

  obtain ⟨T₀, hT₀⟩ :=
    dut_thmD_simple_lam h0 hlt hcertlam
      (ε / 2) (by linarith)

  refine ⟨T₀, ?_⟩
  intro T hT

  have hmain := hT₀ T hT
  have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) :=
    Nat.cast_nonneg _

  have hcoef :
      dutHeadlineRate - ε
        ≤ dutRate (ThmD.cStar lam) lam - ε / 2 := by
    linarith

  exact
    (mul_le_mul_of_nonneg_right hcoef hN0).trans hmain

/-- Generic one-certificate finish line.

A single admissible lambda and a single external verifier certificate prove
any explicit rational target `q` lying strictly below the corresponding
fixed-lambda DUT rate. -/
theorem dut_thmD₀_simple_of_one_certificate
    {q lam : ℝ}
    (hlam : 1 / 2 ≤ lam)
    (hlt : lam < 1)
    (hcert :
      DUTSharpVerifierCertificate
        (paramsOf stdProfile lam))
    (hrate :
      q < dutRate (ThmD.cStar lam) lam) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (q - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  intro ε hε

  have h0 : 0 < lam := by
    linarith

  let δ :=
    min (ε / 2)
      ((dutRate (ThmD.cStar lam) lam - q) / 2)

  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min
      (by linarith)
      (by linarith)

  obtain ⟨T₀, hT₀⟩ :=
    dut_thmD_simple_lam h0 hlt hcert
      δ hδ

  refine ⟨T₀, ?_⟩
  intro T hT

  have hmain := hT₀ T hT
  have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) :=
    Nat.cast_nonneg _

  have hδ_le :
      δ ≤ (dutRate (ThmD.cStar lam) lam - q) / 2 := by
    exact min_le_right _ _

  have hcoef :
      q - ε
        ≤ dutRate (ThmD.cStar lam) lam - δ := by
    linarith

  exact
    (mul_le_mul_of_nonneg_right hcoef hN0).trans hmain

/-- The 67.27918% headline therefore needs only one suitable fixed-lambda
verifier certificate, together with the kernel-checked numerical comparison
at that lambda. -/
theorem dut_thmD₀_simple_6727918_of_one_certificate
    {lam : ℝ}
    (hlam : 1 / 2 ≤ lam)
    (hlt : lam < 1)
    (hcert :
      DUTSharpVerifierCertificate
        (paramsOf stdProfile lam))
    (hrate :
      (3363959 : ℝ) / 5000000
        < dutRate (ThmD.cStar lam) lam) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3363959 : ℝ) / 5000000 - ε)
          * (Ncount T (2 * T) : ℝ)
        ≤ (N0simple T (2 * T) : ℝ) := by
  exact
    dut_thmD₀_simple_of_one_certificate
      hlam hlt hcert hrate

end Zeta23.ZeroSide.RankTraceMult
