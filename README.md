# DUT extension of `zeta-23-lean`

This repository is a fork of Anthropic's [`zeta-23-lean`](https://github.com/anthropics/zeta-23-lean) containing an experimental Lean 4 formalization of a DUT-based strengthening of the simple-zero argument for the Riemann zeta function.

## Current status

The DUT development now kernel-checks the full deduction of the asymptotic headline

**67.27918%**

for simple zeros on the critical line, **conditional on one explicitly isolated finite verifier certificate**.

The current milestone is tagged:

```text
dut-67.27918
```

The minimal one-certificate headline theorem is:

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_one_certificate
```

It has the form:

- choose one admissible fixed parameter `λ < 1`,
- supply one `DUTSharpVerifierCertificate (paramsOf stdProfile λ)`,
- prove that the corresponding fixed-`λ` DUT rate exceeds `0.6727918`,
- conclude the asymptotic `67.27918% - ε` simple-zero lower bound.

A stronger exact limiting theorem is also formalized through:

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple
```

with exact limiting rate

```lean
dutHeadlineRate = dutRate (ThmD.cStar 1) 1
```

and a kernel-checked numerical theorem:

```lean
Zeta23.ZeroSide.RankTraceMult.dutHeadlineRate_gt_6727918
```

## What is formalized

The checked DUT chain currently includes:

- finite-grid reduction;
- Poisson reduction and sharp kernel control;
- six-point Gram/rank-trace transfer;
- buffered `9.45 -> 9.40` certificate margin;
- entry-error and transfer-loss limits;
- eventual local six-block certification;
- six-phase combinatorics;
- core specialization;
- boundary-strip control and `o(N)` asymptotics;
- generic `Pmat` gluing;
- phase replacement;
- six-phase averaged rank-trace inequalities;
- transfer to the concrete upstream `hat(A_z)` form;
- Anthropic Assembly tail/seam transfer;
- exact core-boundary bootstrap;
- Montgomery-Taylor `cRatio` endgame;
- DUT self-bootstrap;
- asymptotic absorption of all DUT-specific error terms;
- `λ -> 1^-` limiting argument;
- an exact rational/trigonometric Lean proof certifying the `67.27918%` displayed constant.

## Remaining verification boundary

The remaining external obligation is:

```lean
DUTSharpVerifierCertificate P
```

This is intentionally isolated as the contract for the finite rigorous six-point verifier.

The global analytic and asymptotic deduction downstream of that contract is checked by Lean. The current public result should therefore be described as:

> A Lean-kernel-checked deduction of a 67.27918% simple-zero lower bound, conditional on one finite DUT verifier certificate.

The immediate next goal is to discharge this certificate at one suitable explicit rational value of `λ`.

## Important files

The later-stage DUT modules include:

```text
Zeta23/ZeroSide/DUTHatAzPhase.lean
Zeta23/ZeroSide/DUTAssemblySeamAllCore.lean
Zeta23/ZeroSide/DUTAssemblyBootstrapAllCore.lean
Zeta23/ZeroSide/DUTAssemblyC.lean
Zeta23/ZeroSide/DUTCoreFallback.lean
Zeta23/ZeroSide/DUTPhaseReplacementEventually.lean
Zeta23/ZeroSide/DUTMainScaleAsymptotic.lean
Zeta23/ZeroSide/DUTExtraErrorAsymptotic.lean
Zeta23/ZeroSide/DUTSelfBootstrap.lean
Zeta23/ZeroSide/DUTEndgameAbstract.lean
Zeta23/ZeroSide/DUTFinalLam.lean
Zeta23/ZeroSide/DUTFinalHeadline.lean
Zeta23/ZeroSide/DUTHeadlineNumeric.lean
Zeta23/ZeroSide/DUTFinalOneCertificate.lean
```

Earlier `DUT*` modules in the same directory contain the local analytic, six-point, phase, and boundary machinery feeding these endgame files.

## Building

This fork uses the Lean toolchain pinned by the upstream project.

From the repository root:

```powershell
lake exe cache get
lake build
```

For a single module during development:

```powershell
lake env lean .\Zeta23\ZeroSide\<Module>.lean
```

The milestone corresponding to the current development is:

```text
git tag: dut-67.27918
```

## Provenance

This work extends Anthropic's `zeta-23-lean` repository and relies extensively on its existing formalization, including the zero-side matrix framework, Assembly seam, Montgomery-Taylor parameter family, Riemann-von Mangoldt asymptotics, and Theorem-D endgame infrastructure.

Original upstream repository:

https://github.com/anthropics/zeta-23-lean

This fork should be read together with the upstream repository's license, attribution, and original documentation.

## Related work

The separate project [`ainta/zeta-simple-zeros`](https://github.com/ainta/zeta-simple-zeros) develops a different, stronger seven-point/stability approach and reports a `67.3008528%` result with an Arb-based external verifier.

That architecture is not currently imported into this DUT proof chain. It is best treated as related work and a possible source of verifier engineering or a future stronger branch.

## Near-term roadmap

1. Pick one explicit rational `λ < 1` for which the Lean rate remains strictly above `0.6727918`.
2. Implement or adapt a rigorous finite verifier for the exact `DUTSharpVerifierCertificate` obligation at that `λ`.
3. Attach the resulting certificate/verifier artifact to this repository.
4. Replace the remaining certificate hypothesis by a checked concrete theorem.
5. Package the resulting unconditional one-`λ` headline theorem as the next tagged milestone.

---

**Current milestone:** formal endgame closed; one finite verifier certificate remains.
