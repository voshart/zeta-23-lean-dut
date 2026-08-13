# Authorship and contribution record

## Sol–Voshart

For this repository, **Sol–Voshart** is shorthand for the experimental
collaboration between OpenAI GPT-5.6 Sol and Daniel Voshart.

It is a contribution description, not a claim about journal-specific or legal
definitions of authorship.

## OpenAI GPT-5.6 Sol

### Primary producer of the new DUT mathematical/formal work

GPT-5.6 Sol produced the substantive new DUT contribution, including:

- identifying the rank-trace information-loss point exploited by DUT;
- developing the Defect-Utilizing Tightening refinement;
- deriving the six-point local defect mechanism;
- developing the local-to-global, phase, boundary, and endgame chain;
- writing and debugging the new Lean modules;
- developing the fixed-parameter numerical endgame;
- deriving the formal `67.27918%` headline certification;
- constructing the rigorous Arb six-point verifier;
- proving the physical sharp-kernel / scale-free sinc-kernel bridge;
- proving the matrix Gram-energy / 15-pair scalar-energy identity;
- proving the exact `9.45` verifier-domain seam;
- drafting substantial technical and public documentation.

GPT-5.6 Sol was not treated as a trusted authority. New proof steps were
accepted only after Lean checking, and the remaining finite proposition was
checked rigorously using Arb/FLINT.

## Daniel Voshart / `@voshart`

### Experiment conception and operation

Daniel Voshart:

- conceived the experiment;
- selected Anthropic's result as the target;
- intentionally supplied **no mathematical steering** to the model;
- funded the AI/tooling used in the experiment;
- kept the interactive research process running;
- executed Lean commands and returned compiler output;
- executed the Arb/FLINT verifier and returned runtime output;
- preserved successful working states;
- maintained the Git repository;
- managed reproducibility and publication;
- made the explicit trust-boundary decisions;
- proposed the name **DUT — Defect-Utilizing Tightening**.

Voshart's role was not the mathematical derivation of DUT.

For this experiment, Voshart describes his mathematical background as roughly
high-school level, with no prior expertise in analytic number theory or Lean.

## Anthropic and contributors to `zeta-23-lean`

### Foundational formalization

DUT depends extensively on Anthropic's original `zeta-23-lean` mathematical
framework and Lean formalization.

The upstream project supplies the rank-trace framework, zero-side matrix and
atom infrastructure, optimized window/profile machinery, Assembly/endgame
infrastructure, and the formal analytic-number-theory foundation on which DUT
is built.

Upstream:

https://github.com/anthropics/zeta-23-lean

## Other mathematical and software influences

A complete provenance record is maintained in:

```text
WORKS_CONSULTED.md
```

The final Arb verifier materially adapted engineering patterns from the
MIT-licensed `ainta/zeta-simple-zeros` project.

The required MIT notice is retained in:

```text
dut-verifier/THIRD_PARTY_NOTICES.md
```


## Documentation authorship

The public-facing documentation for the DUT repository was drafted primarily
by **OpenAI GPT-5.6 Sol**.

**Daniel Voshart** reviewed, selected, corrected, and published that
documentation. Statements describing Voshart's background, intentions, or
role are therefore third-person descriptions of the experiment record, not
first-person prose attributed to Voshart unless explicitly presented as a
quotation.

## Compact attribution

> **Primary producer of the new DUT mathematical/formal work:** OpenAI
> GPT-5.6 Sol  
> **Experiment conception, funding, and operation:** Daniel Voshart  
> **Foundational formalization:** Anthropic and upstream contributors  
> **Additional mathematical/software provenance:** `WORKS_CONSULTED.md`
