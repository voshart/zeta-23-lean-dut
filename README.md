# DUT Refinement of `zeta-23-lean`

## A Sol–Voshart project

**Primary producer of the new mathematical, Lean, and verifier work:**  
**OpenAI GPT-5.6 Sol**

**Experiment conception, operation, validation workflow, and repository maintenance:**  
**Daniel Voshart (`@voshart`)**

Built on Anthropic's [`zeta-23-lean`](https://github.com/anthropics/zeta-23-lean).

**Public documentation:** drafted primarily by GPT-5.6 Sol; reviewed and published by Daniel Voshart.

---

## Result

This repository contains a rigorous computer-assisted Lean 4 formalization of a

# **67.27918%**

asymptotic lower bound for simple zeros of the Riemann zeta function on the
critical line.

Anthropic's corresponding Theorem D gives approximately

```text
67.250070%
```

while the formalized DUT milestone gives

```text
67.27918%
```

an improvement of approximately

```text
+0.02911 percentage points
```

The numerical movement is modest. The interesting part is **where the
improvement comes from**.

The final Lean endpoint is

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_span_certificate
```

with sole external hypothesis

```lean
DUTFixedScaleFreeSpanCertificate
```

at the explicit rational parameter

```text
lambda = 999999999 / 1000000000
```

The rigorous external Arb/FLINT verifier returned

```text
verified: true
```

and Lean proves that this external proposition is exactly the finite
span-restricted six-point scalar problem searched by that verifier.

---

# What is actually new in DUT?

The shortest version is:

> **Anthropic proves a geometry-sensitive rank-trace inequality and then
> deliberately forgets part of that geometry to obtain a clean leak-free
> global bound. DUT goes back to the stronger form and proves that six
> consecutive zero atoms cannot simultaneously realize the forgotten
> worst case.**

The recovered defect is small, but it survives averaging and improves the
final asymptotic simple-zero proportion.

## Hidden gem 1 — the proof improves an explicit information-loss step

The upstream rank-trace development first retains actual local atom
norm-square information.

A later leak-free relaxation replaces those local quantities by the
worst-case bound `1`.

That simplification is valid, but it throws away information about the actual
Gram geometry of nearby zeta-zero atoms.

DUT asks:

> **What if six consecutive zero atoms cannot all behave like that abstract
> worst case?**

The sharp Fourier kernel constrains their mutual geometry. DUT turns the
resulting failure of worst-case behavior into an additional rank-trace saving.

This is the conceptual origin of the refinement.

---

## Hidden gem 2 — an infinite zeta problem collapses to five real gaps

After normalization, the genuinely new finite problem no longer depends on:

- the height `T`;
- the absolute ordinates of the zeros;
- the full global matrix;
- or infinitely many zeros.

Six ordered points are determined by five consecutive nonnegative gaps.

The final finite search is over

```text
g1,...,g5 >= 0
g1 + ... + g5 <= 9.45
```

and the six-point matrix defect becomes exactly the 15 unordered pair
interactions

```text
2 * sum_{0 <= i < j <= 5} k_lambda(x_j - x_i)^2
```

for one explicit scale-free sinc kernel.

So the new computer-assisted input can be summarized as:

> **A global asymptotic statement about infinitely many zeta zeros is reduced
> to one inequality on a compact five-dimensional simplex.**

Lean checks every analytic and algebraic reduction to that finite problem.

---

## Hidden gem 3 — six phases globalize a local six-point rigidity

One certified six-zero block would not alter an asymptotic density theorem.

DUT takes consecutive six-point blocks in all six residue classes modulo `6`
and averages the resulting strengthened inequalities.

The phase decomposition spreads the local defect across the core range while
controlling overlap and boundary loss.

Conceptually:

> **Every interior zero is exposed to the six-point rigidity without the
> bookkeeping destroying the gain.**

This is the bridge from a tiny local certificate to a global asymptotic
saving.

---

## Hidden gem 4 — the improvement self-bootstraps

The DUT saving itself contains the simple-zero count, which is also the
quantity being lower-bounded.

That initially looks circular.

The final argument moves that contribution to the opposite side and divides
by the resulting positive denominator.

In plain English:

> **Part of the local improvement feeds back into the global lower bound that
> the proof is trying to establish.**

This self-bootstrap is one of the most distinctive pieces of the DUT endgame.

---

## Hidden gem 5 — the verifier deliberately proves more than Lean spends

The external finite computation works with the cutoff

```text
9.45
```

while the downstream local theorem only needs

```text
9.40
```

The `0.05` difference is deliberate.

The finite verifier proves something slightly stronger than necessary, and
Lean formally spends that excess as an error budget during the transfer from
the ideal sharp kernel to the analytic object used downstream.

The pattern is:

> **Verify something stronger than necessary, then formally spend the excess
> as transfer slack.**

---

## Hidden gem 6 — the refinement falls back cleanly to Anthropic's proof

The six-point improvement matters only where at least six relevant core
points are available.

The final theorem does not need to assume that globally.

When fewer than six core points are present, the DUT saving disappears and the
argument falls back to the original upstream inequality.

So DUT behaves as a genuine refinement:

> **It improves the proof where the extra local geometry exists and reduces
> harmlessly to the original proof where it does not.**

---

## Hidden gem 7 — a continuum of external obligations becomes one computation

An intermediate endgame formulation naturally suggested verifier certificates
for parameters approaching `lambda = 1`.

The final development instead pins the theorem to one exact rational value:

```text
lambda = 999999999 / 1000000000
```

Lean proves that this one parameter still clears the `67.27918%` target.

The remaining computer-assisted obligation is therefore one reproducible
finite computation rather than an external continuum of certificates.

---

## The DUT pipeline

```text
Anthropic's stronger local rank-trace inequality
                |
                | leak-free relaxation replaces local data by <= 1
                v
        information is discarded
                |
                | DUT returns to the stronger form
                v
       six-zero Gram rigidity
                |
                | rigorous finite five-gap certificate
                v
       positive local defect
                |
                | six-phase averaging
                v
       global rank-trace saving
                |
                | boundary control + Assembly seam
                v
          DUT self-bootstrap
                |
                v
   67.250070...%  ->  67.27918%
```

The numerical difference is small. The structural result is that local
geometry discarded by the original relaxation can be recovered, certified,
globalized, and made to survive the full formal endgame.

---

# The experiment

This project began with a deliberately low-touch question:

> **Could Daniel Voshart improve upon Anthropic's formal proof using
> GPT-5.6 Sol while supplying no mathematical steering to the model?**

Daniel Voshart conceived the experiment and selected Anthropic's result as the
target. He intentionally supplied **no mathematical steering** during the
development of DUT.

Voshart has described his mathematical background for this experiment as
roughly high-school level, with no prior expertise in analytic number theory
or Lean.

Much of the exploratory prompting was extremely sparse, sometimes literally:

```text
Do ur thang.
```

GPT-5.6 Sol selected and developed the mathematical route that became DUT,
wrote and debugged the new Lean formalization, developed the numerical
endgame, constructed the rigorous finite verifier, and formalized the bridges
between that verifier and the original Lean theorem.

Voshart's role was operational and experimental: choosing the target, running
the interaction, executing requested Lean builds and Arb/FLINT computations,
returning errors and outputs to the model, preserving successful states,
maintaining the repository, funding the experiment, and requiring claims to
survive mechanical verification before publication.

The experiment was designed to test how far an AI system could carry a
substantive formal-mathematics research task without receiving mathematical
steering from the human operator.

### Documentation authorship

The public documentation in this repository was drafted primarily by
**OpenAI GPT-5.6 Sol** and reviewed, selected, and published by
**Daniel Voshart**.

Accordingly, descriptions of Voshart's role are written in the third person.
They should not be read as prose authored by Voshart unless explicitly marked
as a quotation.

---

# Attribution

For this repository, **Sol–Voshart** refers to the experimental collaboration:

- **OpenAI GPT-5.6 Sol:** primary producer of the new DUT mathematical,
  formal, verifier, and technical work.
- **Daniel Voshart:** experiment conceiver and operator; validation and
  reproducibility workflow; repository maintenance; funding of the experiment;
  publication and trust-boundary decisions.
- **Anthropic and upstream contributors:** foundational `zeta-23-lean`
  formalization and mathematical infrastructure.

Daniel Voshart intentionally supplied **no mathematical steering** to the
development of DUT.

GPT-5.6 Sol was not treated as a trusted mathematical authority. Suggested
proofs were accepted only when checked by Lean, and the remaining finite
numerical proposition was subjected to rigorous Arb/FLINT verification.

Full attribution and provenance:

- [`AUTHORS.md`](AUTHORS.md)
- [`WORKS_CONSULTED.md`](WORKS_CONSULTED.md)
- [`RESEARCH_HISTORY.md`](RESEARCH_HISTORY.md)
- [`dut-verifier/THIRD_PARTY_NOTICES.md`](dut-verifier/THIRD_PARTY_NOTICES.md)

The inherited upstream README is preserved as:

```text
README_UPSTREAM.md
```

---

# What Lean checks

The DUT development includes:

- finite-grid reduction;
- Poisson reduction and sharp-kernel control;
- six-point Gram/rank-trace transfer;
- the buffered `9.45 -> 9.40` margin;
- entry-error and transfer-loss limits;
- eventual local six-block certification;
- six-phase combinatorics;
- core specialization and fallback;
- boundary-strip control and `o(N)` asymptotics;
- `Pmat` gluing and phase replacement;
- transfer to the concrete upstream `hat(A_z)` expression;
- Assembly seam and tail estimates;
- exact core-count bootstrap;
- DUT self-bootstrap;
- Montgomery-Taylor `cRatio` endgame;
- `lambda -> 1^-` limiting machinery;
- exact rational/trigonometric numerical certification;
- reduction to one explicit rational verifier parameter;
- exact physical-kernel / scale-free-kernel identity;
- exact Gram-energy / 15-pair scalar-energy identity;
- exact all-span / span-`<= 9.45` verifier-domain equivalence.

No `sorry`, `admit`, or new mathematical axiom is used in the DUT proof
chain.

---

# External finite verifier

The verifier is:

```text
dut-verifier/verify_dut_six.py
```

The successful run is recorded in:

```text
dut-verifier/dut-six-certificate.json
```

Recorded values include:

```text
verified: true
lambda: 999999999/1000000000
eta: 27/20000
R_verifier: 189/20
target: 5103/400000
grid: 4000
precision_bits: 128
nodes: 68772
splits: 30498
maximum_depth: 32
```

See [`dut-verifier/README.md`](dut-verifier/README.md).

The verifier engineering materially adapted ideas from the MIT-licensed
`ainta/zeta-simple-zeros` project. The required attribution is retained in:

```text
dut-verifier/THIRD_PARTY_NOTICES.md
```

---

# Trust boundary

This is a **rigorous computer-assisted Lean formalization**, not a fully
Lean-kernel-checked end-to-end computation.

Lean checks the mathematical deduction and the exact reduction to the finite
span-restricted scalar proposition.

Arb/FLINT, through `python-flint`, checks that finite proposition.

A fully kernel-checked end-to-end version would additionally require a
Lean-checkable finite certificate or a formalization of the interval search.

---

# Research history

The earlier exploratory DUT research bundle recorded:

```text
simple-zero candidate:   67.2820595066%
distinct-zero candidate: 83.6410297533%
```

These are research-candidate values, not the current formalized headline.

The repository advertises **67.27918%**, the conservative value carried
through the complete Lean + Arb bridge.

See [`RESEARCH_HISTORY.md`](RESEARCH_HISTORY.md).

---

# Building

```powershell
lake exe cache get
lake build
```

---

## Compact description

> **Sol–Voshart DUT:** GPT-5.6 Sol developed a computer-assisted Lean
> refinement of Anthropic's `zeta-23-lean` argument giving a 67.27918%
> asymptotic lower bound for simple zeros on the critical line. Daniel Voshart
> conceived, funded, and operated the no-mathematical-steering experiment.
> Lean checks the full deduction and exact reduction to a finite six-point
> proposition; the remaining finite proposition is rigorously verified using
> Arb/FLINT.
