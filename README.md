# A Six-Point Refinement of Anthropic's `zeta-23-lean`

> **Previously titled:** *DUT Refinement of `zeta-23-lean`*.  
> The project and Lean modules still use the internal prefix **DUT**
> ("Defect-Utilizing Tightening"), so older links or searches for the
> "DUT Refinement" refer to this same work.

## A Sol–Voshart project

**Primary producer of the new mathematical, Lean, and verifier work:**  
**OpenAI GPT-5.6 Sol**

**Experiment conception, operation, validation workflow, and repository maintenance:**  
**Daniel Voshart (`@voshart`)**

Built on Anthropic's [`zeta-23-lean`](https://github.com/anthropics/zeta-23-lean).

**Public documentation:** drafted primarily by GPT-5.6 Sol; reviewed and
published by Daniel Voshart.

---

## Result

This repository contains a rigorous computer-assisted Lean 4 formalization of
an asymptotic lower bound of

# **67.27918%**

for simple zeros of the Riemann zeta function on the critical line.

For comparison:

```text
Anthropic Theorem D:  approximately 67.250070%
This refinement:      67.27918%
Improvement:          approximately +0.02911 percentage points
```

The numerical gain is small. The interesting part is **where it comes from**.

The final Lean endpoint is

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_span_certificate
```

with one external finite hypothesis:

```lean
DUTFixedScaleFreeSpanCertificate
```

at the exact rational parameter

```text
lambda = 999999999 / 1000000000
```

The corresponding rigorous Arb/FLINT computation returned

```text
verified: true
```

Lean proves that this external proposition is exactly the finite
span-restricted six-point scalar problem searched by the verifier.

---

## Where the improvement comes from

Anthropic's rank-trace argument first retains actual local information about
the zero atoms.

A later leak-free relaxation replaces part of that information by the
worst-case bound `1`.

That simplification is valid, but it discards some of the local Gram geometry.

This refinement returns to the stronger form and asks:

> **Can six consecutive zero atoms actually realize that abstract worst case?**

The sharp Fourier kernel constrains their mutual geometry. The answer is no:
a small positive defect remains.

That defect becomes the new source of saving.

---

## Why six points are enough

After normalization, the genuinely new finite problem no longer depends on

- the height `T`,
- the absolute ordinates of the zeros,
- the full global matrix,
- or infinitely many zeros.

Six ordered points are determined by five consecutive nonnegative gaps.

The external search is over

```text
g1,...,g5 >= 0
g1 + ... + g5 <= 9.45
```

and the relevant `6 x 6` Gram contribution reduces exactly to the 15
unordered pair interactions

```text
2 * sum_{0 <= i < j <= 5} k_lambda(x_j - x_i)^2
```

for one explicit scale-free sinc kernel.

So the genuinely new computer-assisted input can be summarized as:

> **A global asymptotic statement about infinitely many zeta zeros is reduced
> to one inequality on a compact five-dimensional simplex.**

Lean checks the analytic and algebraic reductions to that exact finite
problem.

---

## How the local gain becomes global

A single certified block of six zeros would not change an asymptotic density
theorem.

The proof therefore takes consecutive six-point blocks in all six residue
classes modulo `6` and averages the resulting strengthened inequalities.

This phase decomposition spreads the local defect across the full core range
while controlling overlap and boundary loss.

Conceptually:

> **Every interior zero is exposed to the six-point rigidity without the
> bookkeeping destroying the gain.**

---

## Why the proof self-bootstraps

The new saving itself contains the simple-zero count, which is also the
quantity being lower-bounded.

That initially looks circular.

Instead, the final argument moves that contribution to the other side and
divides by the resulting positive denominator.

In plain English:

> **Part of the local improvement feeds back into the global lower bound that
> the proof is trying to establish.**

This self-bootstrap is one of the most distinctive parts of the endgame.

---

## Why `9.45` and `9.40` are both present

The external finite verifier proves a statement with cutoff

```text
9.45
```

while the downstream local theorem only needs

```text
9.40
```

The difference is deliberate.

The finite computation proves something slightly stronger than necessary, and
Lean spends the extra `0.05` as an explicit transfer/error budget.

The proof therefore follows the robust pattern:

> **Verify something stronger than necessary, then formally spend the excess
> as transfer slack.**

---

## A clean fallback

The six-point improvement matters only where at least six relevant core points
are available.

The final theorem does not need to assume that globally.

When fewer than six core points are present, the extra saving disappears and
the argument falls back to Anthropic's original inequality.

So the refinement improves the proof where the additional local geometry is
available and reduces harmlessly to the upstream proof where it is not.

---

## One exact verifier parameter

An intermediate formulation naturally suggested certificates for parameters
approaching `lambda = 1`.

The final development instead pins the argument to one exact rational value:

```text
999999999 / 1000000000
```

Lean proves that this single parameter still clears the `67.27918%` target.

That leaves one reproducible external finite computation rather than a
continuum of verifier obligations.

---

## The proof in one picture

```text
Anthropic's stronger local rank-trace inequality
                |
                | leak-free relaxation replaces local data by <= 1
                v
        information is discarded
                |
                | return to the stronger form
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
            self-bootstrap
                |
                v
   67.250070...%  ->  67.27918%
```

---

## Verification status

This is a **rigorous computer-assisted Lean formalization**, but not yet a
fully Lean-kernel-checked end-to-end computation.

Lean checks the mathematical deduction and the exact reduction to the finite
span-restricted scalar proposition.

Arb/FLINT, through `python-flint`, checks that remaining finite proposition.

A fully kernel-checked version would additionally require either

1. a Lean-checkable finite certificate, or
2. a formalization of the interval branch-and-bound computation itself.

No `sorry`, `admit`, or new mathematical axiom is used in the current Lean
proof chain.

The recorded verifier run is in

```text
dut-verifier/dut-six-certificate.json
```

and includes

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

See [`DUT_STATUS.md`](DUT_STATUS.md) and
[`dut-verifier/README.md`](dut-verifier/README.md) for the technical details.

---

## The experiment

Daniel Voshart conceived the project as a deliberately low-touch
AI-mathematics experiment and selected Anthropic's formalized result as the
target.

He intentionally supplied **no mathematical steering** during the development
of the refinement.

Voshart has described his mathematical background for the experiment as
roughly high-school level, with no prior expertise in analytic number theory
or Lean.

Much of the exploratory prompting was extremely sparse, sometimes literally:

```text
Do ur thang.
```

GPT-5.6 Sol selected and developed the mathematical route, wrote and debugged
the new Lean formalization, developed the numerical endgame, constructed the
rigorous finite verifier, and formalized the bridge between that verifier and
the upstream theorem.

Voshart operated the experiment: choosing the target, running the interaction,
executing Lean builds and Arb/FLINT computations, returning errors and outputs,
preserving successful states, maintaining the repository, funding the
experiment, and requiring claims to survive mechanical verification before
publication.

The public documentation was drafted primarily by GPT-5.6 Sol and reviewed,
selected, corrected, and published by Daniel Voshart. Descriptions of
Voshart's role are therefore third-person project records, not prose attributed
to Voshart unless explicitly marked as a quotation.

---

## Attribution and provenance

- **OpenAI GPT-5.6 Sol:** primary producer of the new mathematical, formal,
  verifier, and technical work.
- **Daniel Voshart:** experiment conception and operation; validation and
  reproducibility workflow; repository maintenance; funding; publication and
  trust-boundary decisions.
- **Anthropic and upstream contributors:** foundational `zeta-23-lean`
  mathematical and formal infrastructure.

The external verifier engineering materially adapted ideas from the
MIT-licensed `ainta/zeta-simple-zeros` project.

Full records:

- [`AUTHORS.md`](AUTHORS.md)
- [`WORKS_CONSULTED.md`](WORKS_CONSULTED.md)
- [`RESEARCH_HISTORY.md`](RESEARCH_HISTORY.md)
- [`dut-verifier/THIRD_PARTY_NOTICES.md`](dut-verifier/THIRD_PARTY_NOTICES.md)

The inherited upstream README is preserved as

```text
README_UPSTREAM.md
```

---

## Research history

An earlier exploratory research bundle recorded stronger candidate values:

```text
simple-zero candidate:   67.2820595066%
distinct-zero candidate: 83.6410297533%
```

Those remain **research candidates**, not the current formalized headline.

This repository advertises **67.27918%**, the conservative value carried
through the complete current Lean + Arb verification bridge.

See [`RESEARCH_HISTORY.md`](RESEARCH_HISTORY.md).

---

## Building

From the repository root:

```powershell
lake exe cache get
lake build
```

---

## Compact description

> **Sol–Voshart six-point refinement:** GPT-5.6 Sol developed a
> computer-assisted Lean refinement of Anthropic's `zeta-23-lean` argument
> giving a `67.27918%` asymptotic lower bound for simple zeros on the critical
> line. Daniel Voshart conceived, funded, and operated the no-mathematical-
> steering experiment. Lean checks the complete deduction to one finite
> six-point proposition; that proposition is rigorously verified externally
> using Arb/FLINT.
