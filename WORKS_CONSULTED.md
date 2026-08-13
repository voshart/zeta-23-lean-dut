# Works consulted and provenance

This file records external mathematical works, software artifacts, source
repositories, and documentation that were deliberately consulted during the
DUT project.

The purpose is attribution and research provenance. Inclusion here does **not**
mean that every listed work is a dependency of the final theorem.

The record is split into two phases:

1. the original exploratory research session in which GPT-5.6 Sol developed
   the DUT idea; and
2. the later Lean/formalization/verifier-closure session in which the result
   was integrated, compiled, and matched exactly to the external Arb search.

---

# 1. Original exploratory DUT research session

This section preserves the provenance record reconstructed from the original
interactive DUT research session.

| Work / artifact | How consulted | Role in the search |
|---|---|---|
| Claude / Anthropic, *More Than Two Thirds of the Zeros of the Riemann Zeta Function Lie on the Critical Line* (2026) | Full manuscript repeatedly opened and searched | Primary upstream dependency: rank-trace framework, zero-side blocks, prime side, Poisson/Gabor identity, optimized windows, sharpness, normalizations. |
| Anthropic, *zeta-23-lean* (2026) | Repository and source files opened, especially `RankTraceMult.lean`, `Mult.lean`, `TightMult.lean`, `LinAlg.lean` | Audited exact formal theorem signatures, located the leak-free relaxation, checked tightness, prepared the DUT Lean patch. |
| S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya, C. L. Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta-function*, Acta Arith. 214 (2024), 357-376 | Article/arXiv material retrieved | Background on unconditional pair correlation and alternative positivity routes. Not a new direct dependency beyond Anthropic's upstream use. |
| S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya, C. L. Turnage-Butterbaugh, *Pair Correlation of Zeros of the Riemann Zeta Function I: Proportions of Simple Zeros and Critical Zeros*, arXiv:2501.14545 (2025) | arXiv paper opened and searched | Used to understand unconditional pair-correlation positivity, narrow-box hypotheses, and discarded hybrid approaches. |
| A. Y. Cheer, D. A. Goldston, *Simple zeros of the Riemann zeta-function*, Proc. Amer. Math. Soc. 118 (1993), 365-372 | AMS searchable PDF material repeatedly retrieved; direct download also attempted | Historical benchmark and inspiration for local combinatorics among zero spacings. No theorem from it is imported into the final DUT six-block proof. |
| A. Chirre, F. Gonçalves, D. de Laat, *Pair correlation estimates for the zeros of the zeta function via semidefinite programming*, Adv. Math. 361 (2020), 106926 | Paper/abstract material consulted | Motivated a discarded global-positivity / SDP route. |
| V. Chandee, Y. Lee, S.-C. Liu, M. Radziwiłł, *Simple zeros of primitive Dirichlet L-functions and the asymptotic large sieve*, Q. J. Math. 65 (2014), 63-87 | arXiv/published material opened | Tested a support-2 Dirichlet-family extension; reading the hypotheses exposed GRH dependence, so the proposed unconditional family result was discarded. |
| K. Sono, *A note on simple zeros of primitive Dirichlet L-functions*, Bull. Aust. Math. Soc. 93 (2016), 19-30 | Cambridge PDF opened; relevant pages inspected | Second check on the discarded Dirichlet-family route; confirmed GRH dependence of high simple-zero proportions. |
| J.-C. Bourin, M. Uchiyama, *A matrix subadditivity inequality for f(A+B) and f(A)+f(B)*, Linear Algebra Appl. 423 (2007), 512-518 | arXiv paper opened | Temporarily supported a grouped spectral inequality. Later removed after the cleaner six-atom unitary-regrouping argument was found. Final DUT does not depend on it. |
| Anthropic, Riemann zeta research announcement (2026) | Web page opened repeatedly | Context and links to upstream manuscript/formalization; not a proof dependency. |

## Foundational works followed mainly through upstream citations

The exploratory session repeatedly discussed Montgomery's original
pair-correlation method and the Montgomery-Taylor optimization, but these were
followed mainly through the Anthropic manuscript and Cheer-Goldston rather
than independently read during DUT development:

- H. L. Montgomery, *The pair correlation of zeros of the zeta function*,
  Proc. Sympos. Pure Math. 24 (1973), 181-193.
- H. L. Montgomery, *Distribution of the zeros of the Riemann zeta function*,
  ICM Vancouver 1974, Vol. 1 (published 1975), 379-381.

This distinction is intentional: this file records what was actually
consulted, not every work relevant to the subject.

---

# 2. Later formalization and verifier-closure session

The later session did not originate the DUT idea. Its purpose was to compile,
repair, integrate, numerically pin down, and exactly match the final external
finite verifier to the Lean theorem.

Several searches were nevertheless materially useful to that work.

## Anthropic `zeta-23-lean`

The upstream repository was repeatedly inspected for exact theorem names,
definitions, namespaces, and normalization conventions, including material in
or around:

- `RankTraceMult.lean`
- `ZeroSide/Mult.lean`
- `ParamsD.lean`
- `Assembly.lean`
- `ThmD/Endgame.lean`
- `ThmD/Final.lean`
- `ThmD/Limit.lean`
- window/profile and Fourier-transform definitions
- linear-algebra definitions such as `frobSq` and `rtrace`

**Role:** indispensable formal integration and API/source verification.

**Contribution type:** upstream mathematical/formal foundation and exact Lean
interface information.

These inspections did not supply the original DUT refinement idea, but they
did materially determine how the new proof had to be expressed inside the
actual upstream formalization.

## Mathlib / Lean documentation and source

Mathlib documentation and source were consulted for exact Lean APIs and
lemmas involving, among other things:

- `Real.sinc`;
- trigonometric identities;
- interval integrals;
- complex exponentials;
- continuity/integrability;
- finite sums;
- arithmetic tactics and order lemmas.

**Role:** Lean implementation and compiler-driven proof repair.

**Contribution type:** formal-library infrastructure.

These lookups were implementation work rather than a source of the DUT
mathematical idea.

## `ainta/zeta-simple-zeros`

Repository:

https://github.com/ainta/zeta-simple-zeros

This project was inspected after the DUT global proof chain was already
substantially developed.

Its stronger seven-point mathematical architecture was **not** imported into
the DUT proof.

However, its rigorous external-verifier engineering materially influenced the
final DUT verifier, including the general pattern of:

- Arb interval evaluation of transcendental kernels;
- conservative cellwise lower bounds;
- branch-and-bound subdivision;
- sparse range minima;
- outward-rounded floating-point lower arithmetic;
- convex/tangent pruning.

The DUT verifier was adapted in part from this engineering and therefore
retains the upstream MIT notice in:

```text
dut-verifier/THIRD_PARTY_NOTICES.md
```

**Role:** material verifier-engineering influence.

**Contribution type:** software/verifier methodology, not the original DUT
theoretical refinement.

## `python-flint` / Arb / FLINT

Documentation and package information were consulted to install and run the
rigorous external finite computation.

**Role:** numerical verification infrastructure.

The final recorded finite search uses Arb/FLINT through `python-flint`.

## GitHub documentation

GitHub documentation was consulted for repository/fork/remote/push workflow.

**Role:** publication and repository administration only.

No mathematical or verifier result depended on these searches.

## Reddit thread

The public Reddit thread documenting the experiment was consulted later for
historical provenance and to confirm the deliberately sparse prompting style.

**Role:** historical record only.

It did not influence the DUT mathematics or formal proof.

## Authorship-policy sources

During preparation of the public README, current authorship/AI-policy material
from organizations and publishers such as ICMJE, COPE, and Nature was
consulted.

**Role:** wording and attribution-policy discussion only.

These sources played no role in the mathematics, Lean development, or
verifier.

---

# 3. Attribution summary

The most accurate high-level provenance statement is:

- **Anthropic and upstream contributors** supplied the foundational
  `zeta-23-lean` mathematical and formal framework.
- **OpenAI GPT-5.6 Sol** produced the primary new DUT mathematical
  development, Lean formalization, verifier construction, and technical
  integration work.
- **Daniel Voshart** conceived and operated the no-mathematical-steering
  experiment, ran the validation loop, maintained reproducibility and the
  repository, and made publication/trust-boundary decisions.
- The original exploratory research consulted the mathematical literature
  listed above.
- The later formalization phase relied heavily on Anthropic source inspection
  and Mathlib API lookup.
- The final external verifier materially borrowed engineering ideas from
  `ainta/zeta-simple-zeros`, with MIT attribution retained.

This file intentionally distinguishes **theoretical influence** from
**implementation influence**, **upstream dependency**, and **historical or
administrative consultation**.


---

## Documentation provenance

This provenance record was assembled and drafted by GPT-5.6 Sol from the
research and implementation history, then reviewed/published by Daniel
Voshart.
