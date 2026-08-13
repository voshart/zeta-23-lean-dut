# DUT formalization status

## Current result

**Rigorous computer-assisted 67.27918% simple-zero lower bound.**

Baseline and refinement:

```text
Anthropic Theorem D: approximately 67.250070%
DUT milestone:       67.27918%
gain:                approximately +0.02911 percentage points
```

Final Lean endpoint:

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_span_certificate
```

External finite proposition:

```lean
DUTFixedScaleFreeSpanCertificate
```

Fixed verifier parameter:

```text
lambda = 999999999 / 1000000000
```

Recorded Arb result:

```text
verified: true
```

## Distinctive proof features

1. **Information recovery.** DUT returns to the stronger upstream rank-trace
   inequality before the leak-free relaxation replaces actual local atom
   information by the worst-case bound `1`.

2. **Five-gap finite reduction.** The new finite input becomes an inequality
   on five nonnegative consecutive gaps with total span at most `9.45`.

3. **Six-phase globalization.** Six residue classes of consecutive six-point
   blocks turn the local defect into a global asymptotic saving.

4. **Self-bootstrap.** The saving contains the simple-zero count itself;
   rearrangement feeds part of that improvement back into the final bound.

5. **Buffered verifier margin.** The external computation proves the stronger
   `9.45` cutoff while the downstream theorem only spends `9.40`.

6. **Harmless fallback.** With fewer than six core points, the extra saving
   disappears and the proof reduces to Anthropic's original inequality.

7. **One exact external computation.** The final proof pins the verifier to
   `lambda = 999999999 / 1000000000`.

## Exact matching chain

Lean proves:

1. the DUT global proof chain;
2. the exact fixed-parameter numerical reduction;
3. physical sharp kernel = scale-free sinc kernel;
4. physical certificate = scale-free matrix certificate;
5. matrix Gram energy = the verifier's 15-pair scalar energy;
6. all-span positive-part certificate = span-`<=9.45` search certificate.

Thus the proposition exposed at the external boundary matches the actual
finite Arb search analytically, algebraically, and in domain.

## Trust boundary

Lean checks the formal proof and exact reduction.

Arb/FLINT checks the finite interval search externally.

## Attribution

- **GPT-5.6 Sol:** primary producer of the new DUT
  mathematical/formal/verifier work.
- **Daniel Voshart:** experiment conception, funding and operation, validation
  loop, reproducibility, repository maintenance, publication decisions.
- **Anthropic/upstream:** foundational formalization.
- **Other consulted works/software:** see `WORKS_CONSULTED.md`.


## Documentation provenance

This status document was drafted by GPT-5.6 Sol and published by Daniel
Voshart. It is a third-person project record, not a statement written in
Voshart's voice.
