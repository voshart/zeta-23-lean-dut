# DUT extension of `zeta-23-lean`

This repository is a fork of Anthropic's
[`zeta-23-lean`](https://github.com/anthropics/zeta-23-lean) containing a
Lean 4 formalization of a DUT-based strengthening of the simple-zero argument
for the Riemann zeta function.

## Result

The development gives a **computer-assisted 67.27918% asymptotic lower
bound for simple zeros on the critical line**.

The final fixed-parameter computation uses

```text
lambda = 999999999 / 1000000000.
```

Lean checks the complete deduction from the finite six-point certificate to
the 67.27918% headline, including the exact identification of the physical
sharp Fourier kernel with the scale-free sinc kernel used by the verifier.

The remaining finite inequality was rigorously verified externally using
Arb/FLINT through `python-flint`.

## Final Lean endpoint

The theorem at the external-computation boundary is

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_scaleFree_certificate
```

with hypothesis

```lean
DUTFixedScaleFreeSharpCertificate
```

The following bridge the external scale-free statement to the original DUT
formalization:

```text
Zeta23/ZeroSide/DUTVerifierScaleFreePrelude.lean
Zeta23/ZeroSide/DUTVerifierKernelBridge.lean
Zeta23/ZeroSide/DUTVerifierCertificateBridge.lean
```

In particular,

```lean
dutDSharpKernel_eq_scaleFree
```

proves that the normalized sharp Fourier kernel in the Lean development is
exactly the sinc kernel evaluated by the external verifier.

## External finite verifier

The verifier is in

```text
dut-verifier/verify_dut_six.py
```

and a successful run is recorded in

```text
dut-verifier/dut-six-certificate.json
```

The run returned

```text
verified: true
lambda: 999999999/1000000000
eta: 27/20000
R_verifier: 189/20
grid: 4000
precision_bits: 128
nodes: 68772
splits: 30498
maximum_depth: 32
```

Reproduce it with:

```powershell
py -m pip install "python-flint>=0.8,<1"

py .\dut-verifier\verify_dut_six.py `
  --progress-every 100000 `
  --output .\dut-verifier\dut-six-certificate.json
```

See `dut-verifier/README.md` for the exact verified statement and trust
boundary.

## What Lean checks

The DUT chain includes:

- finite-grid and Poisson reduction;
- sharp six-point kernel control;
- Gram/rank-trace transfer;
- the buffered `9.45 -> 9.40` margin;
- eventual local six-block certification;
- six-phase combinatorics and replacement;
- boundary-strip and `o(N)` control;
- transfer to the concrete upstream `hat(A_z)`;
- Assembly seam and tail estimates;
- self-bootstrap and `cRatio` endgame;
- the `lambda -> 1` limiting argument;
- the exact rational/trigonometric numerical bound;
- reduction to one explicit rational lambda;
- exact physical-kernel to scale-free-verifier identification.

## Trust boundary

This is a **computer-assisted formalization**, not a fully Lean-kernel-checked
end-to-end computation.

Lean checks the mathematical deduction and the exact reduction to the
finite scale-free proposition. Arb/FLINT checks that finite proposition.

Eliminating the external-computation trust boundary would require a
Lean-checkable certificate consumer or a formalization of the interval
verification itself.

## Building

From the repository root:

```powershell
lake exe cache get
lake build
```

## Provenance

This work extends Anthropic's `zeta-23-lean` and retains the upstream
repository's source, history, licensing, and attribution. The inherited
upstream README is preserved as `README_UPSTREAM.md`.

The external verifier engineering was adapted in part from the MIT-licensed
`ainta/zeta-simple-zeros` project. See
`dut-verifier/THIRD_PARTY_NOTICES.md`.

## Milestones

The earlier Lean-only conditional milestone is tagged:

```text
dut-67.27918
```

The external-verifier/bridge milestone should be tagged separately after the
final verifier artifacts are committed.
