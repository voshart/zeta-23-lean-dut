# DUT six-point verifier

This directory contains the external rigorous finite verifier used by the DUT
extension of `zeta-23-lean`.

## Status

The verifier has been run successfully at

```text
lambda = 999999999 / 1000000000
```

and returned

```json
"verified": true
```

for the exact scale-free six-point inequality consumed by the Lean theorem

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_scaleFree_certificate
```

through the proposition

```lean
Zeta23.ZeroSide.RankTraceMult.DUTFixedScaleFreeSharpCertificate
```

## Verified statement

For nonnegative gaps `g1,...,g5` with total span at most

```text
R_verifier = 189 / 20 = 9.45
```

the verifier proves

```text
eta * (g1 + ... + g5)
  + 2 * sum_{0 <= i < j <= 5} k_lambda(x_j - x_i)^2
  >= eta * R_verifier
```

where

```text
eta = 27 / 20000
x_0 = 0
x_j = g1 + ... + gj
```

and

```text
k_lambda(y)
  =
  [sinc(pi*y - lambda/sqrt(2))
    + sinc(pi*y + lambda/sqrt(2))]
  /
  [2*sinc(lambda/sqrt(2))].
```

Equivalently,

```text
2 * sum_{i<j} k_lambda(x_j-x_i)^2
  >= eta * max(R_verifier - (x_5-x_0), 0).
```

## Reproduction

The verifier requires Python and `python-flint`.

Example:

```powershell
py -m pip install "python-flint>=0.8,<1"

py .\dut-verifier\verify_dut_six.py `
  --progress-every 100000 `
  --output .\dut-verifier\dut-six-certificate.json
```

The successful run recorded:

```text
verified: true
nodes: 68772
splits: 30498
maximum_depth: 32
precision_bits: 128
grid: 4000
```

The JSON report also records hashes of the verifier source and generated
kernel tables.

## Lean bridge

The external verifier does not directly generate a Lean proof term.

The following Lean modules prove that its scale-free kernel and geometry are
exactly the quantities used by the DUT theorem:

```text
Zeta23/ZeroSide/DUTVerifierScaleFreePrelude.lean
Zeta23/ZeroSide/DUTVerifierKernelBridge.lean
Zeta23/ZeroSide/DUTVerifierCertificateBridge.lean
```

In particular:

```lean
dutDSharpKernel_eq_scaleFree
```

identifies the normalized physical sharp Fourier kernel with the exact sinc
kernel evaluated by the verifier, and

```lean
dutSharpVerifierCertificate_of_scaleFree
```

transfers the scale-free six-point certificate to the original
`DUTSharpVerifierCertificate`.

## Trust boundary

The Lean proof does not assert the external computation as an axiom.

The final computer-assisted result therefore has two layers:

1. the global analytic, asymptotic, algebraic, and kernel-identification chain,
   checked by Lean;
2. the finite six-point inequality, checked externally using Arb/FLINT through
   `python-flint`.

A fully kernel-checked end-to-end result would additionally require a
Lean-checkable certificate format/consumer or a formalization of the finite
interval verification itself.

## Related verifier engineering

The branch-and-bound architecture was adapted from the MIT-licensed verifier
in:

```text
https://github.com/ainta/zeta-simple-zeros
```

Its license/attribution should be preserved when distributing derived verifier
code.
