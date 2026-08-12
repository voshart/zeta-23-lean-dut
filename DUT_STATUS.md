# DUT 67.27918% milestone status

## Result

This fork contains a Lean 4 formalization of the full DUT deduction of the
asymptotic lower bound

**67.27918%**

for simple zeros on the critical line, together with a rigorous external Arb
verification of the remaining finite six-point inequality at

```text
lambda = 999999999 / 1000000000.
```

## Lean endpoint

The final Lean theorem at the external-computation boundary is

```lean
Zeta23.ZeroSide.RankTraceMult.dut_thmD₀_simple_6727918_of_scaleFree_certificate
```

with hypothesis

```lean
DUTFixedScaleFreeSharpCertificate
```

The Lean development proves that this hypothesis is exactly the scale-free
finite statement evaluated by `dut-verifier/verify_dut_six.py`.

## External verifier result

A successful run produced:

```json
{
  "verified": true,
  "lambda": "999999999/1000000000",
  "eta": "27/20000",
  "R_verifier": "189/20",
  "target": "5103/400000",
  "grid": 4000,
  "precision_bits": 128,
  "nodes": 68772,
  "splits": 30498,
  "maximum_depth": 32
}
```

The full report is stored in:

```text
dut-verifier/dut-six-certificate.json
```

## Interpretation

The result should be described as a **computer-assisted Lean formalization**:

- all deductions from the finite six-point certificate through the 67.27918%
  asymptotic headline are checked by Lean;
- the exact kernel/coordinate bridge to the finite verifier is checked by Lean;
- the remaining finite inequality is rigorously checked externally using
  Arb/FLINT.

It should not be described as fully kernel-checked end-to-end unless the
external interval certificate is later consumed and verified inside Lean.

## Built modules added at the final stage

```text
DUTFixedLambdaNumeric.lean
DUTVerifierScaleFreePrelude.lean
DUTVerifierKernelBridge.lean
DUTVerifierCertificateBridge.lean
```

The milestone prior to verifier closure was tagged:

```text
dut-67.27918
```

A later release/tag should be created after the verifier artifacts and final
bridge modules are committed.
