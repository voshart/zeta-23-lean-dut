# DUT six-point Arb verifier

This directory contains the rigorous external finite verifier for the DUT
67.27918% milestone.

## Attribution

**Primary verifier development:** OpenAI GPT-5.6 Sol.

**Experiment operation and reproduction:** Daniel Voshart.

The branch-and-bound verifier engineering materially adapts patterns from the
MIT-licensed:

```text
https://github.com/ainta/zeta-simple-zeros
```

The required notice is retained in:

```text
THIRD_PARTY_NOTICES.md
```

See the repository-level `WORKS_CONSULTED.md` for broader provenance.

## Verified parameter

```text
lambda = 999999999 / 1000000000
```

## Successful recorded run

```text
verified: true
eta: 27/20000
R_verifier: 189/20
target: 5103/400000
grid: 4000
precision_bits: 128
nodes: 68772
pruned: 38274
splits: 30498
maximum_depth: 32
```

## Reproduction

```powershell
py -m pip install "python-flint>=0.8,<1"

py .\dut-verifier\verify_dut_six.py `
  --progress-every 100000 `
  --output .\dut-verifier\dut-six-certificate.json
```

## Lean boundary

The final Lean theorem at this exact search boundary is:

```lean
dut_thmD₀_simple_6727918_of_span_certificate
```

with:

```lean
DUTFixedScaleFreeSpanCertificate
```

The Lean development proves that this proposition is exactly the
span-restricted 15-pair scalar inequality searched here.

## Trust boundary

The verifier is rigorous but external to Lean.

Its trust base includes Python, `python-flint`, Arb/FLINT, the verifier source,
and the execution environment.


## Documentation provenance

This verifier README was drafted by GPT-5.6 Sol and published by Daniel
Voshart.
