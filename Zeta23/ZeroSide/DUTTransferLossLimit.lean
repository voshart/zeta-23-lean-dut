/-
DUTTransferLossLimit.lean

Purely algebraic/asymptotic wrapper for the DUT matrix-transfer loss.

Once the scalar entrywise error tends to zero, the polynomial matrix-transfer
loss

  36 δ (9 + δ) + 12 δ

also tends to zero.  Since the buffered certificate provides the fixed positive
budget `dutCertificateTransferSlack = 27/400000`, the loss is eventually below
that budget.

This file intentionally does NOT prove the concrete entry-error limit.  That is
the next analytic module.

Intended location:
  Zeta23/ZeroSide/DUTTransferLossLimit.lean
-/

import Zeta23.ZeroSide.DUTSharpCertificateSeam

noncomputable section
set_option linter.unusedSectionVars false

open Filter
open scoped Topology

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23

/-- If the uniform Gram-entry error tends to zero, then the induced
Frobenius/trace energy-transfer loss also tends to zero. -/
lemma dutCoreSixTransferLoss_tendsto_zero_of_entryError
    (P : Params)
    (hδ :
      Tendsto (fun T : ℝ => dutCoreSixEntryError T P)
        atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => dutCoreSixTransferLoss T P)
      atTop (𝓝 0) := by
  have h36 :
      Tendsto
        (fun T : ℝ => 36 * dutCoreSixEntryError T P)
        atTop (𝓝 0) := by
    simpa using hδ.const_mul 36
  have h9 :
      Tendsto
        (fun T : ℝ => 9 + dutCoreSixEntryError T P)
        atTop (𝓝 9) := by
    simpa using tendsto_const_nhds.add hδ
  have hprod :
      Tendsto
        (fun T : ℝ =>
          36 * dutCoreSixEntryError T P *
            (9 + dutCoreSixEntryError T P))
        atTop (𝓝 0) := by
    simpa using h36.mul h9
  have h12 :
      Tendsto
        (fun T : ℝ => 12 * dutCoreSixEntryError T P)
        atTop (𝓝 0) := by
    simpa using hδ.const_mul 12
  simpa [dutCoreSixTransferLoss] using hprod.add h12

lemma dutCertificateTransferSlack_pos :
    0 < dutCertificateTransferSlack := by
  norm_num [dutCertificateTransferSlack]

/-- Therefore the matrix-transfer loss eventually fits inside the fixed
buffer created by replacing the verifier cutoff `9.45` by the Lean cutoff
`9.40`. -/
lemma dutCoreSixTransferLoss_eventually_le_slack_of_entryError
    (P : Params)
    (hδ :
      Tendsto (fun T : ℝ => dutCoreSixEntryError T P)
        atTop (𝓝 0)) :
    ∀ᶠ T : ℝ in atTop,
      dutCoreSixTransferLoss T P ≤ dutCertificateTransferSlack := by
  have hloss :=
    dutCoreSixTransferLoss_tendsto_zero_of_entryError P hδ
  exact
    hloss.eventually
      (eventually_le_nhds dutCertificateTransferSlack_pos)

end Zeta23.ZeroSide.RankTraceMult
