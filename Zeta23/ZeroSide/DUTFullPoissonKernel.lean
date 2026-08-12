/-
DUTFullPoissonKernel.lean

Exact infinite-grid kernel behind the concrete Theorem-D six-zero vectors.

For the height-T Montgomery--Taylor window P.atD T, Anthropic's generic
AdmWindow Poisson theorem gives

  sum_{k in Z} phiHat(gamma-tau_k) phiHat(gamma'-tau_k)
    = L * VPhiR(phiD)(gamma-gamma').

After division by the vhat normalization a L^2, the corresponding full-grid
normalized pair kernel is

  VPhiR(phiD)(gamma-gamma') / (a L).

This file deliberately does NOT compare the finite k=0,...,d-1 Gram entry to
that full-grid sum and does NOT compare phiD^2 to the sharp cosine kernel.
Those are the two remaining analytic transfer estimates.

Intended location:
  Zeta23/ZeroSide/DUTFullPoissonKernel.lean
-/

import Zeta23.ZeroSide.DUTThmDBlocks

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The exact real full-grid kernel attached to the Theorem-D window before
normalization by `a L`. -/
noncomputable def dutDFullKernelRaw (P : Params) (T x : ℝ) : ℝ :=
  AdmWindow.VPhiR (P.phiD T) x

/-- The exact normalized full-grid kernel corresponding to the upstream
`vhat` normalization `a L^2`. -/
noncomputable def dutDFullKernel (P : Params) (T x : ℝ) : ℝ :=
  AdmWindow.VPhiR (P.phiD T) x /
    ((P.atD T).a T * (P.atD T).L T)

/-- Anthropic's generic admissible-window Poisson theorem, specialized to the
height-T Theorem-D window.  This identifies the *full integer grid* pair sum
exactly, before any finite-grid truncation. -/
theorem dutD_full_pair_hasSum
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (gamma gamma' : ℝ) :
    HasSum
      (fun k : ℤ =>
        (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
        (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k))
      (P.L T * dutDFullKernelRaw P T (gamma - gamma')) := by
  have hW := ThmD.admWindow_params hP h8
  have h := hW.hasSum_vHatR_mul T gamma gamma'
  simpa [dutDFullKernelRaw, ThmD.atD_phiHatR hP T,
    ThmD.atD_tau_eq, Params.atD_L] using h

/-- The raw kernel at zero is exactly `a L`, hence the normalized full-grid
kernel has unit diagonal once `a L` is nonzero. -/
lemma dutDFullKernelRaw_zero
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    dutDFullKernelRaw P T 0 = (P.atD T).a T * (P.atD T).L T := by
  have hW := ThmD.admWindow_params hP h8
  unfold dutDFullKernelRaw
  rw [hW.VPhiR_zero]
  rw [← ThmD.atD_a_eq_av hP T]
  simp

/-- Unit diagonal for the normalized full-grid kernel. -/
lemma dutDFullKernel_zero
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T) :
    dutDFullKernel P T 0 = 1 := by
  have hL : 0 < (P.atD T).L T := by
    rw [Params.atD_L]
    linarith [hP.one_le_w]
  have ha : 0 < (P.atD T).a T := by
    linarith [(ThmD.aD_range_of hP h8 h4pi).1]
  have hden : (P.atD T).a T * (P.atD T).L T ≠ 0 :=
    ne_of_gt (mul_pos ha hL)
  change dutDFullKernelRaw P T 0 /
    ((P.atD T).a T * (P.atD T).L T) = 1
  rw [dutDFullKernelRaw_zero P hP h8]
  exact div_self hden

/-- The full-grid kernel is even, inherited from the Fourier transform of the
even real function `phiD^2`. -/
lemma dutDFullKernel_even
    (P : Params) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (x : ℝ) :
    dutDFullKernel P T (-x) = dutDFullKernel P T x := by
  have hW := ThmD.admWindow_params hP h8
  unfold dutDFullKernel
  rw [hW.VPhiR_even]

end Zeta23.ZeroSide.RankTraceMult
