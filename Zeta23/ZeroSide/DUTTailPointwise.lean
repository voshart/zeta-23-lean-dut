/-
DUTTailPointwise.lean

Pointwise Fourier-tail bounds for interior-core six-zero blocks.

For the concrete Theorem-D window, AdmWindow supplies

  |vHatR(r)| * r^2 <= cDT / w.

Every zero in DUTInteriorBlocks lies sqrt(T) from the left grid edge and
sqrt(T)-h from the first omitted right-grid point.  This file combines those
facts to give explicit O(distance^-2) bounds for every omitted lattice sample.

No infinite summation is performed here; that is deliberately left to the
next module.

Intended location:
  Zeta23/ZeroSide/DUTTailPointwise.lean
-/

import Zeta23.ZeroSide.DUTInteriorBlocks

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Generic consequence of the `r^-2` Fourier decay estimate. -/
lemma dut_abs_vHatR_le_of_distance
    {v : ℝ → ℝ} {L w c r D : ℝ}
    (hW : AdmWindow v L w c)
    (hD : 0 < D)
    (hr : D ≤ |r|) :
    |AdmWindow.vHatR v r| ≤ (c / w) / D ^ 2 := by
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hsq : D ^ 2 ≤ r ^ 2 := by
    apply (sq_le_sq).2
    simpa [abs_of_pos hD] using hr
  have hmul :
      |AdmWindow.vHatR v r| * D ^ 2
        ≤ |AdmWindow.vHatR v r| * r ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have hdecay := hW.abs_vHatR_mul_sq_le r
  have hprod :
      |AdmWindow.vHatR v r| * D ^ 2 ≤ c / w :=
    hmul.trans hdecay
  rwa [le_div_iff₀ hD2]

/-- The Theorem-D Fourier transform itself satisfies the same distance bound. -/
lemma dutD_phiHatR_le_of_distance
    (P : Params) (hP : P.Valid) {T r D : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (hD : 0 < D)
    (hr : D ≤ |r|) :
    |(P.atD T).phiHatR T r|
      ≤ (ThmD.cDT P.ϱ P.lam / P.w) / D ^ 2 := by
  have hW := ThmD.admWindow_params hP h8
  rw [ThmD.atD_phiHatR hP T]
  exact dut_abs_vHatR_le_of_distance hW hD hr

/-- Every omitted lattice point to the left of the finite grid is at least
`sqrt(T)` away from an interior-core zero. -/
lemma dutCoreSix_left_abs_distance
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT : 0 < T) (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    {k : ℤ} (hk : k < 0) :
    D0 T ≤
      |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - (P.atD T).tau T k| := by
  have hdist :=
    dutCoreSix_left_of_grid Z T P hL i hi j hk
  have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have hr0 :
      0 ≤
        ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T k :=
    hD0.trans hdist
  rw [abs_of_nonneg hr0]
  exact hdist

/-- Pointwise `r^-2` bound for every omitted left-grid sample. -/
lemma dutCoreSix_phiHatR_left_tail
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T) (h8 : 8 * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    {k : ℤ} (hk : k < 0) :
    |(P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T k)|
      ≤ (ThmD.cDT P.ϱ P.lam / P.w) / (D0 T) ^ 2 := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hD : 0 < D0 T := by
    exact Real.sqrt_pos.2 hT
  exact dutD_phiHatR_le_of_distance
    P hP h8 hD
    (dutCoreSix_left_abs_distance Z T P hT hL i hi j hk)

/-- The lattice map `k ↦ tau_k` is monotone because the grid step is positive. -/
lemma dutD_tau_mono
    (P : Params) {T : ℝ} (hL : 0 < P.L T)
    {k m : ℤ} (hkm : k ≤ m) :
    (P.atD T).tau T k ≤ (P.atD T).tau T m := by
  have hh : 0 < (P.atD T).hgrid T := by
    have hhP : 0 < P.hgrid T := by
      unfold Params.hgrid
      positivity
    simpa using hhP
  have hcast : (k : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hkm
  unfold Params.tau
  nlinarith

/-- Every omitted lattice point to the right is at least
`sqrt(T)-h` away from an interior-core zero. -/
lemma dutCoreSix_right_abs_distance
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT : 0 ≤ T) (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    {k : ℤ} (hk : ((P.atD T).d T : ℤ) ≤ k) :
    D0 T - (P.atD T).hgrid T ≤
      |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - (P.atD T).tau T k| := by
  have hbase :=
    dutCoreSix_right_distance_at_d Z T P hL hT i hi j
  have htau :
      (P.atD T).tau T ((P.atD T).d T : ℤ)
        ≤ (P.atD T).tau T k :=
    dutD_tau_mono P hL hk
  have hdist :
      D0 T - (P.atD T).hgrid T
        ≤ (P.atD T).tau T k
          - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im := by
    linarith
  calc
    D0 T - (P.atD T).hgrid T
        ≤ (P.atD T).tau T k
            - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im := hdist
    _ ≤
        |(P.atD T).tau T k
            - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im| :=
      le_abs_self _
    _ =
        |((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - (P.atD T).tau T k| := by
      rw [abs_sub_comm]

/-- Pointwise `r^-2` bound for every omitted right-grid sample. -/
lemma dutCoreSix_phiHatR_right_tail
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 ≤ T) (h8 : 8 * P.w ≤ P.L T)
    (hgap : 0 < D0 T - (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    {k : ℤ} (hk : ((P.atD T).d T : ℤ) ≤ k) :
    |(P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T k)|
      ≤ (ThmD.cDT P.ϱ P.lam / P.w) /
          (D0 T - (P.atD T).hgrid T) ^ 2 := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  exact dutD_phiHatR_le_of_distance
    P hP h8 hgap
    (dutCoreSix_right_abs_distance Z T P hT hL i hi j hk)

end Zeta23.ZeroSide.RankTraceMult
