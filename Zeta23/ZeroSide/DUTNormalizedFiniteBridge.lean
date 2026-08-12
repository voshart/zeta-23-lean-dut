/-
DUTNormalizedFiniteBridge.lean

Normalize the raw finite-grid -> full-Poisson truncation bound and then combine
it with the already-checked full-Poisson -> sharp-cosine comparison.

For an interior-core six-zero pair j,l, define

  S_fin^hat = S_fin / (a_D L^2).

The raw bridge gives

  |S_fin - L * K_full_raw| <= E_tail.

After division by a_D L^2,

  |S_fin^hat - K_full| <= E_tail / (a_D L^2).

Combining with DUTNormalizedKernel gives

  |S_fin^hat - K_sharp|
    <= E_tail / (a_D L^2) + 40 w / L.

This file still treats the finite normalized pair as a real scalar.  The next
module identifies it entrywise with the actual complex Gram matrix WᴴW.

Intended location:
  Zeta23/ZeroSide/DUTNormalizedFiniteBridge.lean
-/

import Zeta23.ZeroSide.DUTFinitePoissonBridge
import Zeta23.ZeroSide.DUTNormalizedKernel

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Raw sum normalized by the exact upstream Theorem-D vector normalization
`a_D L^2`. -/
noncomputable def dutCoreSixNormalizedFinitePair
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) : ℝ :=
  dutCoreSixRawFinitePair Z T P i hi j l /
    ((P.atD T).a T * (P.atD T).L T ^ 2)

/-- The explicit raw truncation budget used below. -/
noncomputable def dutCoreSixRawTailBudget
    (T : ℝ) (P : Params) : ℝ :=
  2 * (dutDTailConst P) ^ 2 /
      ((D0 T) ^ 2 * ((P.atD T).hgrid T) ^ 2)
  +
  2 * (dutDTailConst P) ^ 2 /
      ((D0 T - 2 * (P.atD T).hgrid T) ^ 2
        * ((P.atD T).hgrid T) ^ 2)

/-- The normalized truncation budget. -/
noncomputable def dutCoreSixNormalizedTailBudget
    (T : ℝ) (P : Params) : ℝ :=
  dutCoreSixRawTailBudget T P /
    ((P.atD T).a T * (P.atD T).L T ^ 2)

lemma dutCoreSixRawTailBudget_nonneg
    (T : ℝ) (P : Params)
    (hD : 0 < D0 T)
    (hh : 0 < (P.atD T).hgrid T)
    (hgap2 : 0 < D0 T - 2 * (P.atD T).hgrid T) :
    0 ≤ dutCoreSixRawTailBudget T P := by
  unfold dutCoreSixRawTailBudget
  have hC : 0 ≤ (dutDTailConst P) ^ 2 := sq_nonneg _
  have hDden :
      0 < (D0 T) ^ 2 * ((P.atD T).hgrid T) ^ 2 := by
    positivity
  have hRden :
      0 <
        (D0 T - 2 * (P.atD T).hgrid T) ^ 2
          * ((P.atD T).hgrid T) ^ 2 := by
    positivity
  positivity

/-- Algebraic identification of the normalized full Poisson raw term:
`(L * Kraw)/(a L^2) = Kfull`. -/
private lemma dutD_full_raw_normalizes
    (P : Params) (hP : P.Valid) {T x : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T) :
    (P.L T * dutDFullKernelRaw P T x) /
        ((P.atD T).a T * (P.atD T).L T ^ 2)
      =
      dutDFullKernel P T x := by
  have hL : 0 < (P.atD T).L T := by
    rw [Params.atD_L]
    linarith [hP.one_le_w]
  have haD : 1 / 2 ≤ (P.atD T).a T :=
    (ThmD.aD_range_of hP h8 h4pi).1
  have ha : 0 < (P.atD T).a T := by
    linarith
  unfold dutDFullKernel dutDFullKernelRaw
  rw [Params.atD_L]
  field_simp [ha.ne', hL.ne']

/-- **Normalized finite-grid -> full-Poisson pair error.** -/
theorem dutCoreSix_normalizedFinitePair_close_full
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    |dutCoreSixNormalizedFinitePair Z T P i hi j l
      -
      dutDFullKernel P T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)|
      ≤
      dutCoreSixNormalizedTailBudget T P := by
  let x : ℝ :=
    ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
      - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im

  have hc :
      0 < (P.atD T).a T * (P.atD T).L T ^ 2 :=
    dutD_normConst_pos hP h8 h4pi

  have hraw :
      |dutCoreSixRawFinitePair Z T P i hi j l
        - P.L T * dutDFullKernelRaw P T x|
        ≤ dutCoreSixRawTailBudget T P := by
    simpa [x, dutCoreSixRawTailBudget] using
      dutCoreSix_rawFinitePair_close_full
        Z T P hP hT h8 hgap2 i hi j l

  have hscaled :
      |dutCoreSixRawFinitePair Z T P i hi j l /
          ((P.atD T).a T * (P.atD T).L T ^ 2)
        -
        (P.L T * dutDFullKernelRaw P T x) /
          ((P.atD T).a T * (P.atD T).L T ^ 2)|
        ≤
        dutCoreSixRawTailBudget T P /
          ((P.atD T).a T * (P.atD T).L T ^ 2) := by
    rw [← sub_div, abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right hraw hc.le

  have hnorm :
      (P.L T * dutDFullKernelRaw P T x) /
          ((P.atD T).a T * (P.atD T).L T ^ 2)
        = dutDFullKernel P T x :=
    dutD_full_raw_normalizes P hP h8 h4pi

  rw [hnorm] at hscaled
  simpa [dutCoreSixNormalizedFinitePair,
    dutCoreSixNormalizedTailBudget, x] using hscaled

/-- **Normalized finite-grid -> sharp cosine pair error.**

This is the complete scalar kernel-transfer estimate for a core six-block pair:
finite-grid truncation plus taper/sharp-kernel error. -/
theorem dutCoreSix_normalizedFinitePair_close_sharp
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    |dutCoreSixNormalizedFinitePair Z T P i hi j l
      -
      dutDSharpKernel P T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)|
      ≤
      dutCoreSixNormalizedTailBudget T P
        + 40 * P.w / P.L T := by
  have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
  have h8 : 8 * P.w ≤ P.L T := by
    linarith

  let x : ℝ :=
    ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
      - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im

  have hfin :
      |dutCoreSixNormalizedFinitePair Z T P i hi j l
        - dutDFullKernel P T x|
        ≤ dutCoreSixNormalizedTailBudget T P := by
    simpa [x] using
      dutCoreSix_normalizedFinitePair_close_full
        Z T P hP hT h8 h4pi hgap2 i hi j l

  have hsharp :
      |dutDFullKernel P T x - dutDSharpKernel P T x|
        ≤ 40 * P.w / P.L T :=
    dutDFullKernel_close_sharp P hP h16 h4pi x

  calc
    |dutCoreSixNormalizedFinitePair Z T P i hi j l
        - dutDSharpKernel P T x|
      ≤
      |dutCoreSixNormalizedFinitePair Z T P i hi j l
        - dutDFullKernel P T x|
      + |dutDFullKernel P T x - dutDSharpKernel P T x| := by
        exact abs_sub_le _ _ _
    _ ≤ dutCoreSixNormalizedTailBudget T P
          + 40 * P.w / P.L T :=
      add_le_add hfin hsharp

end Zeta23.ZeroSide.RankTraceMult
