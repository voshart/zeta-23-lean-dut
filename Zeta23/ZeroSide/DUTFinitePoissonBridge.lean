/-
DUTFinitePoissonBridge.lean

Concrete finite-grid -> full-Poisson comparison for an interior-core six-zero
Theorem-D block.

The previous modules established:
  * exact full integer-grid pair sum (DUTFullPoissonKernel);
  * quantitative left/right omitted product tails (DUTTailProduct);
  * exact integer split into left + finite middle + right (DUTIntegerSplit).

This file combines those pieces and proves that the raw finite pair sum over
k = 0,...,d-1 differs from the exact full Poisson pair sum by at most the sum
of the two certified tail errors.

No normalization by a L^2 is performed here.  That is the next small bridge to
the actual normalized Gram matrix.

Intended location:
  Zeta23/ZeroSide/DUTFinitePoissonBridge.lean
-/

import Zeta23.ZeroSide.DUTIntegerSplit
import Zeta23.ZeroSide.DUTFullPoissonKernel

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Raw finite pair sum for two members of an interior-core six-zero block. -/
noncomputable def dutCoreSixRawFinitePair
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) : ℝ :=
  ∑ k : Fin ((P.atD T).d T),
    (P.atD T).phiHatR T
      (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - (P.atD T).tau T (((k : ℕ) : ℤ)))
    *
    (P.atD T).phiHatR T
      (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
        - (P.atD T).tau T (((k : ℕ) : ℤ)))

/-- The full integer pair summand attached to two core-block zeros. -/
private noncomputable def dutCoreSixPairTerm
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) (k : ℤ) : ℝ :=
  (P.atD T).phiHatR T
    (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
      - (P.atD T).tau T k)
  *
  (P.atD T).phiHatR T
    (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
      - (P.atD T).tau T k)

/-- Exact Poisson `HasSum` for the pair of actual core-block ordinates. -/
private lemma dutCoreSixPairTerm_hasSum
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    HasSum
      (dutCoreSixPairTerm Z T P i hi j l)
      (P.L T *
        dutDFullKernelRaw P T
          (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)) := by
  exact
    dutD_full_pair_hasSum P hP h8
      (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im)
      (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)

/-- Exact decomposition of the full Poisson pair sum into the negative tail,
the actual finite grid, and the right tail. -/
lemma dutCoreSix_full_eq_left_add_finite_add_right
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    P.L T *
        dutDFullKernelRaw P T
          (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)
      =
      (∑' n : ℕ,
        (P.atD T).phiHatR T
          (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutLeftTailIndex n))
        *
        (P.atD T).phiHatR T
          (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutLeftTailIndex n)))
      + dutCoreSixRawFinitePair Z T P i hi j l
      +
      (∑' n : ℕ,
        (P.atD T).phiHatR T
          (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutRightTailIndex P T n))
        *
        (P.atD T).phiHatR T
          (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
            - (P.atD T).tau T (dutRightTailIndex P T n))) := by
  let f : ℤ → ℝ := dutCoreSixPairTerm Z T P i hi j l
  have hfull :
      HasSum f
        (P.L T *
          dutDFullKernelRaw P T
            (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
              - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)) := by
    simpa [f] using
      dutCoreSixPairTerm_hasSum Z T P hP h8 i hi j l

  have hleft :
      Summable (fun n : ℕ => f (dutLeftTailIndex n)) := by
    simpa [Function.comp_def] using
      hfull.summable.comp_injective dutLeftTailIndex_injective

  have hright :
      Summable
        (fun n : ℕ =>
          f (dutRightIndexFrom ((P.atD T).d T) n)) := by
    simpa [Function.comp_def] using
      hfull.summable.comp_injective
        (dutRightIndexFrom_injective ((P.atD T).d T))

  have hsplit :=
    dut_hasSum_integer_split
      ((P.atD T).d T) hfull hleft hright

  simpa [f, dutCoreSixPairTerm, dutCoreSixRawFinitePair,
    dutMiddleIndex, dutRightIndexFrom, dutRightTailIndex] using hsplit

/-- **Raw finite-grid -> full-Poisson pair error.**

The finite pair sum differs from the exact full Poisson value by at most the
sum of the left and right omitted-tail bounds. -/
theorem dutCoreSix_rawFinitePair_close_full
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T)
    (hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    |dutCoreSixRawFinitePair Z T P i hi j l
      -
      P.L T *
        dutDFullKernelRaw P T
          (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
            - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)|
      ≤
      2 * (dutDTailConst P) ^ 2 /
          ((D0 T) ^ 2 * ((P.atD T).hgrid T) ^ 2)
      +
      2 * (dutDTailConst P) ^ 2 /
          ((D0 T - 2 * (P.atD T).hgrid T) ^ 2
            * ((P.atD T).hgrid T) ^ 2) := by
  have hsplit :=
    dutCoreSix_full_eq_left_add_finite_add_right
      Z T P hP h8 i hi j l

  let Ltail : ℝ :=
    ∑' n : ℕ,
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutLeftTailIndex n))
      *
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutLeftTailIndex n))

  let Rtail : ℝ :=
    ∑' n : ℕ,
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutRightTailIndex P T n))
      *
      (P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
          - (P.atD T).tau T (dutRightTailIndex P T n))

  have hsplit' :
      P.L T *
          dutDFullKernelRaw P T
            (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
              - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)
        =
        Ltail + dutCoreSixRawFinitePair Z T P i hi j l + Rtail := by
    simpa [Ltail, Rtail] using hsplit

  have hrewrite :
      dutCoreSixRawFinitePair Z T P i hi j l
        -
        P.L T *
          dutDFullKernelRaw P T
            (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
              - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im)
        = -(Ltail + Rtail) := by
    rw [hsplit']
    ring

  have hleft :
      |Ltail| ≤
        2 * (dutDTailConst P) ^ 2 /
          ((D0 T) ^ 2 * ((P.atD T).hgrid T) ^ 2) := by
    simpa [Ltail] using
      dutCoreSix_phiHatR_left_product_tsum_abs_le
        Z T P hP hT h8 i hi j l

  have hright :
      |Rtail| ≤
        2 * (dutDTailConst P) ^ 2 /
          ((D0 T - 2 * (P.atD T).hgrid T) ^ 2
            * ((P.atD T).hgrid T) ^ 2) := by
    simpa [Rtail] using
      dutCoreSix_phiHatR_right_product_tsum_abs_le
        Z T P hP hT.le h8 hgap2 i hi j l

  rw [hrewrite, abs_neg]
  exact (abs_add_le Ltail Rtail).trans (add_le_add hleft hright)

end Zeta23.ZeroSide.RankTraceMult
