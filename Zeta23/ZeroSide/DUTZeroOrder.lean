/-
DUTZeroOrder.lean

First concrete bridge from Anthropic's ZeroConfig data to the finite six-phase
DUT bookkeeping: enumerate the simple critical-line zeros in the window by
increasing ordinate.

Intended location:
  Zeta23/ZeroSide/DUTZeroOrder.lean

This module intentionally does not yet build six-column Gabor blocks.  Its job
is only to make the ordered simple-zero sequence canonical and prove that it
has exactly Z.s1 T entries.
-/

import Zeta23.ZeroSide
import Zeta23.ZeroSide.DUTPhase
import Mathlib.Data.Finset.Sort

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The concrete finite set of simple critical-line zeros in the enlarged
window, written using the same finite `ZI` representation used by
`Zeta23.ZeroSide`. -/
def dutSimpleFinset (Z : ZeroConfig) (T : ℝ) : Finset ℂ :=
  (ZI Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)

/-- The concrete simple-zero finset has cardinality `Z.s1 T`. -/
lemma card_dutSimpleFinset (Z : ZeroConfig) (T : ℝ) :
    (dutSimpleFinset Z T).card = Z.s1 T := by
  rw [ZeroConfig.s1, S1_eq Z T, Set.ncard_coe_finset]
  rfl

/-- Simple critical-line zeros as a finite subtype. -/
abbrev DUTSimpleZero (Z : ZeroConfig) (T : ℝ) := ↥(dutSimpleFinset Z T)

lemma dutSimpleZero_mem_ZI (Z : ZeroConfig) (T : ℝ)
    (z : DUTSimpleZero Z T) : (z : ℂ) ∈ ZI Z T := by
  exact (Finset.mem_filter.mp z.2).1

lemma dutSimpleZero_re (Z : ZeroConfig) (T : ℝ)
    (z : DUTSimpleZero Z T) : (z : ℂ).re = 1 / 2 := by
  exact (Finset.mem_filter.mp z.2).2.1

lemma dutSimpleZero_mult (Z : ZeroConfig) (T : ℝ)
    (z : DUTSimpleZero Z T) : Z.mult (z : ℂ) = 1 := by
  exact (Finset.mem_filter.mp z.2).2.2

/-- On the critical line, the ordinate determines the zero uniquely. -/
lemma dutSimpleZero_im_injective (Z : ZeroConfig) (T : ℝ) :
    Function.Injective (fun z : DUTSimpleZero Z T => (z : ℂ).im) := by
  intro a b hab
  apply Subtype.ext
  apply Complex.ext
  · calc
      (a : ℂ).re = 1 / 2 := dutSimpleZero_re Z T a
      _ = (b : ℂ).re := (dutSimpleZero_re Z T b).symm
  · exact hab

/-- Order the simple zeros by increasing ordinate. -/
noncomputable instance dutSimpleZeroLinearOrder (Z : ZeroConfig) (T : ℝ) :
    LinearOrder (DUTSimpleZero Z T) :=
  LinearOrder.lift' (fun z : DUTSimpleZero Z T => (z : ℂ).im)
    (dutSimpleZero_im_injective Z T)

lemma card_dutSimpleZero (Z : ZeroConfig) (T : ℝ) :
    Fintype.card (DUTSimpleZero Z T) = Z.s1 T := by
  simpa [DUTSimpleZero] using card_dutSimpleFinset Z T

/-- Canonical increasing enumeration of all simple critical-line zeros. -/
noncomputable def dutSimpleOrderIso (Z : ZeroConfig) (T : ℝ) :
    Fin (Z.s1 T) ≃o DUTSimpleZero Z T :=
  Fintype.orderIsoFinOfCardEq (DUTSimpleZero Z T) (card_dutSimpleZero Z T)

/-- The `i`th simple critical-line zero, in increasing ordinate order. -/
noncomputable def dutOrderedSimpleZero (Z : ZeroConfig) (T : ℝ)
    (i : Fin (Z.s1 T)) : ℂ :=
  ((dutSimpleOrderIso Z T) i : DUTSimpleZero Z T)

lemma dutOrderedSimpleZero_mem_ZI (Z : ZeroConfig) (T : ℝ)
    (i : Fin (Z.s1 T)) : dutOrderedSimpleZero Z T i ∈ ZI Z T := by
  simpa [dutOrderedSimpleZero] using
    dutSimpleZero_mem_ZI Z T ((dutSimpleOrderIso Z T) i)

lemma dutOrderedSimpleZero_re (Z : ZeroConfig) (T : ℝ)
    (i : Fin (Z.s1 T)) : (dutOrderedSimpleZero Z T i).re = 1 / 2 := by
  simpa [dutOrderedSimpleZero] using
    dutSimpleZero_re Z T ((dutSimpleOrderIso Z T) i)

lemma dutOrderedSimpleZero_mult (Z : ZeroConfig) (T : ℝ)
    (i : Fin (Z.s1 T)) : Z.mult (dutOrderedSimpleZero Z T i) = 1 := by
  simpa [dutOrderedSimpleZero] using
    dutSimpleZero_mult Z T ((dutSimpleOrderIso Z T) i)

/-- The ordered enumeration is strictly increasing in ordinate. -/
lemma dutOrderedSimpleOrdinate_strictMono (Z : ZeroConfig) (T : ℝ) :
    StrictMono (fun i : Fin (Z.s1 T) => (dutOrderedSimpleZero Z T i).im) := by
  intro i j hij
  change
    (((dutSimpleOrderIso Z T) i : DUTSimpleZero Z T) : ℂ).im <
      (((dutSimpleOrderIso Z T) j : DUTSimpleZero Z T) : ℂ).im
  change (dutSimpleOrderIso Z T i) < (dutSimpleOrderIso Z T j)
  exact (dutSimpleOrderIso Z T).strictMono hij

lemma dutOrderedSimpleOrdinate_monotone (Z : ZeroConfig) (T : ℝ) :
    Monotone (fun i : Fin (Z.s1 T) => (dutOrderedSimpleZero Z T i).im) :=
  (dutOrderedSimpleOrdinate_strictMono Z T).monotone

/-- The ordered zero as the concrete `ZI Z T` subtype expected by
`evalVec` / `blockData`. -/
noncomputable def dutOrderedSimpleZI (Z : ZeroConfig) (T : ℝ)
    (i : Fin (Z.s1 T)) : ZI Z T :=
  ⟨dutOrderedSimpleZero Z T i, dutOrderedSimpleZero_mem_ZI Z T i⟩

@[simp] lemma coe_dutOrderedSimpleZI (Z : ZeroConfig) (T : ℝ)
    (i : Fin (Z.s1 T)) :
    ((dutOrderedSimpleZI Z T i : ZI Z T) : ℂ) = dutOrderedSimpleZero Z T i := rfl

end Zeta23.ZeroSide.RankTraceMult
