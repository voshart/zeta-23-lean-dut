/-
DUTZeroBlocks.lean

Concrete local six-zero bridge for DUT.

Starting from the canonical increasing enumeration of the actual simple
critical-line zeros in `ZI Z T` from DUTZeroOrder, form any six consecutive
simple zeros, view their upstream normalized evaluation vectors as a `Fin 6`
family, prove the required trace bound from the upstream finite Poisson lemma,
and feed the family into the already kernel-checked Gram rotation theorem.

This module does NOT assert the span-dependent defect certificate.  It closes
only the exact bridge

  actual ordered simple zeros -> upstream evalVec/vhat -> Poisson norm bound
  -> six-column Gram rotation + c=2 charge saving identity.

Intended location:
  Zeta23/ZeroSide/DUTZeroBlocks.lean
-/

import Zeta23.ZeroSide.Mult
import Zeta23.ZeroSide.DUTZeroOrder

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- The `j`th index in the consecutive six-block starting at zero-based index
`i`.  The hypothesis says the full block lies inside the ordered simple-zero
sequence. -/
def dutSixIndex {s : ℕ} (i : ℕ) (hi : i + 5 < s) (j : Fin 6) : Fin s :=
  ⟨i + j, by
    have hj : (j : ℕ) ≤ 5 := by omega
    omega⟩

@[simp] lemma coe_dutSixIndex {s : ℕ} (i : ℕ) (hi : i + 5 < s) (j : Fin 6) :
    ((dutSixIndex i hi j : Fin s) : ℕ) = i + j := rfl

/-- The `j`th actual simple zero in the consecutive six-block beginning at
`i`, as the concrete `ZI Z T` subtype used by upstream `evalVec`. -/
noncomputable def dutSixSimpleZI (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < Z.s1 T) (j : Fin 6) : ZI Z T :=
  dutOrderedSimpleZI Z T (dutSixIndex i hi j)

@[simp] lemma coe_dutSixSimpleZI (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < Z.s1 T) (j : Fin 6) :
    ((dutSixSimpleZI Z T i hi j : ZI Z T) : ℂ) =
      dutOrderedSimpleZero Z T (dutSixIndex i hi j) := rfl

/-- Each zero in a DUT six-block is on the critical line, hence belongs to the
upstream `onLine` subtype of the concrete block data. -/
noncomputable def dutSixSimpleOnLine
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) (j : Fin 6) :
    (blockData Z T P hconj).onLine :=
  ⟨dutSixSimpleZI Z T i hi j, by
    apply ((blockData Z T P hconj).mem_onLine).2
    rw [blockData, mkData_σ_eq_iff]
    simpa [dutSixSimpleZI] using
      dutOrderedSimpleZero_re Z T (dutSixIndex i hi j)⟩

/-- The actual upstream normalized evaluation vectors for six consecutive
simple zeros.  The normalization is exactly the one used in
`ZeroBlockData.vhat`, with `c = a L^2`. -/
noncomputable def dutSixVhat
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    Fin 6 → Fin (P.d T) → ℂ :=
  fun j =>
    (blockData Z T P hconj).vhat (P.a T * P.L T ^ 2)
      (dutSixSimpleOnLine Z T P hconj i hi j)

/-- Every vector in an actual consecutive DUT six-block has normalized squared
norm at most one, directly from the upstream finite Poisson bound. -/
lemma xsq_dutSixVhat_le_one
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T) (j : Fin 6) :
    xsq (dutSixVhat Z T P hconj i hi) j ≤ 1 := by
  let D := blockData Z T P hconj
  change xsq (D.vhat (P.a T * P.L T ^ 2))
    (dutSixSimpleOnLine Z T P hconj i hi j) ≤ 1
  exact D.xsq_vhat_le hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
    (dutSixSimpleOnLine Z T P hconj i hi j)

/-- Consequently the total squared norm of the six actual normalized columns
is at most six, exactly the hypothesis consumed by the verified finite
Gram-rotation theorem. -/
lemma sum_xsq_dutSixVhat_le_six
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    (∑ j, xsq (dutSixVhat Z T P hconj i hi) j) ≤ 6 := by
  calc
    (∑ j, xsq (dutSixVhat Z T P hconj i hi) j)
        ≤ ∑ _j : Fin 6, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            exact xsq_dutSixVhat_le_one Z T P hconj hreal hPois hc i hi j
    _ = 6 := by norm_num

/-- **Concrete local DUT bridge.** For every actual consecutive six-tuple of
simple critical-line zeros in the upstream finite window, the normalized
upstream evaluation vectors admit the verified Gram-eigenbasis rotation.  The
rotation preserves the represented positive matrix and yields the exact `c=2`
charge upper bound with spectral defect.

No span-dependent lower bound on the defect is assumed or proved here. -/
theorem dut_consecutive_six_rotated_charge_and_P
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (i : ℕ) (hi : i + 5 < Z.s1 T) :
    let v := dutSixVhat Z T P hconj i hi
    let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
    let vr := columns (gramEigenRotateMatrix W)
    Pmat (fun _ : Fin 6 => (1 : ℝ)) vr =
        Pmat (fun _ : Fin 6 => (1 : ℝ)) v
      ∧
    (∑ j, kc 2 (xsq vr j)) ≤
      18 - ∑ j, dutDefect2 (xsq vr j) := by
  exact fin6_rotated_charge_and_P
    (dutSixVhat Z T P hconj i hi)
    (sum_xsq_dutSixVhat_le_six Z T P hconj hreal hPois hc i hi)

end Zeta23.ZeroSide.RankTraceMult
