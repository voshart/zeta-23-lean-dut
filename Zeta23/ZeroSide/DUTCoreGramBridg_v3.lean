/-
DUTCoreGramBridge.lean

Identify the normalized scalar finite pair from DUTNormalizedFiniteBridge with
the actual entry of the six-column Gram matrix built from the concrete
interior-core Theorem-D vectors.

This closes the structural gap

  scalar finite pair  <->  actual W^H W entry.

After this file, the previously proved scalar sharp-kernel estimate becomes an
entrywise matrix estimate for the genuine six-zero Gram matrix.

Intended location:
  Zeta23/ZeroSide/DUTCoreGramBridge.lean
-/

import Zeta23.ZeroSide.DUTNormalizedFiniteBridge

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Actual six-by-six Gram matrix of the normalized interior-core Theorem-D
evaluation vectors. -/
noncomputable def dutCoreSixGramMatrixD
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  let v := dutCoreSixVhatD Z T P i hi
  let W := Wmat (fun _ : Fin 6 => (1 : ℝ)) v
  Wᴴ * W

lemma dutCoreSixGramMatrixD_posSemidef
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    (dutCoreSixGramMatrixD Z T P i hi).PosSemidef := by
  unfold dutCoreSixGramMatrixD
  exact Matrix.posSemidef_conjTranspose_mul_self _


/-- Generic entry formula for the Gram matrix of unit-weight columns.
Keeping this lemma polymorphic prevents simplification of the concrete DUT
row type from creating a `Fin (atD.d)` / `Fin d` elaboration mismatch. -/
private lemma Wmat_one_gram_apply
    {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    (v : ι → n → ℂ) (j l : ι) :
    ((Wmat (fun _ : ι => (1 : ℝ)) v)ᴴ *
        Wmat (fun _ : ι => (1 : ℝ)) v) j l
      =
      ∑ k : n, starRingEnd ℂ (v j k) * v l k := by
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply, Wmat, RCLike.star_def]

/-- Every core-block zero is on the critical line. -/
private lemma dutCoreSix_re_eq_half
    (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).re) = 1 / 2 := by
  change (dutCoreOrderedZero Z T (dutCoreSixIndex i hi j)).re = 1 / 2
  exact dutCoreOrderedZero_re Z T (dutCoreSixIndex i hi j)

/-- Explicit coordinate formula for the actual normalized core vectors:
on the critical line the complex Fourier evaluation is the real transform,
divided by the upstream normalization `sqrt(a_D L^2)`. -/
lemma dutCoreSixVhatD_apply_real
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j : Fin 6) (k : Fin ((P.atD T).d T)) :
    dutCoreSixVhatD Z T P i hi j k
      =
      ((P.atD T).phiHatR T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - (P.atD T).tau T k) : ℂ)
      /
      (Real.sqrt
        ((P.atD T).a T * (P.atD T).L T ^ 2) : ℂ) := by
  unfold dutCoreSixVhatD
  change
    (P.atD T).phiHat T
      (gammaOf (dutCoreSixZI Z T i hi j)
        - (P.atD T).tau T k)
      /
      (Real.sqrt
        ((P.atD T).a T * (P.atD T).L T ^ 2) : ℂ)
      = _
  rw [gammaOf_of_re_eq_half
      (dutCoreSix_re_eq_half Z T i hi j)]
  rw [← Complex.ofReal_sub]
  rw [dutD_phiHatReal]

/-- **Exact Gram-entry identification.**

The `(j,l)` entry of the genuine normalized six-vector Gram matrix is exactly
the real normalized finite pair sum used by DUTNormalizedFiniteBridge. -/
theorem dutCoreSixGramMatrixD_apply
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    dutCoreSixGramMatrixD Z T P i hi j l
      =
      (dutCoreSixNormalizedFinitePair Z T P i hi j l : ℂ) := by
  let c : ℝ :=
    (P.atD T).a T * (P.atD T).L T ^ 2
  have hc : 0 < c := by
    dsimp [c]
    exact dutD_normConst_pos hP h8 h4pi
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqrtC : (Real.sqrt c : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  have hsq : ((Real.sqrt c : ℂ)) ^ 2 = (c : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]

  unfold dutCoreSixGramMatrixD
  rw [Wmat_one_gram_apply]
  simp_rw [dutCoreSixVhatD_apply_real Z T P i hi]

  have hterm :
      ∀ k : Fin ((P.atD T).d T),
        starRingEnd ℂ
          (((P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
                - (P.atD T).tau T k) : ℂ) /
            (Real.sqrt c : ℂ))
        *
          (((P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
                - (P.atD T).tau T k) : ℂ) /
            (Real.sqrt c : ℂ))
        =
        (((P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
                - (P.atD T).tau T k)
          *
          (P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
                - (P.atD T).tau T k)
          / c : ℝ) : ℂ) := by
    intro k
    rw [map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [div_mul_div_comm, ← sq, hsq]
    push_cast

  rw [show
      (∑ k : Fin ((P.atD T).d T),
        starRingEnd ℂ
          (((P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
                - (P.atD T).tau T k) : ℂ) /
            (Real.sqrt c : ℂ))
        *
          (((P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
                - (P.atD T).tau T k) : ℂ) /
            (Real.sqrt c : ℂ)))
        =
      ∑ k : Fin ((P.atD T).d T),
        (((P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
                - (P.atD T).tau T k)
          *
          (P.atD T).phiHatR T
              (((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im
                - (P.atD T).tau T k)
          / c : ℝ) : ℂ) by
        apply Finset.sum_congr rfl
        intro k _
        exact hterm k]

  unfold dutCoreSixNormalizedFinitePair dutCoreSixRawFinitePair
  dsimp [c]
  rw [← Finset.sum_div]
  push_cast

/-- **Actual Gram entry -> sharp-cosine kernel.**

This is the matrix-entry form of the complete finite-grid truncation plus
taper/sharp-kernel comparison. -/
theorem dutCoreSixGramMatrixD_entry_close_sharp
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (hT : 0 < T)
    (h16 : 16 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgap2 :
      0 < D0 T - 2 * (P.atD T).hgrid T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T)
    (j l : Fin 6) :
    ‖dutCoreSixGramMatrixD Z T P i hi j l
      -
      (dutDSharpKernel P T
        (((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
          - ((dutCoreSixZI Z T i hi l : ZI Z T) : ℂ).im) : ℂ)‖
      ≤
      dutCoreSixNormalizedTailBudget T P
        + 40 * P.w / P.L T := by
  have hw0 : 0 ≤ P.w := le_trans zero_le_one hP.one_le_w
  have h8 : 8 * P.w ≤ P.L T := by
    linarith
  rw [dutCoreSixGramMatrixD_apply Z T P hP h8 h4pi i hi j l]
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact
    dutCoreSix_normalizedFinitePair_close_sharp
      Z T P hP hT h16 h4pi hgap2 i hi j l

end Zeta23.ZeroSide.RankTraceMult
