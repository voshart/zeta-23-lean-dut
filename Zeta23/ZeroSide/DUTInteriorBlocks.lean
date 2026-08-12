/-
DUTInteriorBlocks.lean

Interior-core version of the concrete DUT six-zero blocks.

The finite Gabor grid occupies approximately [T, 2T].  A zero at an endpoint
cannot have a small finite-grid -> full-Poisson truncation error, because one
half of the centered lattice is missing.  The correct local object is therefore
the interior core

  [T + D0(T), 2T - D0(T)],   D0(T) = sqrt T.

This file:
  * defines the simple critical-line zeros in that core;
  * orders them canonically by ordinate;
  * forms six consecutive core blocks;
  * instantiates the actual Theorem-D normalized evaluation vectors;
  * proves the same trace <= 6 bound as for the enlarged-window blocks;
  * records the left/right distance-to-grid-edge inequalities needed by the
    forthcoming truncation estimate.

It intentionally does not yet bound the discarded boundary zero count.

Intended location:
  Zeta23/ZeroSide/DUTInteriorBlocks.lean
-/

import Zeta23.ZeroSide.DUTNormalizedKernel
import Zeta23.ZeroSide.DUTThmDBlocks
import Mathlib.Data.Finset.Sort

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Simple critical-line zeros in the interior core
`[T + sqrt T, 2T - sqrt T]`, represented inside the upstream finite `ZI`
container. -/
def dutCoreSimpleFinset (Z : ZeroConfig) (T : ℝ) : Finset ℂ :=
  (ZI Z T).filter fun ρ =>
    ρ.re = 1 / 2 ∧
    Z.mult ρ = 1 ∧
    T + D0 T ≤ ρ.im ∧
    ρ.im ≤ 2 * T - D0 T

/-- Number of simple critical-line zeros in the interior core. -/
def dutCoreCount (Z : ZeroConfig) (T : ℝ) : ℕ :=
  (dutCoreSimpleFinset Z T).card

/-- The finite type of interior-core simple zeros. -/
abbrev DUTCoreSimpleZero (Z : ZeroConfig) (T : ℝ) :=
  ↥(dutCoreSimpleFinset Z T)

lemma dutCoreSimpleZero_mem_ZI
    (Z : ZeroConfig) (T : ℝ) (z : DUTCoreSimpleZero Z T) :
    (z : ℂ) ∈ ZI Z T :=
  (Finset.mem_filter.mp z.2).1

lemma dutCoreSimpleZero_re
    (Z : ZeroConfig) (T : ℝ) (z : DUTCoreSimpleZero Z T) :
    (z : ℂ).re = 1 / 2 :=
  (Finset.mem_filter.mp z.2).2.1

lemma dutCoreSimpleZero_mult
    (Z : ZeroConfig) (T : ℝ) (z : DUTCoreSimpleZero Z T) :
    Z.mult (z : ℂ) = 1 :=
  (Finset.mem_filter.mp z.2).2.2.1

lemma dutCoreSimpleZero_lower
    (Z : ZeroConfig) (T : ℝ) (z : DUTCoreSimpleZero Z T) :
    T + D0 T ≤ (z : ℂ).im :=
  (Finset.mem_filter.mp z.2).2.2.2.1

lemma dutCoreSimpleZero_upper
    (Z : ZeroConfig) (T : ℝ) (z : DUTCoreSimpleZero Z T) :
    (z : ℂ).im ≤ 2 * T - D0 T :=
  (Finset.mem_filter.mp z.2).2.2.2.2

/-- On the critical line, ordinate remains injective after the core restriction. -/
lemma dutCoreSimpleZero_im_injective (Z : ZeroConfig) (T : ℝ) :
    Function.Injective (fun z : DUTCoreSimpleZero Z T => (z : ℂ).im) := by
  intro a b hab
  apply Subtype.ext
  apply Complex.ext
  · calc
      (a : ℂ).re = 1 / 2 := dutCoreSimpleZero_re Z T a
      _ = (b : ℂ).re := (dutCoreSimpleZero_re Z T b).symm
  · exact hab

/-- Order the core simple zeros by increasing ordinate. -/
noncomputable instance dutCoreSimpleZeroLinearOrder
    (Z : ZeroConfig) (T : ℝ) :
    LinearOrder (DUTCoreSimpleZero Z T) :=
  LinearOrder.lift'
    (fun z : DUTCoreSimpleZero Z T => (z : ℂ).im)
    (dutCoreSimpleZero_im_injective Z T)

lemma card_dutCoreSimpleZero (Z : ZeroConfig) (T : ℝ) :
    Fintype.card (DUTCoreSimpleZero Z T) = dutCoreCount Z T := by
  simpa [DUTCoreSimpleZero, dutCoreCount] using
    (Fintype.card_coe (dutCoreSimpleFinset Z T))

/-- Canonical increasing enumeration of all core simple zeros. -/
noncomputable def dutCoreOrderIso (Z : ZeroConfig) (T : ℝ) :
    Fin (dutCoreCount Z T) ≃o DUTCoreSimpleZero Z T :=
  Fintype.orderIsoFinOfCardEq
    (DUTCoreSimpleZero Z T)
    (card_dutCoreSimpleZero Z T)

/-- The `i`th core simple zero. -/
noncomputable def dutCoreOrderedZero
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) : ℂ :=
  ((dutCoreOrderIso Z T) i : DUTCoreSimpleZero Z T)

lemma dutCoreOrderedZero_re
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) :
    (dutCoreOrderedZero Z T i).re = 1 / 2 := by
  simpa [dutCoreOrderedZero] using
    dutCoreSimpleZero_re Z T ((dutCoreOrderIso Z T) i)

lemma dutCoreOrderedZero_mult
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) :
    Z.mult (dutCoreOrderedZero Z T i) = 1 := by
  simpa [dutCoreOrderedZero] using
    dutCoreSimpleZero_mult Z T ((dutCoreOrderIso Z T) i)

lemma dutCoreOrderedZero_lower
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) :
    T + D0 T ≤ (dutCoreOrderedZero Z T i).im := by
  simpa [dutCoreOrderedZero] using
    dutCoreSimpleZero_lower Z T ((dutCoreOrderIso Z T) i)

lemma dutCoreOrderedZero_upper
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) :
    (dutCoreOrderedZero Z T i).im ≤ 2 * T - D0 T := by
  simpa [dutCoreOrderedZero] using
    dutCoreSimpleZero_upper Z T ((dutCoreOrderIso Z T) i)

/-- The core ordered zero as the concrete upstream `ZI Z T` subtype. -/
noncomputable def dutCoreOrderedZI
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) :
    ZI Z T :=
  ⟨dutCoreOrderedZero Z T i,
    dutCoreSimpleZero_mem_ZI Z T ((dutCoreOrderIso Z T) i)⟩

@[simp] lemma coe_dutCoreOrderedZI
    (Z : ZeroConfig) (T : ℝ) (i : Fin (dutCoreCount Z T)) :
    ((dutCoreOrderedZI Z T i : ZI Z T) : ℂ) = dutCoreOrderedZero Z T i :=
  rfl

/-- Index of the `j`th zero of a consecutive six-block in the core sequence. -/
def dutCoreSixIndex {s : ℕ}
    (i : ℕ) (hi : i + 5 < s) (j : Fin 6) : Fin s :=
  ⟨i + j, by
    have hj : (j : ℕ) ≤ 5 := by omega
    omega⟩

/-- The `j`th actual core simple zero in a consecutive six-block. -/
noncomputable def dutCoreSixZI
    (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    ZI Z T :=
  dutCoreOrderedZI Z T (dutCoreSixIndex i hi j)

lemma dutCoreSix_lower
    (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    T + D0 T ≤ ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im := by
  exact dutCoreOrderedZero_lower Z T (dutCoreSixIndex i hi j)

lemma dutCoreSix_upper
    (Z : ZeroConfig) (T : ℝ)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im ≤
      2 * T - D0 T := by
  exact dutCoreOrderedZero_upper Z T (dutCoreSixIndex i hi j)

/-- Core zeros as upstream on-line points for the concrete Theorem-D window. -/
noncomputable def dutCoreSixOnLineD
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    (blockData Z T (P.atD T) (dutD_phiHatConj P T)).onLine :=
  ⟨dutCoreSixZI Z T i hi j, by
    apply ((blockData Z T (P.atD T) (dutD_phiHatConj P T)).mem_onLine).2
    rw [blockData, mkData_σ_eq_iff]
    exact dutCoreOrderedZero_re Z T (dutCoreSixIndex i hi j)⟩

/-- Actual normalized Theorem-D evaluation vectors for six consecutive
interior-core simple zeros. -/
noncomputable def dutCoreSixVhatD
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    Fin 6 → Fin ((P.atD T).d T) → ℂ :=
  fun j =>
    (blockData Z T (P.atD T) (dutD_phiHatConj P T)).vhat
      ((P.atD T).a T * (P.atD T).L T ^ 2)
      (dutCoreSixOnLineD Z T P i hi j)

/-- Poisson normalization still gives squared norm at most one for every
interior-core vector. -/
lemma xsq_dutCoreSixVhatD_le_one
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    xsq (dutCoreSixVhatD Z T P i hi) j ≤ 1 := by
  let D :=
    blockData Z T (P.atD T) (dutD_phiHatConj P T)
  change
    xsq
      (D.vhat ((P.atD T).a T * (P.atD T).L T ^ 2))
      (dutCoreSixOnLineD Z T P i hi j) ≤ 1
  exact D.xsq_vhat_le
    (dutD_normConst_pos hP h8 h4pi)
    (sum_normSq_v_le
      Z T (P.atD T)
      (dutD_phiHatConj P T)
      (dutD_phiHatReal P T)
      (ThmD.poissonSqD hP h8))
    (dutCoreSixOnLineD Z T P i hi j)

/-- Total core-block squared norm is at most six. -/
lemma sum_xsq_dutCoreSixVhatD_le_six
    (Z : ZeroConfig) (T : ℝ) (P : Params) (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) :
    (∑ j, xsq (dutCoreSixVhatD Z T P i hi) j) ≤ 6 := by
  calc
    (∑ j, xsq (dutCoreSixVhatD Z T P i hi) j)
        ≤ ∑ _j : Fin 6, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          exact xsq_dutCoreSixVhatD_le_one
            Z T P hP h8 h4pi i hi j
    _ = 6 := by norm_num

/-- The left omitted grid starts at least `D0(T)` away from every core zero:
for every negative integer grid index `k`, `tau_k <= T`. -/
lemma dutCoreSix_left_of_grid
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6)
    {k : ℤ} (hk : k < 0) :
    D0 T ≤
      ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im
        - (P.atD T).tau T k := by
  have hh : 0 < (P.atD T).hgrid T := by
    have hhP : 0 < P.hgrid T := by
      unfold Params.hgrid
      positivity
    simpa using hhP
  have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hk)
  have htau : (P.atD T).tau T k ≤ T := by
    unfold Params.tau
    nlinarith
  have hcore := dutCoreSix_lower Z T i hi j
  linarith

/-- First right-omitted grid point `k=d` lies to the right of
`2T-h`.  Hence every core zero is at least `D0(T)-h` away from it. -/
lemma dutCoreSix_right_distance_at_d
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T) (hT : 0 ≤ T)
    (i : ℕ) (hi : i + 5 < dutCoreCount Z T) (j : Fin 6) :
    D0 T - (P.atD T).hgrid T ≤
      (P.atD T).tau T ((P.atD T).d T : ℤ)
        - ((dutCoreSixZI Z T i hi j : ZI Z T) : ℂ).im := by
  have hLd : 0 < (P.atD T).L T := by simpa [Params.atD_L] using hL
  have hh : 0 < (P.atD T).hgrid T := by
    unfold Params.hgrid
    positivity
  have hdlt :
      T < (((P.atD T).d T : ℝ) + 1) * (P.atD T).hgrid T := by
    simp only [Params.atD_d, Params.atD_hgrid]
    have hfloor :
        P.L T * T / (2 * Real.pi) <
          (P.d T : ℝ) + 1 := by
      unfold Params.d
      exact Nat.lt_floor_add_one _
    have h2pi : 0 < 2 * Real.pi := by positivity
    have hcross :
        P.L T * T < ((P.d T : ℝ) + 1) * (2 * Real.pi) := by
      rw [div_lt_iff₀ h2pi] at hfloor
      exact hfloor
    unfold Params.hgrid
    calc
      T = (P.L T * T) / P.L T := by
        field_simp [hL.ne']
      _ < (((P.d T : ℝ) + 1) * (2 * Real.pi)) / P.L T := by
        exact (div_lt_div_iff_of_pos_right hL).2 hcross
      _ = ((P.d T : ℝ) + 1) * (2 * Real.pi / P.L T) := by
        ring
  have htau :
      2 * T - (P.atD T).hgrid T <
        (P.atD T).tau T ((P.atD T).d T : ℤ) := by
    unfold Params.tau
    push_cast
    nlinarith
  have hcore := dutCoreSix_upper Z T i hi j
  linarith

end Zeta23.ZeroSide.RankTraceMult
