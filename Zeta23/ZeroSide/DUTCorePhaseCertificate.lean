/-
DUTCorePhaseCertificate.lean

Specialize DUTPhaseCertificate to the actual interior-core simple zeros.

For fixed Z,T,P with at least six core simple zeros, extend the finite ordered
core sequence to a monotone Nat-indexed sequence by clamping indices at the
last core zero.  Normalize ordinates by L/(2*pi).

Then:
  * every valid consecutive six-window span is exactly
    `dutCoreSixNormalizedSpan`;
  * the full normalized core endpoint span is at most L*T/(2*pi);
  * hence the sum of all local certificate savings has the concrete lower bound

      eta * (R * (s-5) - 5 * L*T/(2*pi)),

    where s = dutCoreCount Z T;
  * the six-phase average gets exactly one sixth of this saving.

This is finite/global bookkeeping only.  It does not yet relate `dutCoreCount`
to the total simple-zero count; that boundary-strip estimate is the next layer.

Intended location:
  Zeta23/ZeroSide/DUTCorePhaseCertificate.lean
-/

import Zeta23.ZeroSide.DUTPhaseCertificate

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Clamp an arbitrary natural index to the final valid core-zero index. -/
def dutCoreClampIndex
    (Z : ZeroConfig) (T : ℝ)
    (hs : 1 ≤ dutCoreCount Z T) (n : ℕ) :
    Fin (dutCoreCount Z T) :=
  ⟨min n (dutCoreCount Z T - 1), by omega⟩

lemma dutCoreClampIndex_mono
    (Z : ZeroConfig) (T : ℝ)
    (hs : 1 ≤ dutCoreCount Z T)
    {a b : ℕ} (hab : a ≤ b) :
    dutCoreClampIndex Z T hs a ≤ dutCoreClampIndex Z T hs b := by
  change
    min a (dutCoreCount Z T - 1)
      ≤ min b (dutCoreCount Z T - 1)
  exact min_le_min hab le_rfl

/-- Normalized ordinate sequence, extended constantly after the last core zero. -/
noncomputable def dutCoreNormalizedOrdinate
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hs : 1 ≤ dutCoreCount Z T) (n : ℕ) : ℝ :=
  (P.L T / (2 * Real.pi)) *
    (dutCoreOrderedZero Z T (dutCoreClampIndex Z T hs n)).im

lemma dutCoreNormalizedOrdinate_monotone
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (hs : 1 ≤ dutCoreCount Z T) :
    Monotone (dutCoreNormalizedOrdinate Z T P hs) := by
  intro a b hab
  have hidx :=
    dutCoreClampIndex_mono Z T hs hab
  have him :
      (dutCoreOrderedZero Z T (dutCoreClampIndex Z T hs a)).im
        ≤
      (dutCoreOrderedZero Z T (dutCoreClampIndex Z T hs b)).im :=
    (dutCoreOrderedZero_im_strictMono Z T).monotone hidx
  unfold dutCoreNormalizedOrdinate
  exact
    mul_le_mul_of_nonneg_left him
      (by positivity : 0 ≤ P.L T / (2 * Real.pi))

/-- On a valid six-window start, the clamped normalized ordinate difference is
exactly the normalized span used by the local certificate. -/
lemma dutCoreNormalizedOrdinate_window_eq_span
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (i : ℕ) (hi : i ∈ Finset.range (dutCoreCount Z T - 5)) :
    let hs1 : 1 ≤ dutCoreCount Z T := by omega
    dutCoreNormalizedOrdinate Z T P hs1 (i + 5)
      - dutCoreNormalizedOrdinate Z T P hs1 i
      =
    dutCoreSixNormalizedSpan Z T P i (by
      have hi' : i < dutCoreCount Z T - 5 :=
        Finset.mem_range.mp hi
      omega) := by
  let hs1 : 1 ≤ dutCoreCount Z T := by omega
  have hi' : i < dutCoreCount Z T - 5 :=
    Finset.mem_range.mp hi
  have hi0 : i < dutCoreCount Z T := by omega
  have hi5 : i + 5 < dutCoreCount Z T := by omega
  let hblock : i + 5 < dutCoreCount Z T := hi5

  have hcl0 :
      dutCoreClampIndex Z T hs1 i = ⟨i, hi0⟩ := by
    apply Fin.ext
    simp [dutCoreClampIndex]
    omega

  have hcl5 :
      dutCoreClampIndex Z T hs1 (i + 5) = ⟨i + 5, hi5⟩ := by
    apply Fin.ext
    simp [dutCoreClampIndex]
    omega

  have hidx0 :
      dutCoreSixIndex i hblock (0 : Fin 6) = (⟨i, hi0⟩ : Fin (dutCoreCount Z T)) := by
    apply Fin.ext
    simp [dutCoreSixIndex]

  have hidx5 :
      dutCoreSixIndex i hblock (5 : Fin 6) =
        (⟨i + 5, hi5⟩ : Fin (dutCoreCount Z T)) := by
    apply Fin.ext
    simp [dutCoreSixIndex]

  dsimp only
  unfold dutCoreNormalizedOrdinate
  rw [hcl0, hcl5]
  unfold dutCoreSixNormalizedSpan dutNormalizedSixSpan dutCoreSixZI
  simp only [coe_dutCoreOrderedZI]
  rw [hidx0, hidx5]
  ring

/-- Certificate saving assigned to a core six-window start.  Outside the valid
start range it is set to zero; phase sums only use valid starts. -/
noncomputable def dutCoreWindowSaving
    (Z : ZeroConfig) (T : ℝ) (P : Params) (i : ℕ) : ℝ :=
  if hi : i + 5 < dutCoreCount Z T then
    dutCertificateRhs (dutCoreSixNormalizedSpan Z T P i hi)
  else
    0

lemma dutCoreWindowSaving_eq
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : ℕ) (hi : i ∈ Finset.range (dutCoreCount Z T - 5)) :
    let hblock : i + 5 < dutCoreCount Z T := by
      have hi' := Finset.mem_range.mp hi
      omega
    dutCoreWindowSaving Z T P i
      =
    dutCertificateRhs
      (dutCoreSixNormalizedSpan Z T P i hblock) := by
  have hi' : i < dutCoreCount Z T - 5 :=
    Finset.mem_range.mp hi
  have hblock : i + 5 < dutCoreCount Z T := by omega
  dsimp only
  simp [dutCoreWindowSaving, hblock]

/-- The normalized distance from the first to the final core zero is at most
`L*T/(2*pi)`.  This intentionally discards the favorable `2*sqrt(T)` margin. -/
lemma dutCoreNormalizedOrdinate_total_span_le
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T) :
    let hs1 : 1 ≤ dutCoreCount Z T := by omega
    dutCoreNormalizedOrdinate Z T P hs1
        (dutCoreCount Z T - 1)
      - dutCoreNormalizedOrdinate Z T P hs1 0
      ≤
    (P.L T / (2 * Real.pi)) * T := by
  let hs1 : 1 ≤ dutCoreCount Z T := by omega
  let s := dutCoreCount Z T

  have hlast_lt : s - 1 < s := by
    dsimp [s]
    omega

  have hcl0 :
      dutCoreClampIndex Z T hs1 0 = (⟨0, by omega⟩ : Fin s) := by
    apply Fin.ext
    simp [dutCoreClampIndex, s]

  have hclLast :
      dutCoreClampIndex Z T hs1 (s - 1) =
        (⟨s - 1, hlast_lt⟩ : Fin s) := by
    apply Fin.ext
    simp [dutCoreClampIndex, s]

  have hD0 : 0 ≤ D0 T := by
    simp [D0]

  have hfirst :
      T ≤
        (dutCoreOrderedZero Z T
          (⟨0, by
            dsimp [s]
            omega⟩ : Fin s)).im := by
    have h :=
      dutCoreOrderedZero_lower Z T
        (⟨0, by
          dsimp [s]
          omega⟩ : Fin s)
    linarith

  have hlast :
      (dutCoreOrderedZero Z T
        (⟨s - 1, hlast_lt⟩ : Fin s)).im
        ≤ 2 * T := by
    have h :=
      dutCoreOrderedZero_upper Z T
        (⟨s - 1, hlast_lt⟩ : Fin s)
    linarith

  have himspan :
      (dutCoreOrderedZero Z T
          (⟨s - 1, hlast_lt⟩ : Fin s)).im
        -
      (dutCoreOrderedZero Z T
          (⟨0, by
            dsimp [s]
            omega⟩ : Fin s)).im
        ≤ T := by
    linarith

  have hscale :
      0 ≤ P.L T / (2 * Real.pi) := by positivity

  dsimp only
  unfold dutCoreNormalizedOrdinate
  change
    (P.L T / (2 * Real.pi)) *
        (dutCoreOrderedZero Z T
          (dutCoreClampIndex Z T hs1 (s - 1))).im
      -
    (P.L T / (2 * Real.pi)) *
        (dutCoreOrderedZero Z T
          (dutCoreClampIndex Z T hs1 0)).im
      ≤
    (P.L T / (2 * Real.pi)) * T
  rw [hcl0, hclLast]
  calc
    (P.L T / (2 * Real.pi)) *
          (dutCoreOrderedZero Z T
            (⟨s - 1, hlast_lt⟩ : Fin s)).im
        -
      (P.L T / (2 * Real.pi)) *
          (dutCoreOrderedZero Z T
            (⟨0, by
              dsimp [s]
              omega⟩ : Fin s)).im
        =
      (P.L T / (2 * Real.pi)) *
        ((dutCoreOrderedZero Z T
            (⟨s - 1, hlast_lt⟩ : Fin s)).im
          -
         (dutCoreOrderedZero Z T
            (⟨0, by
              dsimp [s]
              omega⟩ : Fin s)).im) := by ring
    _ ≤ (P.L T / (2 * Real.pi)) * T :=
      mul_le_mul_of_nonneg_left himspan hscale

/-- **Concrete total certificate saving over all core six-windows.** -/
theorem dutCore_certificate_sum_all_six_windows
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T) :
    dutEta *
        (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
          - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤
      ∑ i ∈ Finset.range (dutCoreCount Z T - 5),
        dutCoreWindowSaving Z T P i := by
  let hs1 : 1 ≤ dutCoreCount Z T := by omega
  let y : ℕ → ℝ := dutCoreNormalizedOrdinate Z T P hs1

  have hmono : Monotone y := by
    dsimp [y]
    exact dutCoreNormalizedOrdinate_monotone Z T P hL hs1

  have hgeneric :=
    dut_certificate_sum_all_six_windows
      y hs6 hmono

  have hsum :
      (∑ i ∈ Finset.range (dutCoreCount Z T - 5),
        dutCertificateRhs (y (i + 5) - y i))
      =
      ∑ i ∈ Finset.range (dutCoreCount Z T - 5),
        dutCoreWindowSaving Z T P i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hspan :=
      dutCoreNormalizedOrdinate_window_eq_span
        Z T P hs6 i hi
    have hsave :=
      dutCoreWindowSaving_eq Z T P i hi
    dsimp [y] at hspan
    rw [hspan, hsave]

  rw [hsum] at hgeneric

  have hlength :=
    dutCoreNormalizedOrdinate_total_span_le
      Z T P hL hs6
  dsimp [y] at hlength

  have hbase :
      dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
          - 5 * ((P.L T / (2 * Real.pi)) * T)
        ≤
      dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
          - 5 *
            (y (dutCoreCount Z T - 1) - y 0) := by
    linarith

  have hscaled :=
    mul_le_mul_of_nonneg_left hbase dutEta_nonneg

  exact hscaled.trans hgeneric

/-- **Concrete six-phase averaged consequence on the interior core.**

Any six phase-wise global inequalities whose savings are the disjoint core
window contributions average to the explicit DUT global saving term. -/
theorem dutCore_certificate_phase_averaged_counting
    {simple Lbase : ℝ}
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 < P.L T)
    (hs6 : 6 ≤ dutCoreCount Z T)
    (hphase :
      ∀ r ∈ Finset.range 6,
        Lbase
          + dutPhaseContribution
              (dutCoreWindowSaving Z T P)
              (dutCoreCount Z T) r
          ≤ simple) :
    Lbase
      + (dutEta / 6) *
          (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
            - 5 * ((P.L T / (2 * Real.pi)) * T))
      ≤ simple := by
  have havg :
      Lbase
        + (1 / 6 : ℝ) *
            (∑ i ∈ Finset.range (dutCoreCount Z T - 5),
              dutCoreWindowSaving Z T P i)
        ≤ simple :=
    dut_phase_averaged_counting
      (delta := dutCoreWindowSaving Z T P)
      (s := dutCoreCount Z T)
      hphase

  have hsave :=
    dutCore_certificate_sum_all_six_windows
      Z T P hL hs6

  have hscale :
      (1 / 6 : ℝ) *
          (dutEta *
            (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
              - 5 * ((P.L T / (2 * Real.pi)) * T)))
        ≤
      (1 / 6 : ℝ) *
          (∑ i ∈ Finset.range (dutCoreCount Z T - 5),
            dutCoreWindowSaving Z T P i) :=
    mul_le_mul_of_nonneg_left hsave
      (by norm_num : (0 : ℝ) ≤ 1 / 6)

  have hreassoc :
      (1 / 6 : ℝ) *
          (dutEta *
            (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
              - 5 * ((P.L T / (2 * Real.pi)) * T)))
        =
      (dutEta / 6) *
          (dutR * ((dutCoreCount Z T - 5 : ℕ) : ℝ)
            - 5 * ((P.L T / (2 * Real.pi)) * T)) := by
    ring

  rw [hreassoc] at hscale
  linarith

end Zeta23.ZeroSide.RankTraceMult
