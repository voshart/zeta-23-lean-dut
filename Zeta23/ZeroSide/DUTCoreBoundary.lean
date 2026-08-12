/-
DUTCoreBoundary.lean

Finite counting seam for passing from the interior DUT core back to the full
dyadic interval (T,2T].

The core used by the finite-grid -> Poisson comparison is

    [T + D0(T), 2T - D0(T)],    D0(T) = sqrt(T).

This file proves only exact finite/counting facts:

  * N0s(T + D0, 2T - D0) <= dutCoreCount;
  * for T >= 4,
      N0s(T,2T)
        <= dutCoreCount
           + N(T,T+D0) + N(2T-D0,2T);
  * the two discarded inside strips are dominated by shifted copies of the
    upstream boundary count NII:
      N(T,T+D0)       <= NII(T+D0),
      N(2T-D0,2T)     <= NII(2T).

The next module will use the already-proved upstream estimate
NII(U) = O(sqrt(U) l(U)) to show these discarded strips are o(N(T,2T)).

Intended location:
  Zeta23/ZeroSide/DUTCoreBoundary.lean
-/

import Zeta23.ZeroSide.DUTCorePhaseCertificate
import Zeta23.Assembly
import Zeta23.Tail

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- Monotonicity of the multiplicity-count `N` under interval inclusion. -/
lemma dut_N_mono_window
    (Z : ZeroConfig)
    {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    Z.N c d ≤ Z.N a b := by
  have hcb : c ≤ b := hcd.trans hdb
  rw [Assembly.N_add Z (a := a) (b := c) (c := b) hac hcb]
  rw [Assembly.N_add Z (a := c) (b := d) (c := b) hcd hdb]
  omega

/-- The strict-open middle interval counted by upstream `N0s` is contained in
our core finset.  Our core uses a closed lower endpoint, so this direction has
no endpoint-loss term. -/
lemma dutCore_middle_N0s_le_count
    (Z : ZeroConfig) (T : ℝ) :
    Z.N0s (T + D0 T) (2 * T - D0 T)
      ≤ dutCoreCount Z T := by
  unfold ZeroConfig.N0s
  let S : Set ℂ :=
    Z.window (T + D0 T) (2 * T - D0 T)
      ∩ ZeroConfig.onLine ∩ Z.simple
  have hsubset :
      S ⊆ (↑(dutCoreSimpleFinset Z T) : Set ℂ) := by
    intro ρ hρ
    dsimp [S] at hρ
    simp only [
      ZeroConfig.window,
      ZeroConfig.onLine,
      ZeroConfig.simple,
      Set.mem_inter_iff,
      Set.mem_setOf_eq
    ] at hρ
    rcases hρ with ⟨⟨⟨hcar, hlow, hupp⟩, hre⟩, hmult⟩

    change ρ ∈ dutCoreSimpleFinset Z T
    rw [dutCoreSimpleFinset, Finset.mem_filter]
    refine ⟨?_, hre, hmult, hlow.le, hupp⟩
    rw [mem_ZI, mem_ZIprime_iff]
    have hD : 0 ≤ D0 T := by
      simp [D0]
    exact ⟨hcar, by linarith, by linarith⟩

  have hfinite :
      ((↑(dutCoreSimpleFinset Z T) : Set ℂ)).Finite :=
    (dutCoreSimpleFinset Z T).finite_toSet

  have hcard := Set.ncard_le_ncard hsubset hfinite
  simpa [S, dutCoreCount] using hcard

/-- The two interior strips removed from `(T,2T]`. -/
def dutCoreBoundaryN (Z : ZeroConfig) (T : ℝ) : ℕ :=
  Z.N T (T + D0 T)
    + Z.N (2 * T - D0 T) (2 * T)

/-- For `T >= 4`, the core interval is nonempty in the ordered sense:
`T + sqrt(T) <= 2T - sqrt(T)`. -/
lemma dutCore_interval_order {T : ℝ} (hT4 : 4 ≤ T) :
    T + D0 T ≤ 2 * T - D0 T := by
  have hT0 : 0 ≤ T := by linarith
  have hD2 : D0 T ^ 2 = T := by
    simp [D0, Real.sq_sqrt hT0]
  have hDge2 : 2 ≤ D0 T := by
    unfold D0
    rw [Real.le_sqrt (by norm_num) hT0]
    norm_num
    exact hT4
  nlinarith

/-- Exact finite recovery of the full dyadic simple-zero count from the core,
up to the two discarded inside boundary strips. -/
theorem dutCoreCount_recovers_N0s
    (Z : ZeroConfig) (T : ℝ)
    (hT4 : 4 ≤ T) :
    Z.N0s T (2 * T)
      ≤ dutCoreCount Z T + dutCoreBoundaryN Z T := by
  have hD : 0 ≤ D0 T := by
    simp [D0]
  have hmidOrder :
      T + D0 T ≤ 2 * T - D0 T :=
    dutCore_interval_order hT4

  have hleft :
      Z.N0s T (T + D0 T)
        ≤ Z.N T (T + D0 T) := by
    have c := Z.trivial_chain T (T + D0 T)
    exact c.1.trans (c.2.1.trans c.2.2.1)

  have hmid :
      Z.N0s (T + D0 T) (2 * T - D0 T)
        ≤ dutCoreCount Z T :=
    dutCore_middle_N0s_le_count Z T

  have hright :
      Z.N0s (2 * T - D0 T) (2 * T)
        ≤ Z.N (2 * T - D0 T) (2 * T) := by
    have c := Z.trivial_chain (2 * T - D0 T) (2 * T)
    exact c.1.trans (c.2.1.trans c.2.2.1)

  have hsplit1 :=
    Assembly.N0s_add Z
      (a := T) (b := T + D0 T) (c := 2 * T)
      (by linarith) (hmidOrder.trans (by linarith))

  have hsplit2 :=
    Assembly.N0s_add Z
      (a := T + D0 T)
      (b := 2 * T - D0 T)
      (c := 2 * T)
      hmidOrder (by linarith)

  rw [hsplit1, hsplit2]
  unfold dutCoreBoundaryN
  omega

/-- The left discarded inside strip is contained in the *lower* upstream
boundary strip for the shifted height `S = T + sqrt(T)`. -/
lemma dutCore_left_boundary_le_shifted_NII
    (Z : ZeroConfig) (T : ℝ) :
    Z.N T (T + D0 T)
      ≤ Assembly.NII Z (T + D0 T) := by
  let S : ℝ := T + D0 T
  have hD : 0 ≤ D0 T := by
    simp [D0]
  have hTS : T ≤ S := by
    dsimp [S]
    linarith
  have hDsqrt :
      D0 T ≤ D0 S := by
    unfold D0
    exact Real.sqrt_le_sqrt hTS
  have hlow :
      S - D0 S ≤ T := by
    dsimp [S]
    linarith

  have hmono :
      Z.N T S ≤ Z.N (S - D0 S) S :=
    dut_N_mono_window Z hlow hTS le_rfl

  dsimp [S] at hmono ⊢
  unfold Assembly.NII
  omega

/-- The right discarded inside strip is contained in the *lower* upstream
boundary strip at height `2T`. -/
lemma dutCore_right_boundary_le_shifted_NII
    (Z : ZeroConfig) (T : ℝ)
    (hT0 : 0 ≤ T) :
    Z.N (2 * T - D0 T) (2 * T)
      ≤ Assembly.NII Z (2 * T) := by
  have hT2 : T ≤ 2 * T := by
    linarith
  have hDsqrt :
      D0 T ≤ D0 (2 * T) := by
    unfold D0
    exact Real.sqrt_le_sqrt hT2
  have hlow :
      2 * T - D0 (2 * T)
        ≤ 2 * T - D0 T := by
    linarith

  have hD : 0 ≤ D0 T := by
    simp [D0]

  have hinside :
      2 * T - D0 T ≤ 2 * T := by
    linarith

  have hmono :
      Z.N (2 * T - D0 T) (2 * T)
        ≤ Z.N (2 * T - D0 (2 * T)) (2 * T) :=
    dut_N_mono_window Z hlow hinside le_rfl

  unfold Assembly.NII
  omega

/-- Both discarded inside strips are controlled by shifted copies of the
already-analyzed upstream boundary count. -/
theorem dutCoreBoundaryN_le_shifted_NII
    (Z : ZeroConfig) (T : ℝ)
    (hT0 : 0 ≤ T) :
    dutCoreBoundaryN Z T
      ≤ Assembly.NII Z (T + D0 T)
        + Assembly.NII Z (2 * T) := by
  have hleft :=
    dutCore_left_boundary_le_shifted_NII Z T
  have hright :=
    dutCore_right_boundary_le_shifted_NII Z T hT0
  unfold dutCoreBoundaryN
  omega

end Zeta23.ZeroSide.RankTraceMult
