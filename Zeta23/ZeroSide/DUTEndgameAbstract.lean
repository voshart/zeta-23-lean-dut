/-
DUTEndgameAbstract.lean

Abstract eventual DUT endgame.

This mirrors Zeta23.ThmD.thmD_abstract, but replaces the ordinary block input
by the verified six-block DUT chain and targets simple critical-line zeros.
The fixed-T DUT saving is self-bootstrapped and all additional DUT error terms
are absorbed into o(N).

Intended location:
  Zeta23/ZeroSide/DUTEndgameAbstract.lean
-/

import Zeta23.ThmD.Endgame
import Zeta23.ZeroSide.DUTAssemblyBootstrapAllCore
import Zeta23.ZeroSide.DUTAssemblyC
import Zeta23.ZeroSide.DUTSelfBootstrap
import Zeta23.ZeroSide.DUTExtraErrorAsymptotic
import Zeta23.ZeroSide.DUTPhaseReplacementEventually
import Zeta23.ZeroSide.DUTLocalEventually

noncomputable section
set_option linter.unusedSectionVars false

open Filter Asymptotics Topology Real
open Matrix Finset RHLinalg
open scoped Topology BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

open Zeta23 Classical

/-- DUT-strengthened Theorem-D A-line, at fixed lambda.

The conclusion is on the simple critical-line zero count `N0s`, with limiting
coefficient `dutRate c P.lam`. -/
theorem dut_thmD_simple_abstract
    (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr :
      ThmD.TracesBoundsD
        P aT bT JT trG trG2
        (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc :
      Tendsto
        (fun T =>
          ThmD.cRatio
            (P.lam1 T) (aT T) (bT T) (JT T))
        atTop (𝓝 c))
    (ha :
      ∀ᶠ T in atTop,
        1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hcert : DUTSharpVerifierCertificate P)
    (θ₀ : ℝ → ℝ)
    (hTail :
      ∀ᶠ T in atTop,
        Assembly.TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ :
      ∃ C : ℝ,
        ∀ᶠ T in atTop,
          θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII :
      ∃ C : ℝ,
        ∀ᶠ T in atTop,
          (Assembly.NII Z T : ℝ)
            ≤ C * Real.sqrt T * l T)
    (hGzGp :
      ∀ᶠ T in atTop,
        Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId :
      ∀ᶠ T in atTop,
        (P.atD T).trGtilde T = trG T
        ∧ (P.atD T).trGtildeSq T = trG2 T
        ∧ (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (dutRate c P.lam - ε)
          * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le

  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII

  set N : ℝ → ℝ :=
    fun T => (Z.N T (2 * T) : ℝ)
    with hNdef

  set cinv : ℝ → ℝ :=
    fun T =>
      (ThmD.cRatio
        (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
    with hcinv

  set R₁ : ℝ → ℝ :=
    fun T => C₁ * Real.sqrt (P.X T) / aT T
    with hR₁

  set R₂ : ℝ → ℝ :=
    fun T => C₂ * P.calE T * (cinv T * N T)
    with hR₂

  set B : ℝ → ℝ :=
    fun T => θ₀ T / (aT T * P.L T)
    with hBdef

  set baseErr : ℝ → ℝ :=
    fun T =>
      4 * R₁ T + R₂ T
        + 3 * (Assembly.NII Z T : ℝ)
        + B T *
            (4
              + 2 * Real.sqrt
                  (cinv T * N T + R₂ T)
              + B T)
    with hbaseErr

  set dutErr : ℝ → ℝ :=
    fun T =>
      dutQ * (dutCoreBoundaryN Z T : ℝ)
        + 5 * dutQ
        + 5 * dutBeta *
            ((P.L T / (2 * Real.pi)) * T
              - P.lam * N T)
    with hdutErr

  set err : ℝ → ℝ :=
    fun T =>
      baseErr T
        + |cinv T - c⁻¹| * N T
        + dutErr T
    with herr

  set errScaled : ℝ → ℝ :=
    fun T => err T / dutDen
    with herrScaled

  have hcinv_to :
      Tendsto cinv atTop (𝓝 c⁻¹) :=
    hc.inv₀ hc0.ne'

  have hlocal :=
    dutCoreSix_local_hypotheses_eventually P hP

  have hphase :=
    dutPhaseReplacementResult_eventually
      P hP hcert

  ------------------------------------------------------------------
  -- (1) strengthened main inequality, eventually in T
  ------------------------------------------------------------------
  have hmain :
      ∀ᶠ T in atTop,
        dutRate c P.lam * N T
            - errScaled T
          ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [
      hTail,
      hGzGp,
      hId,
      ha,
      hlocal,
      hphase,
      eventually_ge_atTop T₁,
      eventually_ge_atTop T₂,
      eventually_ge_atTop (4 : ℝ),
      Assembly.eventually_l_pos,
      Assembly.eventually_calE_nonneg
        P hlam0 (zero_le_one.trans hP.one_le_w)
    ] with T hTl hGG hid ha2 hloc hphaseT hT₁ hT₂ hT4 hl hE0

    obtain ⟨hidtr, hidfr, hida⟩ := hid
    rcases hloc with
      ⟨hTpos, h16, h4pi, hgap2, hentry0, hloss⟩

    have hw0 : 0 ≤ P.w :=
      le_trans zero_le_one hP.one_le_w

    have h8 : 8 * P.w ≤ P.L T := by
      nlinarith

    have hT0 : 0 ≤ T := by
      linarith

    have hapos' : 0 < aT T := by
      linarith [ha2.1]

    have haposD : 0 < (P.atD T).a T := by
      rw [hida]
      exact hapos'

    have hLpos : 0 < P.L T := by
      simp only [Params.L]
      positivity

    have hrepZ :
        ∀ r ∈ Finset.range 6,
          DUTPhaseReplacementResult Z T P r := by
      intro r hr
      exact hphaseT Z r hr

    have hA :=
      dut_seamA_N0s_bootstrap_all_core
        Z T P hP hT4 hTl haposD
        h8 h4pi hrepZ

    have hrt :
        rtrace
            ((P.atD T).hat T
              (Z.Gz (P.atD T) T))
          =
        (aT T * P.L T)⁻¹ * trG T := by
      rw [
        Assembly.rtrace_hat,
        hGG,
        Assembly.rtrace_tilde_Gp,
        hidtr,
        hida
      ]
      rfl

    have hfr :
        frobSq
            ((P.atD T).hat T
              (Z.Gz (P.atD T) T))
          =
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [
        Assembly.frobSq_hat,
        hGG,
        Assembly.frobSq_tilde_Gp,
        hidfr,
        hida
      ]
      rfl

    have haL :
        (P.atD T).a T * (P.atD T).L T
          = aT T * P.L T := by
      rw [hida]
      rfl

    rw [hrt, hfr, haL] at hA

    have htr :
        |(aT T * P.L T)⁻¹ * trG T - N T|
          ≤ R₁ T :=
      Assembly.trGhat_sub_N_le
        hapos' hLpos
        (by simpa only using htr1 T hT₁)

    have hfrb :
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
          ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 :
          trG2 T / (aT T * P.L T) ^ 2
              - cinv T * N T
            ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact
          le_trans
            (le_trans (le_max_left _ 0) (le_abs_self _))
            h
      have e :
          ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
            =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]
      simp only [hR₂]
      linarith

    have hB0 : 0 ≤ B T :=
      div_nonneg
        hTl.theta_nonneg
        (mul_pos hapos' hLpos).le

    have hA' :
        4 * ((aT T * P.L T)⁻¹ * trG T)
          - (((aT T * P.L T)⁻¹) ^ 2 * trG2 T)
          - 2 * N T
          - 3 * (Assembly.NII Z T : ℝ)
          - B T *
              (4
                + 2 * Real.sqrt
                    (((aT T * P.L T)⁻¹) ^ 2 * trG2 T)
                + B T)
          + (dutEta / 6) *
              (dutR *
                  ((Z.N0s T (2 * T) : ℝ)
                    - (dutCoreBoundaryN Z T : ℝ) - 5)
                - 5 *
                    ((P.L T / (2 * Real.pi)) * T))
          ≤ (Z.N0s T (2 * T) : ℝ) := by
      simpa only [hBdef, hNdef] using hA

    have hcfix :=
      dut_N0s_lower_c_with_saving
        hB0 hA' htr hfrb

    have hcfix' :
        (2 - cinv T) * N T
          - baseErr T
          + dutBeta *
              (dutR *
                  ((Z.N0s T (2 * T) : ℝ)
                    - (dutCoreBoundaryN Z T : ℝ) - 5)
                - 5 *
                    ((P.L T / (2 * Real.pi)) * T))
          ≤ (Z.N0s T (2 * T) : ℝ) := by
      simpa only [
        hbaseErr, hR₁, hR₂, hBdef, hNdef,
        dutBeta
      ] using hcfix

    have hself :=
      dut_self_bootstrap_rearrange
        (N := N T)
        (N0s := (Z.N0s T (2 * T) : ℝ))
        (cinv := cinv T)
        (c := c)
        (lam := P.lam)
        (baseErr := baseErr T)
        (boundary := (dutCoreBoundaryN Z T : ℝ))
        (length := (P.L T / (2 * Real.pi)) * T)
        hcfix'

    have hN0 : 0 ≤ N T :=
      Nat.cast_nonneg _

    have hdrift :
        (cinv T - c⁻¹) * N T
          ≤ |cinv T - c⁻¹| * N T :=
      mul_le_mul_of_nonneg_right
        (le_abs_self (cinv T - c⁻¹))
        hN0

    have hscaled :
        dutNumer c P.lam * N T
            - err T
          ≤
        dutDen * (Z.N0s T (2 * T) : ℝ) := by
      calc
        dutNumer c P.lam * N T - err T
            =
          dutNumer c P.lam * N T
            - (baseErr T
              + |cinv T - c⁻¹| * N T
              + dutErr T) := by
                rw [herr]
        _ ≤
          dutNumer c P.lam * N T
            - (baseErr T
              + (cinv T - c⁻¹) * N T
              + dutErr T) := by
                gcongr
        _ ≤
          dutDen * (Z.N0s T (2 * T) : ℝ) := by
                simpa only [hdutErr, add_assoc] using hself

    have hdiv :=
      dut_divide_scaled_bound
        (A := dutNumer c P.lam)
        (N := N T)
        (N0s := (Z.N0s T (2 * T) : ℝ))
        (err := err T)
        hscaled

    change
      (dutNumer c P.lam / dutDen) * N T
          - err T / dutDen
        ≤ (Z.N0s T (2 * T) : ℝ)
    exact hdiv

  ------------------------------------------------------------------
  -- (2) the complete error is o(N)
  ------------------------------------------------------------------
  have hNtop :
      Tendsto N atTop atTop := by
    simpa only [hNdef] using
      Assembly.tendsto_N_atTop Z H.RvM

  have o1 : R₁ =o[atTop] N := by
    have hbd :
        (fun T => C₁ / aT T)
          =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Assembly.isBigO_one_of_abs_le
        (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [
        abs_of_nonneg
          (div_nonneg hC₁.le
            (by linarith [ha2.1]))
      ]
      rw [div_le_iff₀ (by linarith [ha2.1])]
      nlinarith [ha2.1]

    have hh :=
      Assembly.isLittleO_of_bdd_mul hbd
        (Assembly.isLittleO_N_of_isLittleO_Tl
          Z H.RvM
          (Assembly.isLittleO_sqrtX_Tl
            P hlam0 hlam1))

    exact
      hh.congr_left fun T => by
        simp only [hR₁]
        ring

  have hcinv_bd :
      ∀ᶠ T in atTop,
        0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ :=
      inv_pos.mpr hc0
    filter_upwards [
      hcinv_to.eventually
        (eventually_ge_nhds hcpos),
      hcinv_to.eventually
        (eventually_le_nhds
          (show c⁻¹ < 2 * c⁻¹ by linarith))
    ] with T h1 h2
    exact ⟨h1, h2⟩

  have hcinvO :
      cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine Assembly.isBigO_one_of_abs_le
      (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2

  have o2 : R₂ =o[atTop] N := by
    have hcE0 :
        Tendsto
          (fun T => C₂ * P.calE T)
          atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂

    have i1 :
        (fun T => cinv T * N T)
          =O[atTop] N := by
      have hh :=
        hcinvO.mul
          (isBigO_refl N atTop)
      simpa using hh

    have hoE :
        (fun T => C₂ * P.calE T)
          =o[atTop] (fun _ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 hcE0

    have hh :=
      hoE.mul_isBigO i1

    simpa only [hR₂, one_mul] using hh

  have o3 :
      (fun T => (Assembly.NII Z T : ℝ))
        =o[atTop] N := by
    have hO :
        (fun T => (Assembly.NII Z T : ℝ))
          =O[atTop]
        (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [
        hII,
        Assembly.eventually_l_pos
      ] with T h hl
      rw [
        Real.norm_eq_abs,
        Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)
      ]
      simpa [mul_assoc] using h

    exact
      hO.trans_isLittleO
        (Assembly.isLittleO_N_of_isLittleO_Tl
          Z H.RvM
          Assembly.isLittleO_sqrt_mul_l_Tl)

  have o4 :
      Tendsto B atTop (𝓝 0) := by
    have hup :
        Tendsto
          (fun T =>
            2 * |Cθ| *
              (l T * T ^ (P.lam / 2 - 1)
                / P.L T))
          atTop (𝓝 0) := by
      simpa using
        (Assembly.tendsto_theta_over_L
          P hlam0 hlam1).const_mul
            (2 * |Cθ|)

    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hup ?_ ?_

    · filter_upwards [
        hTail,
        ha,
        Assembly.eventually_l_pos
      ] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by
        simp only [Params.L]
        positivity
      exact
        div_nonneg
          hTl.theta_nonneg
          (by nlinarith [ha2.1])

    · filter_upwards [
        hTail,
        ha,
        Assembly.eventually_l_pos,
        hθ,
        eventually_gt_atTop (0 : ℝ)
      ] with T hTl ha2 hl hθT hT0

      have hLpos : 0 < P.L T := by
        simp only [Params.L]
        positivity

      have hapos' : 0 < aT T := by
        linarith [ha2.1]

      have hq :
          0 ≤
            l T * T ^ (P.lam / 2 - 1)
              / P.L T := by
        positivity

      simp only [hBdef]
      rw [
        div_le_iff₀
          (mul_pos hapos' hLpos)
      ]

      calc
        θ₀ T
            ≤ Cθ * l T
                * T ^ (P.lam / 2 - 1) :=
          hθT
        _ ≤ |Cθ| * l T
                * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ =
            |Cθ| *
                (l T * T ^ (P.lam / 2 - 1)
                  / P.L T)
              * P.L T := by
          field_simp
        _ ≤
            (2 * |Cθ| *
                (l T * T ^ (P.lam / 2 - 1)
                  / P.L T))
              * (aT T * P.L T) := by
          have hh :
              |Cθ| *
                  (l T * T ^ (P.lam / 2 - 1)
                    / P.L T)
                * P.L T
                =
              (2 * |Cθ| *
                  (l T * T ^ (P.lam / 2 - 1)
                    / P.L T))
                * (1 / 2 * P.L T) := by
            ring
          rw [hh]
          gcongr
          exact ha2.1

  have obase :
      baseErr =o[atTop] N := by
    have hh :=
      Assembly.err_isLittleO
        (R₁ := R₁)
        (R₂ := R₂)
        (NII := fun T =>
          (Assembly.NII Z T : ℝ))
        (B := B)
        (cl := cinv)
        hNtop o1 o2 o3 o4 hcinv_bd
    simpa only [hbaseErr] using hh

  have odrift :
      (fun T =>
        |cinv T - c⁻¹| * N T)
        =o[atTop] N := by
    refine
      Assembly.isLittleO_of_tendsto_zero_mul ?_
    have hh :
        Tendsto
          (fun T => cinv T - c⁻¹)
          atTop (𝓝 0) := by
      simpa using
        hcinv_to.sub_const c⁻¹
    simpa using hh.abs

  have odut :
      dutErr =o[atTop] N := by
    have hh :=
      dutExtraError_isLittleO_N
        Z H P
    simpa only [hdutErr, hNdef] using hh

  have herr_o :
      err =o[atTop] N := by
    have hh :=
      (obase.add odrift).add odut
    simpa only [herr] using hh

  have herrScaled_o :
      errScaled =o[atTop] N := by
    have hh :=
      herr_o.const_mul_left dutDen⁻¹
    refine
      (hh.congr_left ?_).congr_right ?_
    · intro T
      simp only [herrScaled, div_eq_mul_inv]
      ring
    · intro T
      rfl

  ------------------------------------------------------------------
  -- (3) epsilon form
  ------------------------------------------------------------------
  exact
    Assembly.eps_form_of_isLittleO
      hmain
      (Eventually.of_forall
        fun T => Nat.cast_nonneg _)
      herrScaled_o

end Zeta23.ZeroSide.RankTraceMult
