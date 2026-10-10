/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Brownian exponential-moment foundations

This module starts the Brownian foundation layer from the pinned finite-dimensional law API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Filter
open Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private lemma coe_nndist_real_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    (nndist (t : ℝ) (s : ℝ) : ℝ) = (t : ℝ) - (s : ℝ) := by
  rw [coe_nndist, Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hst))]

/-- The raw natural filtration of a pointwise measurable real process. -/
def brownianRawFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) :
    MeasureTheory.Filtration ℝ≥0 mΩ where
  seq t := ⨆ s : ℝ≥0, ⨆ (_ : s ≤ t), MeasurableSpace.comap (B s) inferInstance
  mono' := by
    intro s t hst
    refine iSup_le fun u => iSup_le fun hus => ?_
    exact le_iSup_of_le u (le_iSup_of_le (hus.trans hst) le_rfl)
  le' := by
    intro t
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact (hB s).comap_le

/-- Restrict a continuous-time filtration to integer times. -/
def brownianIntegerFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) : MeasureTheory.Filtration ℕ mΩ where
  seq n := 𝓕 n
  mono' := by
    intro n m hnm
    apply 𝓕.mono
    exact_mod_cast hnm
  le' := fun n => 𝓕.le n

/-- The past-process map generates precisely the raw natural sigma algebra. -/
theorem brownianHistorySigma_eq
    {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
    MeasurableSpace.comap (fun ω (u : Set.Iic s) => B u ω) inferInstance =
      ⨆ u : ℝ≥0, ⨆ (_ : u ≤ s), MeasurableSpace.comap (B u) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · refine iSup_le fun u => ?_
    exact le_iSup_of_le u.1 (le_iSup_of_le u.2 le_rfl)
  · refine iSup_le fun u => iSup_le fun hus => ?_
    exact le_iSup_of_le (⟨u, hus⟩ : Set.Iic s) le_rfl

/-- The Gaussian moment-generating function computes the exponential moment of a Brownian
increment. This is the deterministic-time input for the exponential martingale. -/
theorem brownian_exp_increment_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (θ : ℝ) :
    ∫ ω, Real.exp (θ * (B t ω - B s ω)) ∂P =
      Real.exp ((nndist (t : ℝ) (s : ℝ) : ℝ) * θ ^ 2 / 2) := by
  have hmgf := mgf_gaussianReal (hB.hasLaw_sub t s) θ
  simpa [ProbabilityTheory.mgf, mul_comm] using hmgf

/-- Each fixed-time exponential of a Brownian motion is integrable. -/
theorem brownian_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (θ c : ℝ) :
    Integrable (fun ω => Real.exp (θ * B t ω + c)) P := by
  have hlaw := hB.hasLaw_eval t
  have h := hlaw.integrable_comp (integrable_exp_mul_gaussianReal (μ := 0) (v := t) θ)
  have heq : (fun ω => Real.exp (θ * B t ω + c)) =
      fun ω => Real.exp c * Real.exp (θ * B t ω) := by
    funext ω
    rw [Real.exp_add]
    ring_nf
  rw [heq]
  exact h.const_mul (Real.exp c)

/-- Every time marginal of the Brownian exponential martingale has mean one. -/
theorem brownian_exponential_expectation_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (θ : ℝ) :
    ∫ ω, Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2) ∂P = 1 := by
  have hmoment : ∫ ω, Real.exp (θ * B t ω) ∂P =
      Real.exp ((t : ℝ) * θ ^ 2 / 2) := by
    have := mgf_gaussianReal (hB.hasLaw_eval t) θ
    simpa [ProbabilityTheory.mgf] using this
  have heq : (fun ω => Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2)) =
      fun ω => Real.exp (- (θ ^ 2 * (t : ℝ) / 2)) * Real.exp (θ * B t ω) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, hmoment, ← Real.exp_add]
  simp; ring

/-- The standard exponential Brownian process is a martingale for the raw natural filtration.
Pointwise measurability is stated explicitly because Mathlib's `IsBrownianReal` only records
almost-everywhere measurability of each evaluation. -/
theorem brownian_exponential_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) (θ : ℝ) :
    MeasureTheory.Martingale
      (fun t ω => Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2))
      (brownianRawFiltration B hmeas) P := by
  let 𝓕 := brownianRawFiltration B hmeas
  have hP : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · intro t
    have hBt : Measurable[𝓕 t] (B t) := by
      apply Measurable.of_comap_le
      change MeasurableSpace.comap (B t) inferInstance ≤
        ⨆ u : ℝ≥0, ⨆ (_ : u ≤ t), MeasurableSpace.comap (B u) inferInstance
      exact le_iSup_of_le t (le_iSup_of_le le_rfl le_rfl)
    have harg : Measurable[𝓕 t] (fun ω => θ * B t ω - θ ^ 2 * (t : ℝ) / 2) := by
      fun_prop
    exact harg.exp.stronglyMeasurable
  · intro s t hst
    let d : ℝ≥0 := t - s
    let Xf : Ω → ℝ≥0 → ℝ := fun ω u => B (s + u) ω - B s ω
    let Xh : Ω → Set.Iic s → ℝ := fun ω u => B u ω
    let mF : MeasurableSpace Ω := MeasurableSpace.comap Xf inferInstance
    let mH : MeasurableSpace Ω := MeasurableSpace.comap Xh inferInstance
    let : MeasurableSpace Ω := mΩ
    let G : (ℝ≥0 → ℝ) → ℝ := fun f => Real.exp (θ * f d - θ ^ 2 * (d : ℝ) / 2)
    let g : Ω → ℝ := G ∘ Xf
    let M : ℝ≥0 → Ω → ℝ := fun u ω =>
      Real.exp (θ * B u ω - θ ^ 2 * (u : ℝ) / 2)
    have hsd : s + d = t := by
      dsimp [d]
      exact add_tsub_cancel_of_le hst
    have hdist : (nndist (t : ℝ) (s : ℝ) : ℝ) = (d : ℝ) := by
      rw [coe_nndist_real_of_le hst]
      dsimp [d]
      exact (NNReal.coe_sub hst).symm
    have hpast : mH = 𝓕 s := by
      dsimp [mH, Xh, 𝓕, brownianRawFiltration]
      exact brownianHistorySigma_eq B s
    have hXfMeas : Measurable[mΩ] Xf := by
      exact measurable_pi_iff.mpr fun u => (hmeas (s + u)).sub (hmeas s)
    have hXhMeas : Measurable[mΩ] Xh := by
      exact measurable_pi_iff.mpr fun u => hmeas u
    have hshift := hB.toIsPreBrownianReal.indepFun_shift s
    change IndepFun Xf Xh P at hshift
    have hInd : Indep mF mH P := hshift
    have hGMeas : Measurable G := by
      dsimp [G]
      fun_prop
    have hgMeas : Measurable[mF] g := by
      exact hGMeas.comp (comap_measurable Xf)
    have hgStrong : StronglyMeasurable[mF] g := hgMeas.stronglyMeasurable
    have hfutureLe : mF ≤ mΩ := hXfMeas.comap_le
    have hpastLe : mH ≤ mΩ := hXhMeas.comap_le
    have hgCond : P[g | mH] =ᵐ[P] fun _ => P[g] :=
      condExp_indep_eq hfutureLe hpastLe hgStrong hInd
    have hgIntExp : Integrable (fun ω => Real.exp (θ * (B t ω - B s ω))) P := by
      exact (hB.toIsPreBrownianReal.hasLaw_sub t s).integrable_comp
        (integrable_exp_mul_gaussianReal (μ := 0)
          (v := nndist (t : ℝ) (s : ℝ)) θ)
    have hgInt : Integrable g P := by
      have heq : g = fun ω => Real.exp (-(θ ^ 2 * (d : ℝ) / 2)) *
          Real.exp (θ * (B t ω - B s ω)) := by
        funext ω
        dsimp [g, G, Xf]
        rw [hsd, ← Real.exp_add]
        congr 1
        ring
      rw [heq]
      exact hgIntExp.const_mul _
    have hgMean : P[g] = 1 := by
      have heq : g = fun ω => Real.exp (-(θ ^ 2 * (d : ℝ) / 2)) *
          Real.exp (θ * (B t ω - B s ω)) := by
        funext ω
        dsimp [g, G, Xf]
        rw [hsd, ← Real.exp_add]
        congr 1
        ring
      rw [heq, integral_const_mul, brownian_exp_increment_integral
        hB.toIsPreBrownianReal s t θ, hdist]
      rw [← Real.exp_add]
      simp; ring
    have hMsStrong : StronglyMeasurable[mH] (M s) := by
      rw [hpast]
      have hBs : Measurable[𝓕 s] (B s) := by
        apply Measurable.of_comap_le
        change MeasurableSpace.comap (B s) inferInstance ≤
          ⨆ u : ℝ≥0, ⨆ (_ : u ≤ s), MeasurableSpace.comap (B u) inferInstance
        exact le_iSup_of_le s (le_iSup_of_le le_rfl le_rfl)
      have harg : Measurable[𝓕 s]
          (fun ω => θ * B s ω - θ ^ 2 * (s : ℝ) / 2) := by
        fun_prop
      exact harg.exp.stronglyMeasurable
    have hMtInt : Integrable (M t) P := by
      simpa [M, sub_eq_add_neg] using
        brownian_exp_integrable hB.toIsPreBrownianReal t θ
          (-(θ ^ 2 * (t : ℝ) / 2))
    have hfactor : (fun ω => M s ω * g ω) = M t := by
      funext ω
      dsimp [M, g, G, Xf]
      rw [hsd, ← Real.exp_add]
      congr 1
      dsimp [d]
      rw [NNReal.coe_sub hst]
      ring
    have hprodInt : Integrable (fun ω => M s ω * g ω) P := by
      rw [hfactor]
      exact hMtInt
    have hpull := condExp_mul_of_stronglyMeasurable_left hMsStrong hprodInt hgInt
    have hcondProd : P[fun ω => M s ω * g ω | mH] =ᵐ[P] M s := by
      filter_upwards [hpull, hgCond] with ω hpullω hcondω
      change P[M s * g | mH] ω = M s ω
      rw [hpullω]
      change M s ω * P[g | mH] ω = M s ω
      rw [hcondω, hgMean]
      ring
    have hcond : P[M t | mH] =ᵐ[P] M s := by
      calc
        P[M t | mH] =ᵐ[P] P[fun ω => M s ω * g ω | mH] :=
          condExp_congr_ae (ae_of_all P fun ω => congrFun hfactor.symm ω)
        _ =ᵐ[P] M s := hcondProd
    simpa only [M, hpast] using hcond

/-- Optional stopping for any bounded countable-range stopping time of the raw filtration. This
uses Mathlib's optional-sampling theorem directly and is the approximation input for general
bounded times. -/
theorem brownian_exponential_countable_range_optional_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) (θ : ℝ) (T : ℝ≥0)
    (τ : Ω → WithTop ℝ≥0) (hτ : MeasureTheory.IsStoppingTime
      (brownianRawFiltration B hmeas) τ)
    (hτT : ∀ ω, τ ω ≤ T) (hτrange : (Set.range τ).Countable) :
    ∫ ω, MeasureTheory.stoppedValue
        (fun t ω => Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2)) τ ω ∂P = 1 := by
  have hP : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2)
  have hM := brownian_exponential_martingale hB hmeas θ
  have hstop := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hτrange
  calc
    ∫ ω, MeasureTheory.stoppedValue M τ ω ∂P =
        ∫ ω, P[M T | hτ.measurableSpace] ω ∂P := integral_congr_ae hstop
    _ = ∫ ω, M T ω ∂P :=
      integral_condExp (hτ.measurableSpace_le_of_le hτT)
    _ = 1 := brownian_exponential_expectation_one hB.toIsPreBrownianReal T θ

/-- Continuous-time optional stopping follows from a bounded approximation by countable-range
stopping times. This is the Vitali-convergence step: all approximating stopped values are
conditional expectations of one fixed terminal value, hence uniformly integrable. -/
theorem brownian_exponential_bounded_optional_stopping_of_approx
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) (θ : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0)
    (hτnStop : ∀ n, MeasureTheory.IsStoppingTime
      (brownianRawFiltration B hmeas) (fun ω => (τn n ω : WithTop ℝ≥0)))
    (hτnT : ∀ n ω, τn n ω ≤ T)
    (hτnRange : ∀ n, (Set.range (fun ω => (τn n ω : WithTop ℝ≥0))).Countable)
    (hτnTendsto : ∀ᵐ ω ∂P, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) :
    ∫ ω, Real.exp (θ * B (τ ω) ω - θ ^ 2 * ((τ ω : ℝ)) / 2) ∂P = 1 := by
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2)
  let F : ℕ → Ω → ℝ := fun n ω => M (τn n ω) ω
  let Fτ : Ω → ℝ := fun ω => M (τ ω) ω
  let 𝓕 := brownianRawFiltration B hmeas
  have hP : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hM := brownian_exponential_martingale hB hmeas θ
  have hMTInt : Integrable (M T) P := by
    simpa [M, sub_eq_add_neg] using
      brownian_exp_integrable hB.toIsPreBrownianReal T θ
        (-(θ ^ 2 * (T : ℝ) / 2))
  let G : ℕ → Ω → ℝ := fun n ω => P[M T | (hτnStop n).measurableSpace] ω
  have hτnEval (n : ℕ) (ω : Ω) :
      ((τn n ω : WithTop ℝ≥0).untopA) = τn n ω := by
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
    apply WithTop.coe_inj.mp
    exact WithTop.coe_untop _ WithTop.coe_ne_top
  have hStopped (n : ℕ) (ω : Ω) :
      MeasureTheory.stoppedValue M (fun ω => (τn n ω : WithTop ℝ≥0)) ω = F n ω := by
    change M ((τn n ω : WithTop ℝ≥0).untopA) ω = M (τn n ω) ω
    rw [hτnEval]
  have hStopCE (n : ℕ) :
      (fun ω => MeasureTheory.stoppedValue M
        (fun ω => (τn n ω : WithTop ℝ≥0)) ω) =ᵐ[P] G n := by
    exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hτnStop n) (fun ω => by exact_mod_cast hτnT n ω) (hτnRange n)
  have hUI_G : UniformIntegrable G 1 P :=
    hMTInt.uniformIntegrable_condExp fun n =>
      (hτnStop n).measurableSpace_le_of_le
        (fun ω => by exact_mod_cast hτnT n ω)
  have hFG : ∀ n, G n =ᵐ[P] F n := by
    intro n
    filter_upwards [hStopCE n] with ω hω
    exact hω.symm.trans (hStopped n ω)
  have hUI : UniformIntegrable F 1 P := hUI_G.ae_eq hFG
  have hMcont : ∀ᵐ ω ∂P, Continuous (fun t => M t ω) := by
    filter_upwards [hB.cont] with ω hω
    have harg : Continuous (fun t => θ * B t ω - θ ^ 2 * (t : ℝ) / 2) := by
      fun_prop
    exact Real.continuous_exp.comp harg
  have hF_tendsto : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (Fτ ω)) := by
    filter_upwards [hMcont, hτnTendsto] with ω hω hτω
    exact hω.continuousAt.tendsto.comp hτω
  have hFInt : ∀ n, Integrable (F n) P := by
    intro n
    exact (integrable_condExp.congr (hFG n))
  have hFτInt : Integrable Fτ P := hUI.integrable_of_ae_tendsto hF_tendsto
  have hInMeasure : TendstoInMeasure P F atTop Fτ :=
    tendstoInMeasure_of_tendsto_ae (fun n => hUI.aestronglyMeasurable n) hF_tendsto
  have hLp : Tendsto (fun n => eLpNorm (F n - Fτ) 1 P) atTop (𝓝 0) := by
    apply (tendstoInMeasure_iff_tendsto_Lp_finite
      (p := (1 : ℝ≥0∞)) (by norm_num) (by simp)
      (fun n => memLp_one_iff_integrable.mpr (hFInt n))
      (memLp_one_iff_integrable.mpr hFτInt)).mp
    exact ⟨hInMeasure, hUI.1⟩
  have hIntegralTendsto :
      Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, Fτ ω ∂P)) :=
    tendsto_integral_of_L1' Fτ (Filter.Eventually.of_forall hFInt) hLp
  have hStopOne (n : ℕ) : ∫ ω, F n ω ∂P = 1 := by
    calc
      ∫ ω, F n ω ∂P = ∫ ω, MeasureTheory.stoppedValue M
          (fun ω => (τn n ω : WithTop ℝ≥0)) ω ∂P := by
        apply integral_congr_ae
        exact ae_of_all P fun ω => (hStopped n ω).symm
      _ = 1 := brownian_exponential_countable_range_optional_stopping hB hmeas θ T
        (fun ω => (τn n ω : WithTop ℝ≥0)) (hτnStop n)
        (fun ω => by exact_mod_cast hτnT n ω) (hτnRange n)
  have hIntegralOne :
      Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (1 : ℝ)) := by
    have hEq : (fun n => ∫ ω, F n ω ∂P) = fun _ => (1 : ℝ) :=
      funext hStopOne
    rw [hEq]
    exact tendsto_const_nhds
  have hFτMean : ∫ ω, Fτ ω ∂P = 1 := tendsto_nhds_unique hIntegralTendsto hIntegralOne
  simpa [Fτ, M] using hFτMean

/-- The dyadic mesh used to approximate bounded stopping times from above. -/
def brownianDyadicMesh (n : ℕ) : ℝ≥0 := (2 : ℝ≥0) ^ n

/-- Round a nonnegative time upward to the next dyadic mesh point. -/
noncomputable def brownianDyadicCeiling {Ω : Type*} (τ : Ω → ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (Nat.ceil (τ ω * brownianDyadicMesh n) : ℝ≥0) / brownianDyadicMesh n

private lemma brownian_dyadic_ceiling_le_iff {x t q : ℝ≥0} (hq : 0 < q) :
    (Nat.ceil (x * q) : ℝ≥0) / q ≤ t ↔
      x ≤ (Nat.floor (t * q) : ℝ≥0) / q := by
  constructor
  · intro h
    have h₁ : (Nat.ceil (x * q) : ℝ≥0) ≤ t * q := (div_le_iff₀ hq).1 h
    have h₂ : Nat.ceil (x * q) ≤ Nat.floor (t * q) :=
      (Nat.le_floor_iff zero_le).2 (by exact_mod_cast h₁)
    have h₃ : x * q ≤ (Nat.floor (t * q) : ℝ≥0) := by
      exact_mod_cast (Nat.ceil_le.mp h₂)
    exact (le_div_iff₀ hq).2 h₃
  · intro h
    have h₁ : x * q ≤ (Nat.floor (t * q) : ℝ≥0) := (le_div_iff₀ hq).1 h
    have h₂ : Nat.ceil (x * q) ≤ Nat.floor (t * q) :=
      (Nat.ceil_le).2 (by exact_mod_cast h₁)
    apply (div_le_iff₀ hq).2
    exact_mod_cast (Nat.le_floor_iff zero_le).1 h₂

private lemma brownian_dyadic_ceiling_lower (x q : ℝ≥0) (hq : 0 < q) :
    x ≤ (Nat.ceil (x * q) : ℝ≥0) / q := by
  apply (le_div_iff₀ hq).2
  exact_mod_cast (Nat.le_ceil (x * q))

private lemma brownian_dyadic_ceiling_upper (x q : ℝ≥0) (hq : 0 < q) :
    (Nat.ceil (x * q) : ℝ≥0) / q ≤ x + q⁻¹ := by
  apply (div_le_iff₀ hq).2
  have hceil : (Nat.ceil (x * q) : ℝ≥0) ≤ x * q + 1 := by
    calc
      (Nat.ceil (x * q) : ℝ≥0) ≤ (Nat.floor (x * q) : ℝ≥0) + 1 := by
        exact_mod_cast Nat.ceil_le_floor_add_one (x * q)
      _ ≤ x * q + 1 := add_le_add (Nat.floor_le zero_le) le_rfl
  have hmul : (x + q⁻¹) * q = x * q + 1 := by
    rw [add_mul, inv_mul_cancel₀ hq.ne']
  rw [hmul]
  exact hceil

private lemma brownian_dyadic_mesh_pos (n : ℕ) : 0 < brownianDyadicMesh n :=
  pow_pos (by norm_num : (0 : ℝ≥0) < 2) n

private lemma brownian_dyadic_mesh_ge_one (n : ℕ) : 1 ≤ brownianDyadicMesh n := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2)

private lemma brownian_dyadic_mesh_inv_tendsto_zero :
    Tendsto (fun n : ℕ => (brownianDyadicMesh n)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (1 / 2 : ℝ≥0)) (by norm_num) (by norm_num)
  have hEq : (fun n : ℕ => (brownianDyadicMesh n)⁻¹) = fun n => (1 / 2 : ℝ≥0) ^ n := by
    funext n
    simp [brownianDyadicMesh, div_eq_mul_inv, inv_pow]
  rw [hEq]
  exact h

/-- A bounded stopping time rounded upward to a dyadic mesh is again a stopping time. Its
sublevel event at `t` is the original stopping event at the largest mesh point not exceeding `t`.
-/
theorem brownian_dyadicCeiling_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n : ℕ) :
    MeasureTheory.IsStoppingTime 𝓕
      (fun ω => (brownianDyadicCeiling τ n ω : WithTop ℝ≥0)) := by
  intro t
  let q := brownianDyadicMesh n
  let g := (Nat.floor (t * q) : ℝ≥0) / q
  have hq : 0 < q := brownian_dyadic_mesh_pos n
  have hg : g ≤ t := by
    apply (div_le_iff₀ hq).2
    exact_mod_cast Nat.floor_le (zero_le)
  have hset :
      {ω | (brownianDyadicCeiling τ n ω : WithTop ℝ≥0) ≤ t} =
        {ω | τ ω ≤ g} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
    exact brownian_dyadic_ceiling_le_iff hq
  rw [hset]
  apply 𝓕.mono hg
  simpa only [WithTop.coe_le_coe] using hτ.measurableSet_le g

/-- The dyadic ceilings of a bounded stopping time have countable range, stay below `T+1`, and
converge pointwise to the stopping time. -/
theorem brownian_dyadicCeiling_properties
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (∀ n, MeasureTheory.IsStoppingTime 𝓕
      (fun ω => (brownianDyadicCeiling τ n ω : WithTop ℝ≥0))) ∧
    (∀ n ω, brownianDyadicCeiling τ n ω ≤ T + 1) ∧
    (∀ ω, Tendsto (fun n => brownianDyadicCeiling τ n ω) atTop (𝓝 (τ ω))) ∧
    (∀ n, (Set.range (fun ω =>
      (brownianDyadicCeiling τ n ω : WithTop ℝ≥0))).Countable) := by
  refine ⟨fun n => brownian_dyadicCeiling_isStoppingTime 𝓕 τ hτ n, ?_, ?_, ?_⟩
  · intro n ω
    let q := brownianDyadicMesh n
    have hq : 0 < q := brownian_dyadic_mesh_pos n
    have hq1 : 1 ≤ q := brownian_dyadic_mesh_ge_one n
    have hInv : q⁻¹ ≤ 1 := by
      have hdiv : 1 / q ≤ 1 := (div_le_iff₀ hq).2 (by simpa using hq1)
      simpa [div_eq_mul_inv] using hdiv
    calc
      brownianDyadicCeiling τ n ω ≤ τ ω + q⁻¹ := by
        exact brownian_dyadic_ceiling_upper (τ ω) q hq
      _ ≤ T + q⁻¹ := add_le_add (hτT ω) le_rfl
      _ ≤ T + 1 := add_le_add le_rfl hInv
  · intro ω
    have hδ := brownian_dyadic_mesh_inv_tendsto_zero
    have hupper : Tendsto (fun n => τ ω + (brownianDyadicMesh n)⁻¹)
        atTop (𝓝 (τ ω)) := by
      simpa using tendsto_const_nhds.add hδ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper
    · intro n
      exact brownian_dyadic_ceiling_lower (τ ω) (brownianDyadicMesh n)
        (brownian_dyadic_mesh_pos n)
    · intro n
      exact brownian_dyadic_ceiling_upper (τ ω) (brownianDyadicMesh n)
        (brownian_dyadic_mesh_pos n)
  · intro n
    let q := brownianDyadicMesh n
    apply Set.Countable.mono ?_ (Set.countable_range fun k : ℕ =>
      (((k : ℝ≥0) / q : ℝ≥0) : WithTop ℝ≥0))
    rintro x ⟨ω, rfl⟩
    refine ⟨Nat.ceil (τ ω * q), ?_⟩
    rfl

/-- Optional stopping for the Brownian exponential martingale at every bounded stopping time of the
raw natural filtration. The proof uses upward dyadic approximation and uniform integrability of
conditional expectations of one fixed terminal value. -/
theorem brownian_exponential_bounded_optional_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) (θ : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0) (hτ : MeasureTheory.IsStoppingTime
      (brownianRawFiltration B hmeas) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T) :
    ∫ ω, Real.exp (θ * B (τ ω) ω - θ ^ 2 * ((τ ω : ℝ)) / 2) ∂P = 1 := by
  obtain ⟨hτnStop, hτnT, hτnTendsto, hτnRange⟩ :=
    brownian_dyadicCeiling_properties (brownianRawFiltration B hmeas) τ hτ T hτT
  exact brownian_exponential_bounded_optional_stopping_of_approx
    hB hmeas θ (T + 1) τ
    (fun n ω => brownianDyadicCeiling τ n ω)
    hτnStop hτnT hτnRange (Filter.Eventually.of_forall hτnTendsto)


end DOZZ.Proofs

end
