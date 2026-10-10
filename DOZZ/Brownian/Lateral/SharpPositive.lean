/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.ReferenceIntensity
public import DOZZ.Brownian.Lateral.PositiveUniform
public import DOZZ.Brownian.Lateral.RadialWindowUniform

/-!
# Positive lateral moments from the proved sharp reference induction

Stationarity moves a given lateral interval into a small logarithmic reference chart.
The source annulus is contained in a small reference ball, whose entire positive
subcritical moment range is now proved. Radial independence then transfers that bound
to the given lateral measure. No moment assumption is added to its source predicate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Moving the left logarithmic endpoint to log eight puts the entire source annulus in the
reference disk of radius one eighth, whatever the interval length. -/
theorem lateral_shifted_annulus_subset_reference_ball (a b : ℝ) :
    lateralLogAnnulus (a + (Real.log 8 - a)) (b + (Real.log 8 - a)) ⊆
      Metric.ball (0 : ℂ) (1 / 8) := by
  have he : Real.exp (-(a + (Real.log 8 - a))) = 1 / 8 := by
    rw [show a + (Real.log 8 - a) = Real.log 8 by ring, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    exact (one_div 8).symm
  simpa only [he] using lateralLogAnnulus_subset_ball
    (a + (Real.log 8 - a)) (b + (Real.log 8 - a))

/-- Every nonnegative subcritical moment of the moved source annulus is finite. This is an
actual consequence of the proved reference induction, not a source-moment premise. -/
theorem sourceLateral_shifted_annulus_nonnegative_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hS : IsSourceLateralProjection P X γ M Z) (hγ : 0 < γ)
    (a b q : ℝ) (hq : 0 ≤ q) (hcrit : q < 4 / γ ^ 2) :
    (∫⁻ ω, (M ω (lateralLogAnnulus
      (a + (Real.log 8 - a)) (b + (Real.log 8 - a)))) ^ q ∂P) < ⊤ := by
  have hfin := gmc_reference_nonnegative_moment_finite P X hS.1 γ q hγ hq hcrit
    M hS.2.1 (by norm_num : (0 : ℝ) < 1 / 8) le_rfl
  apply lt_of_le_of_lt _ hfin
  exact lintegral_mono (fun ω => ENNReal.rpow_le_rpow
    (measure_mono (lateral_shifted_annulus_subset_reference_ball a b)) hq)

/-- The full pointwise positive subcritical range holds for every given lateral chaos.
Translation and radial independence remove all source-ball and annular moment premises. -/
theorem lateralGMC_interval_nonnegative_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hq : 0 ≤ q) (hcrit : q < 4 / γ ^ 2) :
    (∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P) < ⊤ := by
  rw [← lateralGMC_interval_moment_translation_eq P γ Z hZ a b q (Real.log 8 - a)]
  obtain ⟨X, M, hS⟩ := hZ.2.2.2.2.2.2.2.2
  exact sourceLateral_interval_moment_finite_of_annular P X γ M Z hS hZ.2.2.2.1
    (a + (Real.log 8 - a)) (b + (Real.log 8 - a)) q
    (sourceLateral_shifted_annulus_nonnegative_moment_finite P X γ M Z hS hZ.1 a b q hq hcrit)

/-- Positive interval mean gives strict positivity of every positive interval moment.
This argument does not assert almost-sure positivity of the given chaos. -/
theorem lateralGMC_interval_positive_moment_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hab : a < b) (hq : 0 < q) :
    0 < ∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P := by
  have hpow := lateralGMC_interval_rpow_aemeasurable P γ Z hZ a b q
  apply pos_iff_ne_zero.mpr
  intro hz
  have he := (lintegral_eq_zero_iff' hpow).mp hz
  have hzero : (fun ω => Z ω (Ioc a b)) =ᵐ[P] 0 := by
    filter_upwards [he] with ω hω
    exact (ENNReal.rpow_eq_zero_iff_of_pos hq).mp hω
  have hmean : (∫⁻ ω, Z ω (Ioc a b) ∂P) = 0 := by
    simpa only [Pi.zero_apply, lintegral_zero] using lintegral_congr_ae hzero
  rw [lateralGMC_interval_first_moment P γ Z hZ a b hab] at hmean
  exact (ENNReal.ofReal_pos.mpr
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr hab))).ne' hmean


/-- At a fixed charge, one enclosing moment gives a common bound for every nonnegative
order in a compact set and every translated interval. -/
theorem lateralGMC_interval_nonnegative_moments_uniform_orders
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (Kq : Set ℝ) (hKq : IsCompact Kq) (a b : ℝ)
    (hq0 : ∀ q ∈ Kq, 0 ≤ q) (hcrit : ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ q ∈ Kq, ∀ t : ℝ,
      (∫⁻ ω, (Z ω (Ioc (a + t) (b + t))) ^ q ∂P) ≤ C := by
  let _ := hZ.2.2.1
  by_cases hne : Kq.Nonempty
  · obtain ⟨u, hu, hmax⟩ := hKq.exists_isMaxOn hne continuous_id.continuousOn
    let C : ℝ≥0∞ := 1 + ∫⁻ ω, (Z ω (Ioc a b)) ^ u ∂P
    have hC : C < ⊤ := ENNReal.add_lt_top.mpr ⟨by simp,
      lateralGMC_interval_nonnegative_moment_finite P γ Z hZ a b u (hq0 u hu) (hcrit u hu)⟩
    refine ⟨C, hC, ?_⟩
    intro q hq t
    rw [lateralGMC_interval_moment_translation_eq P γ Z hZ a b q t]
    have hm : AEMeasurable (fun ω => Z ω (Ioc a b)) P :=
      (Measure.measurable_coe measurableSet_Ioc).comp_aemeasurable hZ.2.2.2.1
    have h := lintegral_rpow_le_endpoint_sum P _ hm (hq0 q hq) (hmax hq)
    simpa only [C, id_eq, ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one] using h
  · exact ⟨0, by simp, fun q hq => False.elim (hne ⟨q, hq⟩)⟩


/-- The sharp positive unit-interval range now closes the upper-conditioned positive
half-cylinder estimates with no supplied GMC moment premise. -/
theorem upperConditioned_positiveLateralMass_subcritical_nonnegative_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ)
    (hν : 0 < ν) (hq : 0 ≤ q) (hcrit : q < 4 / γ ^ 2)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  exact upperConditioned_positiveLateralMass_moment_finite_of_unit_moment P P₀ hP₀
    ν γ q hν hq B Z hB hZ hi hLaw
    (lateralGMC_interval_nonnegative_moment_finite P γ Z hZ 0 1 q hq hcrit)



/-- At a fixed charge, both drift and moment order may vary over compact strict-subcritical
ranges. The sole unit-chaos input of the block theorem is now discharged by the sharp range. -/
theorem upperConditioned_positiveLateralMass_subcritical_uniform_orders_drift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (Kν Kq : Set ℝ) (hKν : IsCompact Kν) (hKq : IsCompact Kq)
    (B : ℝ → Ω → BrownianPath) (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (hi : ∀ ν ∈ Kν, IndepFun (B ν) Z P)
    (hLaw : ∀ ν ∈ Kν, P.map (B ν) = brownianBelowConditionedLaw P₀ ν 1)
    (hν : ∀ ν ∈ Kν, 0 < ν) (hq0 : ∀ q ∈ Kq, 0 ≤ q)
    (hcrit : ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z ω)) ^ q ∂P) ≤ C := by
  have hZ' : ∀ g ∈ ({γ} : Set ℝ), IsLateralGMCOf P g ((fun _ : ℝ => Z) g) := by
    intro g hg
    simpa only [mem_singleton_iff.mp hg] using hZ
  have hUnit : ∀ u : ℝ, 1 < u → (∀ g ∈ ({γ} : Set ℝ), u < 4 / g ^ 2) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ g ∈ ({γ} : Set ℝ),
        (∫⁻ ω, (Z ω (Ioc 0 1)) ^ u ∂P) ≤ C := by
    intro u hu hc
    refine ⟨∫⁻ ω, (Z ω (Ioc 0 1)) ^ u ∂P,
      lateralGMC_interval_nonnegative_moment_finite P γ Z hZ 0 1 u
        (by linarith) (hc γ (mem_singleton γ)), fun _ _ => le_rfl⟩
  obtain ⟨C, hC, hb⟩ := upperConditioned_positiveLateralMass_compact_orders
    P P₀ hP₀ {γ} Kν Kq isCompact_singleton hKν hKq (singleton_nonempty γ)
    (fun _ => Z) B hZ' hB (fun _ _ ν hν => hi ν hν) hLaw hν
    (fun g hg q hq => by simpa only [mem_singleton_iff.mp hg] using hcrit q hq) hq0 hUnit
  exact ⟨C, hC, fun ν hν q hq => hb γ (mem_singleton γ) ν hν q hq⟩


/-- Positive subcritical moments imply finite total upper-conditioned half-cylinder mass
almost surely, for every given lateral chaos. -/
theorem upperConditioned_positiveLateralMass_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ : ℝ) (hν : 0 < ν)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1) :
    ∀ᵐ ω ∂P, positiveLateralMass γ (B ω) (Z ω) < ⊤ := by
  obtain ⟨q, hq, hc⟩ := gmc_subcritical_higher_order_exists hZ.1 hZ.2.1
  have hf := upperConditioned_positiveLateralMass_subcritical_nonnegative_moment_finite
    P P₀ hP₀ ν γ q hν (by linarith) hc B Z hB hZ hi hLaw
  exact positiveLateralMass_finite_ae_of_uniform_positive_moment P γ q (by linarith)
    B Z hB hZ _ hf le_rfl


/-- Fixed endpoints carry no lateral mass, so the sharp positive range holds for the closed
interval convention as well. -/
theorem lateralGMC_closed_interval_nonnegative_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hab : a ≤ b) (hq : 0 ≤ q) (hcrit : q < 4 / γ ^ 2) :
    (∫⁻ ω, (Z ω (Icc a b)) ^ q ∂P) < ⊤ := by
  have he : (∫⁻ ω, (Z ω (Icc a b)) ^ q ∂P) =
      ∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P := by
    apply lintegral_congr_ae
    filter_upwards [lateralGMC_Icc_eq_Ioc_ae P γ Z hZ a b hab] with ω hω
    rw [hω]
  rw [he]
  exact lateralGMC_interval_nonnegative_moment_finite P γ Z hZ a b q hq hcrit






/-- The actual finite sharp moment provides a quantitative large-mass bound, uniformly in
all deterministic translations of the interval. -/
theorem lateralGMC_interval_large_mass_le_sharp_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hq : 0 < q) (t : ℝ) (v : ℝ≥0∞) :
    v ^ q * P {ω | v ≤ Z ω (Ioc (a + t) (b + t))} ≤
      ∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P := by
  have hm := lateralGMC_interval_rpow_aemeasurable P γ Z hZ (a + t) (b + t) q
  have hs : {ω | v ≤ Z ω (Ioc (a + t) (b + t))} ⊆
      {ω | v ^ q ≤ (Z ω (Ioc (a + t) (b + t))) ^ q} := by
    intro ω hω
    exact ENNReal.rpow_le_rpow hω hq.le
  have h := (mul_le_mul' (le_refl (v ^ q)) (measure_mono hs)).trans
    (mul_meas_ge_le_lintegral₀ hm (v ^ q))
  rw [lateralGMC_interval_moment_translation_eq P γ Z hZ a b q t] at h
  exact h






end DOZZ.Proofs
