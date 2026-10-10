/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.CoulombBounds
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! Moment control for the critical origin mass, including uniform inverse moments. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The constant-weight singular mass is the weighted GMC ball mass. -/
theorem lastone_origin_weighted {Ω : Type*} (M : Ω → Measure ℂ) (γ a : ℝ) (ω : Ω) :
    localSingularMass M (fun _ => 1) 0 γ a ω = weightedGmcBallMass γ (M ω) a 0 1 := by
  simp only [localSingularMass, ENNReal.ofReal_one, one_mul, weightedGmcBallMass,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet, Set.indicator]

/-- A nonnegative insertion increases the unit ball mass. -/
theorem lastone_origin_ball_le {Ω : Type*} (M : Ω → Measure ℂ) (γ a : ℝ)
    (hγ : 0 ≤ γ) (ha : 0 ≤ a) (ω : Ω) :
    M ω (Metric.ball 0 1) ≤ localSingularMass M (fun _ => 1) 0 γ a ω := by
  rw [lastone_origin_weighted]
  have h := weightedGmcBallMass_mono_charge (M ω) hγ (0 : ℂ) (ρ := 1) le_rfl ha
  simpa only [weightedGmcBallMass, mul_zero, ENNReal.rpow_eq_pow, ENNReal.rpow_zero, lintegral_one, Measure.restrict_apply_univ] using h

/-- Every inverse moment of the critical mass is bounded by a fixed ball inverse moment. -/
theorem lastone_origin_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ a : ℝ, 0 ≤ a →
      ∫⁻ ω, localSingularMass M (fun _ => 1) 0 γ a ω ^ (-v) ∂P ≤ C := by
  let C := gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-v)
  have hC : C < ⊤ := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM
    0 (1 / 8) (by norm_num) le_rfl (-v) (by
      have hbulk : 0 < 4 / γ ^ 2 := by positivity
      linarith)
  refine ⟨C, hC, fun a ha => lintegral_mono fun ω => ?_⟩
  have hball : M ω (Metric.ball 0 (1 / 8)) ≤ M ω (Metric.ball 0 1) :=
    measure_mono (Metric.ball_subset_ball (by norm_num))
  simp only [ENNReal.rpow_eq_pow]
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
    (hball.trans (lastone_origin_ball_le M γ a hγ.le ha ω)) hv.le)

/-- The moment at the varying critical order is finite for all sufficiently small positive drifts. -/
theorem lastone_origin_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∀ᶠ ν : ℝ in 𝓝[>] 0,
      ∫⁻ ω, localSingularMass M (fun _ => 1) 0 γ (Q γ - ν) ω ^ (ν / γ) ∂P < ⊤ := by
  have hbulk : 0 < 4 / γ ^ 2 := by positivity
  have he : Tendsto (fun ν : ℝ => ν / γ) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun ν : ℝ => ν) (𝓝 0) (𝓝 0)).div_const γ).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he.eventually (eventually_lt_nhds hbulk)] with ν hν hb
  have hν0 : 0 < ν := hν
  have hfin := weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM
    (Q γ - ν) 0 1 (by norm_num) (ν / γ) (div_pos hν0 hγ) (lt_min hb (by
      rw [sub_sub_cancel]
      have : 0 < ν / γ := div_pos hν0 hγ
      nlinarith [show 2 / γ * ν = 2 * (ν / γ) by ring]))
  simpa only [weightedGmcBallMoment, lastone_origin_weighted, ENNReal.rpow_eq_pow] using hfin

/-- Multiplying by a fixed positive finite mass factor leaves a small-power limit unchanged. -/
theorem lastone_scale_smallPower_limit
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : ι → Ω → ℝ≥0∞)
    (hA : ∀ i, AEMeasurable (A i) P) (l : Filter ι) (e : ι → ℝ) (he : Tendsto e l (𝓝 0))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (L : ℝ)
    (hlim : Tendsto (fun i => (∫⁻ ω, A i ω ^ e i ∂P).toReal) l (𝓝 L)) :
    Tendsto (fun i => (∫⁻ ω, (c * A i ω) ^ e i ∂P).toReal) l (𝓝 L) := by
  have hc : Tendsto (fun i => (c ^ e i).toReal) l (𝓝 1) := by
    simp_rw [← ENNReal.toReal_rpow]
    have hpos := ENNReal.toReal_pos hc0 hcT
    simp_rw [Real.rpow_def_of_pos hpos]
    simpa [Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (he.const_mul (Real.log c.toReal))
  have h := hc.mul hlim
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [] with i
  have hmul : (∫⁻ ω, (c * A i ω) ^ e i ∂P) =
      c ^ e i * ∫⁻ ω, A i ω ^ e i ∂P := by
    calc
      _ = ∫⁻ ω, c ^ e i * A i ω ^ e i ∂P := lintegral_congr fun ω => by
        simp only [ENNReal.mul_rpow_eq_ite, hc0, hcT, false_and, false_or, ite_false]
      _ = _ := lintegral_const_mul'' _ ((hA i).pow_const (e i))
  rw [hmul, ENNReal.toReal_mul]

end DOZZ.Proofs
