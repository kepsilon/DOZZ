/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedTransfer

/-! # Weighted local moments at the chart center are controlled at every center

Truncating the singular weight at height `N` gives bounded weights, for which the location
transfer of small-disk moments holds with a constant independent of `N`. Monotone convergence in
`N` then bounds the weighted local moment at the chart center `0` by a constant times the weighted
local moment at any other center, for positive subcritical orders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The singular weight `‖y‖^{-γα}` truncated at height `N`, as an extended real. -/
noncomputable def insertionTruncWeightE (γ α : ℝ) (N : ℕ) (y : ℂ) : ℝ≥0∞ :=
  min (N : ℝ≥0∞) (ENNReal.rpow (ENNReal.ofReal ‖y‖) (-γ * α))

/-- The singular weight `‖y‖^{-γα}` truncated at height `N`. -/
noncomputable def insertionTruncWeight (γ α : ℝ) (N : ℕ) (y : ℂ) : ℝ≥0 :=
  (insertionTruncWeightE γ α N y).toNNReal

theorem insertionTruncWeightE_le (γ α : ℝ) (N : ℕ) (y : ℂ) :
    insertionTruncWeightE γ α N y ≤ N :=
  min_le_left _ _

theorem coe_insertionTruncWeight (γ α : ℝ) (N : ℕ) (y : ℂ) :
    (insertionTruncWeight γ α N y : ℝ≥0∞) = insertionTruncWeightE γ α N y :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top N)
    (insertionTruncWeightE_le γ α N y))

theorem insertionTruncWeight_le (γ α : ℝ) (N : ℕ) (y : ℂ) :
    insertionTruncWeight γ α N y ≤ (N : ℝ≥0) := by
  rw [← ENNReal.coe_le_coe, coe_insertionTruncWeight, ENNReal.coe_natCast]
  exact insertionTruncWeightE_le γ α N y

theorem measurable_insertionTruncWeightE (γ α : ℝ) (N : ℕ) :
    Measurable (insertionTruncWeightE γ α N) :=
  measurable_const.min ((ENNReal.continuous_rpow_const (y := -γ * α)).measurable.comp
    (ENNReal.measurable_ofReal.comp measurable_norm))

theorem measurable_insertionTruncWeight (γ α : ℝ) (N : ℕ) :
    Measurable (insertionTruncWeight γ α N) :=
  ENNReal.measurable_toNNReal.comp (measurable_insertionTruncWeightE γ α N)

theorem insertionTruncWeightE_le_weight (γ α : ℝ) (N : ℕ) (y : ℂ) :
    insertionTruncWeightE γ α N y ≤ ENNReal.rpow (ENNReal.ofReal ‖y‖) (-γ * α) :=
  min_le_right _ _

theorem insertionTruncWeightE_mono (γ α : ℝ) (y : ℂ) :
    Monotone fun N : ℕ => insertionTruncWeightE γ α N y := fun _ _ h =>
  min_le_min_right _ (Nat.cast_le.mpr h)

theorem insertionTruncWeightE_tendsto (γ α : ℝ) (y : ℂ) :
    Tendsto (fun N : ℕ => insertionTruncWeightE γ α N y) atTop
      (𝓝 (ENNReal.rpow (ENNReal.ofReal ‖y‖) (-γ * α))) := by
  have h := ENNReal.tendsto_nat_nhds_top.min
    (tendsto_const_nhds (x := ENNReal.rpow (ENNReal.ofReal ‖y‖) (-γ * α)))
  rwa [min_eq_right le_top] at h

/-- Truncated weighted masses increase to the weighted local mass. -/
theorem insertionTrunc_mass_tendsto (γ α : ℝ) (μ : Measure ℂ) (z : ℂ) (ρ : ℝ) :
    Tendsto (fun N : ℕ => ∫⁻ x in Metric.ball z ρ, (insertionTruncWeight γ α N (x - z) : ℝ≥0∞)
        ∂μ) atTop (𝓝 (weightedGmcBallMass γ μ α z ρ)) := by
  simp only [coe_insertionTruncWeight]
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun N => ((measurable_insertionTruncWeightE γ α N).comp
      (measurable_id.sub_const z)).aemeasurable)
    (Eventually.of_forall fun x => insertionTruncWeightE_mono γ α (x - z))
    (Eventually.of_forall fun x => insertionTruncWeightE_tendsto γ α (x - z))

/-- The weighted local moment at the chart center is bounded by an explicit constant times the
weighted local moment at any other center, for small disks and positive subcritical orders. -/
theorem weightedGmcBallMoment_center_le_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : ℝ) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (p : ℝ) (hp : 0 < p)
    (hp4 : p < 4 / γ ^ 2) :
    weightedGmcBallMoment P M γ α 0 ρ p ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + (‖z‖ + ρ)))) / 2 *
          |p ^ 2 - p|)) * ENNReal.ofReal ((1 + (‖z‖ + ρ)) ^ 4) ^ |p| *
        weightedGmcBallMoment P M γ α z ρ p := by
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 +
      2 * Real.log (1 + (‖z‖ + ρ)))) / 2 * |p ^ 2 - p|)) *
      ENNReal.ofReal ((1 + (‖z‖ + ρ)) ^ 4) ^ |p| with hT
  have hB : MeasurableSet (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball.measurableSet
  -- the bounded-weight transfer, uniformly in the truncation height
  have hN : ∀ N : ℕ, ∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) ρ,
      (insertionTruncWeight γ α N (x - 0) : ℝ≥0∞) ∂M ω) ^ p ∂P ≤
        T * weightedGmcBallMoment P M γ α z ρ p := by
    intro N
    refine (gmc_weighted_ball_moment_transfer P X hX γ hγ hγ2 M hM 0 z ρ (‖z‖ + ρ) hρ hρ8
      (by positivity) (by simp) le_rfl (insertionTruncWeight γ α N)
      (measurable_insertionTruncWeight γ α N) (N : ℝ≥0) (insertionTruncWeight_le γ α N) p hp
      hp4).trans (mul_le_mul' le_rfl ?_)
    apply lintegral_mono
    intro ω
    refine ENNReal.rpow_le_rpow ?_ hp.le
    apply lintegral_mono
    intro x
    dsimp only
    rw [coe_insertionTruncWeight]
    exact insertionTruncWeightE_le_weight γ α N (x - z)
  -- monotone convergence in the truncation height
  have hmeas : ∀ N : ℕ, AEMeasurable (fun ω => (∫⁻ x in Metric.ball (0 : ℂ) ρ,
      (insertionTruncWeight γ α N (x - 0) : ℝ≥0∞) ∂M ω) ^ p) P := fun N =>
    (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (measurable_coe_nnreal_ennreal.comp ((measurable_insertionTruncWeight γ α N).comp
        (measurable_id.sub_const 0))) _ hB).pow_const p
  have hmono : ∀ᵐ ω ∂P, Monotone fun N : ℕ => (∫⁻ x in Metric.ball (0 : ℂ) ρ,
      (insertionTruncWeight γ α N (x - 0) : ℝ≥0∞) ∂M ω) ^ p := by
    refine Eventually.of_forall fun ω m n hmn => ENNReal.rpow_le_rpow ?_ hp.le
    apply lintegral_mono
    intro x
    simp only [coe_insertionTruncWeight]
    exact insertionTruncWeightE_mono γ α (x - 0) hmn
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∫⁻ x in Metric.ball (0 : ℂ) ρ,
      (insertionTruncWeight γ α N (x - 0) : ℝ≥0∞) ∂M ω) ^ p) atTop
        (𝓝 (ENNReal.rpow (weightedGmcBallMass γ (M ω) α 0 ρ) p)) :=
    Eventually.of_forall fun ω =>
      ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
        (insertionTrunc_mass_tendsto γ α (M ω) 0 ρ)
  have hconv := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  exact le_of_tendsto' hconv hN

end DOZZ.Proofs
