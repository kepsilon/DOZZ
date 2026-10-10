/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedCenterTransfer

/-! # Location transfer of weighted local moments between two centers

The truncated-weight argument of `weightedGmcBallMoment_center_le_transfer` works between any two
centers of small disks inside a common disk about the origin: the weighted local moment at one
center is bounded by the explicit transfer constant times the weighted local moment at the other. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The weighted local moment at one center is bounded by an explicit constant times the weighted
local moment at another center, for small disks and positive subcritical orders. -/
theorem weightedGmcBallMoment_le_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : ℝ) (z₁ z₂ : ℂ) (ρ R : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hR : 0 ≤ R)
    (h₁ : ‖z₁‖ + ρ ≤ R) (h₂ : ‖z₂‖ + ρ ≤ R) (p : ℝ) (hp : 0 < p) (hp4 : p < 4 / γ ^ 2) :
    weightedGmcBallMoment P M γ α z₁ ρ p ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
          |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
        weightedGmcBallMoment P M γ α z₂ ρ p := by
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 +
      2 * Real.log (1 + R))) / 2 * |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| with hT
  have hB : MeasurableSet (Metric.ball z₁ ρ) := Metric.isOpen_ball.measurableSet
  -- the bounded-weight transfer, uniformly in the truncation height
  have hN : ∀ N : ℕ, ∫⁻ ω, (∫⁻ x in Metric.ball z₁ ρ,
      (insertionTruncWeight γ α N (x - z₁) : ℝ≥0∞) ∂M ω) ^ p ∂P ≤
        T * weightedGmcBallMoment P M γ α z₂ ρ p := by
    intro N
    refine (gmc_weighted_ball_moment_transfer P X hX γ hγ hγ2 M hM z₁ z₂ ρ R hρ hρ8 hR h₁ h₂
      (insertionTruncWeight γ α N) (measurable_insertionTruncWeight γ α N) (N : ℝ≥0)
      (insertionTruncWeight_le γ α N) p hp hp4).trans (mul_le_mul' le_rfl ?_)
    apply lintegral_mono
    intro ω
    refine ENNReal.rpow_le_rpow ?_ hp.le
    apply lintegral_mono
    intro x
    dsimp only
    rw [coe_insertionTruncWeight]
    exact insertionTruncWeightE_le_weight γ α N (x - z₂)
  -- monotone convergence in the truncation height
  have hmeas : ∀ N : ℕ, AEMeasurable (fun ω => (∫⁻ x in Metric.ball z₁ ρ,
      (insertionTruncWeight γ α N (x - z₁) : ℝ≥0∞) ∂M ω) ^ p) P := fun N =>
    (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (measurable_coe_nnreal_ennreal.comp ((measurable_insertionTruncWeight γ α N).comp
        (measurable_id.sub_const z₁))) _ hB).pow_const p
  have hmono : ∀ᵐ ω ∂P, Monotone fun N : ℕ => (∫⁻ x in Metric.ball z₁ ρ,
      (insertionTruncWeight γ α N (x - z₁) : ℝ≥0∞) ∂M ω) ^ p := by
    refine Eventually.of_forall fun ω m n hmn => ENNReal.rpow_le_rpow ?_ hp.le
    apply lintegral_mono
    intro x
    simp only [coe_insertionTruncWeight]
    exact insertionTruncWeightE_mono γ α (x - z₁) hmn
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∫⁻ x in Metric.ball z₁ ρ,
      (insertionTruncWeight γ α N (x - z₁) : ℝ≥0∞) ∂M ω) ^ p) atTop
        (𝓝 (ENNReal.rpow (weightedGmcBallMass γ (M ω) α z₁ ρ) p)) :=
    Eventually.of_forall fun ω =>
      ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
        (insertionTrunc_mass_tendsto γ α (M ω) z₁ ρ)
  have hconv := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  exact le_of_tendsto' hconv hN

end DOZZ.Proofs
