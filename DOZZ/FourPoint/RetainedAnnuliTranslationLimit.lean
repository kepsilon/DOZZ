/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliTranslation
public import DOZZ.FourPoint.RetainedAnnuliMomentConvergence

/-! The bounded-chart joint translation estimate on the supplied GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Simultaneous translation of two retained disks in the supplied limiting chaos. -/
theorem gmc_joint_ball_inverse_translate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z z₀ u v : ℂ) (ρ σ τ L a b : ℝ) (hL : 0 ≤ L)
    (hρ : 0 < ρ) (hσ : 0 < σ) (hρ8 : ρ ≤ 1 / 8) (hσ8 : σ ≤ 1 / 8)
    (hzL : ‖z‖ + τ ≤ L) (hz₀L : ‖z₀‖ + τ ≤ L)
    (hu : Metric.ball u ρ ⊆ Metric.ball 0 τ) (hv : Metric.ball v σ ⊆ Metric.ball 0 τ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ ω, (M ω (Metric.ball (u + z) ρ)) ^ (-a) * (M ω (Metric.ball (v + z) σ)) ^ (-b) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * gmcCircleChartRemainder L) / 2 *
        ((a + b) ^ 2 + a + b))) * ENNReal.ofReal ((1 + L) ^ 4) ^ (a + b) *
          ∫⁻ ω, (M ω (Metric.ball (u + z₀) ρ)) ^ (-a) *
            (M ω (Metric.ball (v + z₀) σ)) ^ (-b) ∂P := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * gmcCircleChartRemainder L) / 2 *
    ((a + b) ^ 2 + a + b))) * ENNReal.ofReal ((1 + L) ^ 4) ^ (a + b)
  have hT : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (add_nonneg ha hb) ENNReal.ofReal_ne_top)
  have hleft := gmc_joint_ball_inverse_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc
    (u + z) (v + z) ρ σ a b hρ hσ hρ8 hσ8 ha hb
  have hright := ENNReal.Tendsto.const_mul
    (gmc_joint_ball_inverse_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc
      (u + z₀) (v + z₀) ρ σ a b hρ hσ hρ8 hσ8 ha hb) (Or.inr hT)
  exact le_of_tendsto_of_tendsto' hleft hright (fun n =>
    cutoff_joint_ball_inverse_translate P X hX Xc hXc γ n (Nat.cast_nonneg n)
      z z₀ u v ρ σ τ L a b hL hzL hz₀L hu hv ha hb)

end DOZZ.Proofs
