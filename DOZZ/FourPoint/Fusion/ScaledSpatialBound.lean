/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ScaledSpatialConvergence
/-! # Uniform absolute bounds on scaled spatial integrals -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs
/-- The uniform rooted factor bounds every absolutely integrable signed planar kernel. -/
theorem fusionScaledIntegral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) (K : ℂ → ℂ) (hK : Integrable K volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := fusionScaledFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs
  refine ⟨(∫ y : ℂ, ‖K y‖) * B, mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hB, ?_⟩
  intro z hz
  calc
    _ ≤ ∫ y : ℂ, ‖K y‖ * B := by
      apply norm_integral_le_of_norm_le (hK.norm.mul_const B)
      exact ae_of_all _ fun y => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hb y z hz) (norm_nonneg _)
    _ = _ := integral_mul_const _ _
end DOZZ.Proofs
