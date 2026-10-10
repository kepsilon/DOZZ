/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingInverseMoments
import Mathlib.Topology.Sequences

/-! # The inverse expectation appearing in the scaled fusion integrand -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The fused subcritical charge leaves room for a small positive moment. -/
theorem fusion_small_moment_order (γ α₁ : ℝ) (hγ : 0 < γ) (hα₁ : α₁ < 2 / γ) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      p < min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2))) := by
  have hgap : 0 < Q γ - (α₁ + γ / 2) := by unfold Q; linarith
  let b := min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2)))
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  refine ⟨min 1 b / 2, by positivity, ?_, ?_⟩
  · have := min_le_left (1 : ℝ) b
    linarith
  · have := min_le_right (1 : ℝ) b
    have : 0 < min (1 : ℝ) b := lt_min zero_lt_one hb
    linarith

/-- Inverse expectations converge at zero without a first moment assumption on the mass. -/
theorem fusionMovingMass_inverse_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (y : ℂ) (hy : y ≠ 0)
    (s : ℝ) (hs : s < 0) :
    Tendsto (fun z => ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P)
      (nhds 0) (nhds (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) ^ s ∂P)) := by
  obtain ⟨p, hp, hp1, hpRange⟩ := fusion_small_moment_order γ α₁ hγ hα₁
  apply tendsto_iff_seq_tendsto.mpr
  intro z hz
  exact fusionMovingMass_inverse_expectation_seq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p
    hα hα₁ hα₂ hα₃ hp hp1 hpRange y hy z hz s hs

/-- The limiting inverse expectation is finite, as needed for `toReal` continuity. -/
theorem fusionMovingMass_inverse_expectation_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) (y : ℂ) :
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) ^ s ∂P) < ⊤ := by
  obtain ⟨C, hC, hbound⟩ := fusionMovingMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ s hs
  exact (hbound y 0 (by simp)).trans_lt hC

end DOZZ.Proofs
