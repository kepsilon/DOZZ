/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ComplementMass

/-! Uniform higher moments of the actual noncritical complement masses. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- In the three-to-two residue bridge, the actual critical-ball complement has a uniform moment
above the critical order, including when the smaller charge is at or below gamma/2. -/
theorem residue_unequal_complement_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα2 : 0 < α2) (hα23 : α2 < α3) (hα3 : γ / 2 < α3) (hα3Q : α3 < Q γ) :
    ∃ d₀ ρ : ℝ, 0 < d₀ ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d₀ →
        ∫⁻ ω, ENNReal.rpow (∫⁻ x, if x ∉ Metric.ball (3 : ℂ) 1 then
          coulombWeight γ ![α3, α2] ![3, 7] (α3 - α2 + ε) x else 0 ∂M ω)
          (reflectionExponent γ α3 + ρ) ∂P ≤ K := by
  obtain ⟨d₀, ρ, hd₀, hρ, K, hK, hKb⟩ := residue_unequal_competitor_coulomb_moment
    P X M γ α2 α3 hγ hγ2 hX hM hα2 hα23 hα3 hα3Q
  let t := reflectionExponent γ α3 + ρ
  have ht : 0 ≤ t := (add_pos (residue_critical_order_bounds γ α3 hγ hα3 hα3Q).1 hρ).le
  have hcoef : (ENNReal.ofReal ((5 : ℝ) ^ (γ * α3))) ^ t < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg ht ENNReal.ofReal_ne_top
  refine ⟨d₀, ρ, hd₀, hρ, (ENNReal.ofReal ((5 : ℝ) ^ (γ * α3))) ^ t * K,
    ENNReal.mul_lt_top hcoef hK, ?_⟩
  intro ε hε hεd
  have hα3pos : 0 < α3 := lt_trans (by positivity) hα3
  have hh := residue_complement_moment_le P M γ α3 α2 (α3 - α2 + ε) t
    (mul_nonneg hγ.le hα3pos.le) ht 3 7
  norm_num only [Complex.norm_ofNat] at hh
  exact hh.trans (mul_le_mul_right (hKb ε hε hεd) _)

/-- The equal-charge complement outside both critical balls also has a uniform moment
strictly above the common pole. -/
theorem residue_equal_complement_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : γ / 2 < α) (hαQ : α < Q γ) :
    ∃ d₀ ρ : ℝ, 0 < d₀ ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d₀ →
        ∫⁻ ω, ENNReal.rpow (∫⁻ x, if ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1 then
          coulombWeight γ ![α, α] ![3, 7] ε x else 0 ∂M ω)
          (reflectionExponent γ α + ρ) ∂P ≤ K := by
  obtain ⟨d₀, ρ, hd₀, hρ, K, hK, hKb⟩ := residue_equal_background_coulomb_moment
    P X M γ α hγ hγ2 hX hM hα hαQ
  let t := reflectionExponent γ α + ρ
  let A := ∏ k : Fin 2, ENNReal.ofReal ((‖(![3, 7] : Fin 2 → ℂ) k‖ + 2) ^ (γ * α))
  have ht : 0 ≤ t := (add_pos (residue_critical_order_bounds γ α hγ hα hαQ).1 hρ).le
  have hAtop : A ≠ ⊤ := (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)).ne
  have hcoef : A ^ t < ⊤ := ENNReal.rpow_lt_top_of_nonneg ht hAtop
  refine ⟨d₀, ρ, hd₀, hρ, A ^ t * K, ENNReal.mul_lt_top hcoef hK, ?_⟩
  intro ε hε hεd
  have hαpos : 0 < α := lt_trans (by positivity) hα
  have hh := residue_all_complement_moment_le P M γ ε t ![α, α]
    (fun k => by fin_cases k <;> exact mul_nonneg hγ.le hαpos.le) ![3, 7] ht
  exact hh.trans (mul_le_mul_right (hKb ε hε hεd) _)

end DOZZ.Proofs
