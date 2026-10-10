/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ExtendedTail
public import DOZZ.Correlations.Residue.TailCoefficient
public import DOZZ.Correlations.Residue.TailMargins
public import DOZZ.Correlations.Tails.SingularMassMeasurability

/-! Source-specific local moment reductions for the unequal and equal branches of the
three-to-two residue bridge. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exact one-insertion tail estimate gives the critical local moment residue. -/
theorem residue_oneInsertion_local_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 Rbar η d₀ C : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα3 : γ / 2 < α3) (hα3Q : α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hη : 0 < η) (hd₀ : 0 < d₀) (hC : 0 ≤ C)
    (htail : ∀ ε, 0 < ε → ε < d₀ → ∀ t : ℝ, 1 ≤ t →
      |(P {ω | ENNReal.ofReal t < localSingularMass M
        (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3 ω}).toReal -
        oneInsertionTailCoefficient γ α3 3 (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar *
          t ^ (-reflectionExponent γ α3)| ≤ C * t ^ (-reflectionExponent γ α3 - η)) :
    Tendsto (fun ε : ℝ => ε * ∫ ω,
      (localSingularMass M (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3 ω).toReal ^
        (reflectionExponent γ α3 - ε / γ) ∂P) (𝓝[>] 0)
      (𝓝 (γ * reflectionExponent γ α3 * (4 : ℝ) ^
        (-(γ * α2 * reflectionExponent γ α3)) * Rbar)) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hcoef := residue_chart_tail_coefficient_limit γ α3 α2 Rbar hγ.ne' 3 7
    (by norm_num) (by norm_num) (by norm_num)
  have hn : ‖(3 : ℂ) - 7‖ = 4 := by norm_num
  have hh := residue_extended_uniform_tail_limit P
    (fun ε => localSingularMass M (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3)
    (fun ε => oneInsertionTailCoefficient γ α3 3
      (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar)
    ((4 : ℝ) ^ (-(γ * α2 * reflectionExponent γ α3)) * Rbar)
    (reflectionExponent γ α3) η γ d₀ C
    (residue_critical_order_bounds γ α3 hγ hα3 hα3Q).1 hη hγ hd₀ hC
    (fun ε _ _ => localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _)
    (by simpa only [hn] using hcoef) htail
  convert hh using 1
  congr 1
  ring

/-- The equal-charge two-insertion estimate is coalesced before taking the moment limit.
The strict tail ceiling supplies a positive error; the leading coefficient is the sum. -/
theorem residue_twoInsertion_equal_local_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α Rbar d₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : γ / 2 < α) (hαQ : α < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (hd₀ : 0 < d₀)
    (htail : ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε, 0 < ε → ε < d₀ → ∀ t : ℝ, 1 ≤ t →
        |(P {ω | ENNReal.ofReal t <
            localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
            localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω}).toReal -
          (oneInsertionTailCoefficient γ α 3 (residueLocalWeight γ (2 * α + ε) α 7 3) Rbar * t ^ (-reflectionExponent γ α) +
           oneInsertionTailCoefficient γ α 7 (residueLocalWeight γ (2 * α + ε) α 3 7) Rbar * t ^ (-reflectionExponent γ α))| ≤
          C * t ^ (-(twoInsertionTailCeiling γ α α - θ))) :
    Tendsto (fun ε : ℝ => ε * ∫ ω,
      (localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
       localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω).toReal ^
         (reflectionExponent γ α - ε / γ) ∂P) (𝓝[>] 0)
      (𝓝 (2 * γ * reflectionExponent γ α * (4 : ℝ) ^
        (-(γ * α * reflectionExponent γ α)) * Rbar)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let p := reflectionExponent γ α
  let θ := (twoInsertionTailCeiling γ α α - p) / 2
  have hθ : 0 < θ := div_pos (sub_pos.mpr (residue_equal_twoInsertionTailCeiling_gt γ α hγ hα hαQ)) (by norm_num)
  obtain ⟨C, hC, hCb⟩ := htail θ hθ
  have hexp : -(twoInsertionTailCeiling γ α α - θ) = -p - θ := by dsimp only [θ]; ring
  have hn37 : ‖(3 : ℂ) - 7‖ = 4 := by norm_num
  have hn73 : ‖(7 : ℂ) - 3‖ = 4 := by norm_num
  have hc1 := residue_chart_tail_coefficient_limit γ α α Rbar hγ.ne' 3 7 (by norm_num) (by norm_num) (by norm_num)
  have hc2 := residue_chart_tail_coefficient_limit γ α α Rbar hγ.ne' 7 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hn37] at hc1
  rw [hn73] at hc2
  have hh := residue_extended_uniform_tail_limit P
    (fun ε ω => localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
      localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω)
    (fun ε => oneInsertionTailCoefficient γ α 3 (residueLocalWeight γ (2 * α + ε) α 7 3) Rbar +
      oneInsertionTailCoefficient γ α 7 (residueLocalWeight γ (2 * α + ε) α 3 7) Rbar)
    ((4 : ℝ) ^ (-(γ * α * p)) * Rbar + (4 : ℝ) ^ (-(γ * α * p)) * Rbar)
    p θ γ d₀ C (residue_critical_order_bounds γ α hγ hα hαQ).1 hθ hγ hd₀ hC
    (fun ε _ _ =>
      (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
        (by unfold residueLocalWeight; fun_prop) _ _).add
      (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
        (by unfold residueLocalWeight; fun_prop) _ _))
    (hc1.add hc2) (by
      intro ε hε hεd t ht
      have hh := hCb ε hε hεd t ht
      rw [hexp, ← add_mul] at hh
      exact hh)
  convert hh using 1
  congr 1
  dsimp only [p]
  ring

end DOZZ.Proofs
