/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.TailMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The tail hypothesis itself implies almost-sure finiteness of extended insertion masses. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A strictly decaying power-tail estimate excludes infinite insertion mass. -/
theorem residue_ae_finite_of_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞) (c β η C : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |(P {ω | ENNReal.ofReal t < Y ω}).toReal - c * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    ∀ᵐ ω ∂P, Y ω ≠ ⊤ := by
  have hb : Tendsto (fun t : ℝ => c * t ^ (-β) + C * t ^ (-β - η)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_rpow_neg_atTop hβ).const_mul c).add
        ((by simpa only [neg_add_rev, add_comm, sub_eq_add_neg] using tendsto_rpow_neg_atTop (add_pos hβ hη) :
          Tendsto (fun t : ℝ => t ^ (-β - η)) atTop (𝓝 0)).const_mul C)
  have hbound : ∀ᶠ t : ℝ in atTop,
      (P {ω | Y ω = ⊤}).toReal ≤ c * t ^ (-β) + C * t ^ (-β - η) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hm : P {ω | Y ω = ⊤} ≤ P {ω | ENNReal.ofReal t < Y ω} :=
      measure_mono (fun ω hω => by simp only [mem_ofPred_eq] at hω ⊢; rw [hω]; exact ENNReal.ofReal_lt_top)
    have hmr := ENNReal.toReal_mono (measure_ne_top P _) hm
    have herr := (abs_le.mp (htail t ht)).2
    linarith only [hmr, herr]
  have hz : (P {ω | Y ω = ⊤}).toReal ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hb hbound
  have hmzero : P {ω | Y ω = ⊤} = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hz ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top P _)
  exact measure_eq_zero_iff_ae_notMem.mp hmzero

/-- Extended masses with the uniform tail remainder have the real moment residue used in the
three-to-two residue bridge. Almost-sure finiteness is derived from the tail estimate for each
member of the family. -/
theorem residue_extended_uniform_tail_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ≥0∞) (c : ℝ → ℝ) (c₀ β η γ d₀ C : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hC : 0 ≤ C)
    (hY : ∀ d, 0 < d → d < d₀ → AEMeasurable (Y d) P)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀))
    (htail : ∀ d, 0 < d → d < d₀ → ∀ t : ℝ, 1 ≤ t →
      |(P {ω | ENNReal.ofReal t < Y d ω}).toReal - c d * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    Tendsto (fun d => d * ∫ ω, (Y d ω).toReal ^ (β - d / γ) ∂P)
      (𝓝[>] 0) (𝓝 (γ * β * c₀)) := by
  apply residue_real_uniform_tail_limit P (fun d ω => (Y d ω).toReal) c c₀ β η γ d₀ C
    hβ hη hγ hd₀ hC
    (fun d hd hd' => ENNReal.measurable_toReal.comp_aemeasurable (hY d hd hd'))
    (fun _ _ _ => ae_of_all _ fun _ => ENNReal.toReal_nonneg) hc
  intro d hd hd' t ht
  rw [residue_realUpperTail_toReal P (Y d) (hY d hd hd')
    (residue_ae_finite_of_tail P (Y d) (c d) β η C hβ hη (htail d hd hd')) t (by linarith only [ht])]
  exact htail d hd hd' t ht

end DOZZ.Proofs
