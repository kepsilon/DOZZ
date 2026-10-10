/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterWickCopy
public import DOZZ.Correlations.Tails.RandomScalarLimit

/-! Samplewise pin removal, with the original equator reference density retained. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The translated point in a local circle chart is outside the unit equator. -/
theorem local_circle_normPlus (z : ℂ) (hz : 2 ≤ ‖z‖)
    (p : localCircle) : normPlus (z + p.val.1) = ‖z + p.val.1‖ := by
  unfold normPlus
  apply max_eq_right
  have h := localCircle_exterior z hz p
  linarith [Real.exp_pos (-p.val.2)]

/-- Exact density ratio between the unpinned local chaos and the translated equator chaos. -/
theorem unpinned_density_ratio {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ) (ω : Ω) (p : localCircle) :
    Real.exp (γ * (Xc ω (z + p.val.1) p.val.2 - Xc ω z 0) - γ ^ 2 / 2 * p.val.2) =
      Real.exp (-γ * Xc ω z 0) *
        Real.exp ((γ ^ 2 + 4) * Real.log (normPlus (z + p.val.1))) *
        (Real.exp (γ * Xc ω (z + p.val.1) p.val.2 -
          γ ^ 2 / 2 * (p.val.2 + 2 * Real.log ‖z + p.val.1‖)) *
          normPlus (z + p.val.1) ^ (-4 : ℝ)) := by
  have hn : 0 < normPlus (z + p.val.1) := by unfold normPlus; positivity
  rw [Real.rpow_def_of_pos hn, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    local_circle_normPlus z hz p]
  congr 1
  ring

/-- The original and unpinned second moments at local circle coordinates. -/
theorem local_circle_second_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    (∫ ω, Xc ω (z+p.val.1) p.val.2 ^ 2 ∂P) =
        p.val.2 + 2 * Real.log ‖z+p.val.1‖ ∧
      (∫ ω, (Xc ω (z+p.val.1) p.val.2 - Xc ω z 0) ^ 2 ∂P) = p.val.2 := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨hG, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hmU : (∫ ω, Xc ω (z+p.val.1) p.val.2 - Xc ω z 0 ∂P) = 0 := by
    rw [integral_sub ((hc.2.1 _ _).integrable (by norm_num))
      ((hc.2.1 _ _).integrable (by norm_num)), hm, hm, sub_self]
  have hO := offCenter_circle_self_covariance P X Xc hX hc z hz p
  have hU := offCenter_unpinned_circle_covariance P X Xc hX hc z hz p p
  rw [local_circle_self_potential] at hU
  simp only [covariance, hm] at hO
  simp only [covariance, hmU] at hU
  simp only [sub_zero, ← pow_two] at hO hU
  exact ⟨hO, hU⟩

/-- Pin removal commutes with every local weighted cutoff integral, sample by sample. -/
theorem unpinned_weighted_cutoff_ratio
    {Ω S : Type*} [MeasurableSpace S] (ν : Measure S)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (γ : ℝ) (ω : Ω) (p : S → localCircle) (w : S → ℝ) :
    (∫ x, w x * Real.exp (γ * (Xc ω (z + (p x).val.1) (p x).val.2 - Xc ω z 0) -
      γ ^ 2 / 2 * (p x).val.2) ∂ν) =
      Real.exp (-γ * Xc ω z 0) *
        ∫ x, (w x * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus (z + (p x).val.1)))) *
          (Real.exp (γ * Xc ω (z + (p x).val.1) (p x).val.2 -
            γ ^ 2 / 2 * ((p x).val.2 + 2 * Real.log ‖z + (p x).val.1‖)) *
            normPlus (z + (p x).val.1) ^ (-4 : ℝ)) ∂ν := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [unpinned_density_ratio Xc z hz γ ω (p x)]
  ring


end DOZZ.Proofs
