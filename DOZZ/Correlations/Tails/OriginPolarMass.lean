/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TranslatedPolar
public import DOZZ.Correlations.Tails.TranslatedField
public import DOZZ.Statements.Brownian.LateralProjectedGMC

/-! The exact positive-time polar integral for the canonical translated equator chaos. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem origin_polar_measure_eq (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) :
    translatedPolarMeasure γ 0 A M (fun _ => 1) 0 = lateralProjectedGMC γ A M := by
  unfold translatedPolarMeasure lateralProjectedGMC
  have hd : (fun x : ℂ => ENNReal.ofReal (1 : ℝ) *
      (if x = 0 then 0 else ENNReal.ofReal
        (Real.exp (-γ * (0 + A (translatedLogRadius 0 x)) +
          γ * Q γ * |translatedLogRadius 0 x|)))) =
      (fun x : ℂ => ENNReal.ofReal (if ‖x‖ = 0 then 0 else
        Real.exp (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|))) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp only [norm_zero, ite_true, mul_zero, ENNReal.ofReal_zero]
    · simp only [translatedLogRadius, sub_zero, zero_add, abs_neg,
        ENNReal.ofReal_one, one_mul, ite_eq_right hx,
        ite_eq_right (norm_ne_zero_iff.mpr hx)]
  rw [hd]
  congr 1
  funext x
  simp only [translatedLogRadius, sub_zero]

/-- Removing the radial Wick factor identifies the canonical singular mass with its inward
drifted Brownian exponential integral, without changing the insertion at the origin. -/
theorem origin_singular_mass_polar
    (γ α : ℝ) (A : TwoSidedPath) (M : Measure ℂ) (hM0 : M {0} = 0) :
    localSingularMass (fun _ : Unit => M) (fun _ => 1) 0 γ α () =
      ∫⁻ t, (if 0 < t then ENNReal.ofReal
        (Real.exp (γ * (A t - (Q γ - α) * t))) else 0)
          ∂lateralProjectedGMC γ A M := by
  rw [localSingularMass_translatedPolar γ α 0 A M (fun _ => 1)
    measurable_const 0 hM0, origin_polar_measure_eq]
  simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- The positive-time polar identity applies almost surely to the actual translated source
GMC, since its deterministic insertion center has zero mass. -/
theorem translated_canonical_singular_mass_polar
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (A : Ω → TwoSidedPath) :
    ∀ᵐ ω ∂P, localSingularMass N (fun _ => 1) 0 γ α ω =
      ∫⁻ t, (if 0 < t then ENNReal.ofReal
        (Real.exp (γ * (A ω t - (Q γ - α) * t))) else 0)
          ∂lateralProjectedGMC γ (A ω) (N ω) := by
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P (translatedField X Xc z)
    (translated_field_isEquatorGFF P X Xc hX hc z) γ hγ hγ2 N hN 0] with ω hω
  exact origin_singular_mass_polar γ α (A ω) (N ω) hω


end DOZZ.Proofs
