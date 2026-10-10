/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionCutoff
public import DOZZ.Correlations.Symmetry.ReflectionCutoffWeight
public import DOZZ.Correlations.Symmetry.ReflectionWeightedLimit
@[expose] public section
open MeasureTheory
open scoped Distributions ENNReal
namespace DOZZ.Proofs

/-- The coupled chaos measure obtained by reflection and correlated equator re-pinning. -/
noncomputable def symmetryRepinnedChaos {Ω : Type*} (γ : ℝ) (M : Ω → Measure ℂ)
    (L : Ω → ℝ) (ω : Ω) : Measure ℂ :=
  ENNReal.ofReal (Real.exp (-γ * L ω)) •
    ((M ω).map (fun x : ℂ => 1 - x)).withDensity
      (fun x => ENNReal.ofReal (symmetryReflectionLimitWeight γ x))

theorem symmetryRepinnedChaos_finite {Ω : Type*} (γ : ℝ) (M : Ω → Measure ℂ)
    (L : Ω → ℝ) (hM : ∀ ω, IsFiniteMeasure (M ω)) (ω : Ω) :
    IsFiniteMeasure (symmetryRepinnedChaos γ M L ω) := by
  let := hM ω
  let := symmetry_bcf_withDensity_finite ((M ω).map (fun x : ℂ => 1 - x))
    (symmetryReflectionLimitWeight γ)
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

/-- Real test integrals of a reflected weighted measure use the literal affine pullback. -/
theorem symmetry_reflection_weighted_integral (μ : Measure ℂ)
    (w f : BoundedContinuousFunction ℂ ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∫ x, f x ∂(μ.map (fun x : ℂ => 1 - x)).withDensity
      (fun x => ENNReal.ofReal (w x))) = ∫ x, f (1 - x) * w (1 - x) ∂μ := by
  have hW : Measurable (fun x => ENNReal.ofReal (w x)) :=
    ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hfinite : ∀ᵐ x ∂μ.map (fun x : ℂ => 1 - x), ENNReal.ofReal (w x) < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul hW hfinite]
  have he : (fun x => (ENNReal.ofReal (w x)).toReal • f x) = fun x => f x * w x := by
    funext x
    rw [ENNReal.toReal_ofReal (hw x), smul_eq_mul, mul_comm]
  rw [he]
  exact integral_map (measurable_const.sub measurable_id).aemeasurable
    (f.continuous.mul w.continuous).aestronglyMeasurable

theorem symmetryRepinnedChaos_integral {Ω : Type*} (γ : ℝ) (M : Ω → Measure ℂ)
    (L : Ω → ℝ) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) :
    (∫ x, f x ∂symmetryRepinnedChaos γ M L ω) = Real.exp (-γ * L ω) *
      ∫ x, f (1 - x) * symmetryReflectionLimitWeight γ (1 - x) ∂M ω := by
  rw [symmetryRepinnedChaos, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
    symmetry_reflection_weighted_integral _ _ f
      (fun x => by rw [symmetryReflectionLimitWeight_apply]; exact (Real.exp_pos _).le)]

theorem regularizedGMC_symmetryRepinned_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) :
    (∫ x, f x ∂regularizedGMC P (fun ω x r => Xc ω (1 - x) r - Xc ω 1 0) γ r ω) =
      Real.exp (-γ * Xc ω 1 0) *
        ∫ x, f (1 - x) * symmetryReflectionCutoffWeight γ r (1 - x)
          ∂regularizedGMC P Xc γ r ω := by
  rw [regularizedGMC_symmetryRepinned P X hX Xc hXc]
  have he : (fun x => ENNReal.ofReal (Real.exp (-γ * Xc ω 1 0 +
      γ ^ 2 * symmetryCirclePotentialMean r x + 4 * symmetryReflectionPotential x))) =
      ENNReal.ofReal (Real.exp (-γ * Xc ω 1 0)) •
        (fun x => ENNReal.ofReal (symmetryReflectionCutoffWeight γ r x)) := by
    funext x
    simp only [Pi.smul_apply]
    rw [symmetryReflectionCutoffWeight_apply, smul_eq_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hW : Measurable (fun x => ENNReal.ofReal (symmetryReflectionCutoffWeight γ r x)) :=
    ENNReal.measurable_ofReal.comp (symmetryReflectionCutoffWeight γ r).continuous.measurable
  rw [he, withDensity_smul _ hW, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
    symmetry_reflection_weighted_integral _ _ f
      (fun x => by rw [symmetryReflectionCutoffWeight_apply]; exact (Real.exp_pos _).le)]
end DOZZ.Proofs
