/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.InnerPolar
public import DOZZ.FourPoint.Reflected.GlobalReinsertion
import Mathlib.Tactic
/-! The copied spatial inner mass has the actual unweighted lateral polar projection. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Reinsertion followed by radial projection recovers the logarithmic pushforward of the
lateral plane carrier. The only excluded mass is its null origin. -/
theorem reflected_reinserted_lateral_projection (γ : ℝ) (A : TwoSidedPath)
    (N : Measure ℂ) (h0 : N {0} = 0) :
    lateralProjectedGMC γ A (N.withDensity
      (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x))) =
        N.map (fun x => -Real.log ‖x‖) := by
  have hL : Measurable (lateralRadialWeight γ A) := by
    change Measurable ((fun p : (ℝ × TwoSidedPath) × ℂ =>
      lateralRadialWeight p.1.1 p.1.2 p.2) ∘ fun x : ℂ => ((γ, A), x))
    exact measurable_lateralRadialWeight.comp (measurable_const.prodMk measurable_id)
  have hW : Measurable (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have he : (N.withDensity (fun x => ENNReal.ofReal
      (reflected_global_reinsertionWeight γ A x))).withDensity (lateralRadialWeight γ A) =
      (N.withDensity (lateralRadialWeight γ A)).withDensity
        (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) := by
    rw [← withDensity_mul N hW hL, ← withDensity_mul N hL hW]
    congr 1
    funext x
    exact mul_comm (ENNReal.ofReal (reflected_global_reinsertionWeight γ A x))
      (lateralRadialWeight γ A x)
  change ((N.withDensity (fun x => ENNReal.ofReal
    (reflected_global_reinsertionWeight γ A x))).withDensity
      (lateralRadialWeight γ A)).map _ = _
  rw [he, reflected_global_reinsertion_measure]
  have hrest : N.restrict ({0} : Set ℂ)ᶜ = N :=
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp h0)
  rw [hrest]

/-- The actual independently reinserted inner radial mass equals its lateral polar integral. -/
theorem reflected_copied_inner_radial_polar (γ α : ℝ) (A : TwoSidedPath)
    (N : Measure ℂ) (h0 : N {0} = 0) (T : ℝ≥0) :
    (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
      ENNReal.ofReal (‖x‖ ^ (-(γ * α))) *
        ENNReal.ofReal (reflected_global_reinsertionWeight γ A x) ∂N) =
      ∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal
        (Real.exp (γ * (A s - (Q γ - α) * s))) ∂N.map (fun x => -Real.log ‖x‖) := by
  have hW : Measurable (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hi := reflected_inner_radial_polar γ α A
    (N.withDensity (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x))) T
  rw [reflected_reinserted_lateral_projection γ A N h0] at hi
  have hf : Measurable (fun x : ℂ => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))) := by fun_prop
  have hU : MeasurableSet {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  rw [setLIntegral_withDensity_eq_setLIntegral_mul N hW hf hU] at hi
  simpa only [Pi.mul_apply, mul_comm] using hi

/-- The actual removed plane carrier projects to the source lateral GMC on one common
full-measure event; its plane origin has zero mass on that event. -/
theorem reflected_removed_carrier_projection
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (A : Ω → TwoSidedPath) (M N : Ω → Measure ℂ)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (A ω)))) :
    ∀ᵐ ω ∂P, N ω {0} = 0 ∧
      (N ω).map (fun x => -Real.log ‖x‖) = lateralProjectedGMC γ (A ω) (M ω) := by
  filter_upwards [heq] with ω hω
  rw [hω]
  constructor
  · rw [withDensity_apply _ (measurableSet_singleton (0 : ℂ))]
    calc
      (∫⁻ x in ({0} : Set ℂ), lateralRadialWeight γ (A ω) x ∂M ω) =
          ∫⁻ x in ({0} : Set ℂ), (0 : ℝ≥0∞) ∂M ω := by
        apply setLIntegral_congr_fun (measurableSet_singleton (0 : ℂ))
        intro x hx
        rw [mem_singleton_iff.mp hx, lateralRadialWeight_zero]
      _ = 0 := lintegral_zero
  · rfl

/-- Independently reinserted inner masses restart against the translated actual source lateral
measure, uniformly over the copied radial path and deterministic restart time. -/
theorem reflected_copied_inner_source_restart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (A : Ω → TwoSidedPath) (M N : Ω → Measure ℂ)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (A ω)))) :
    ∀ᵐ ω ∂P, ∀ a : TwoSidedPath, ∀ T : ℝ≥0,
      (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
        ENNReal.ofReal (‖x‖ ^ (-(γ * α))) *
          ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω) =
        ENNReal.ofReal (Real.exp (γ * (a T - (Q γ - α) * T))) *
          ∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
            (γ * (brownianShiftPath T (radialPositiveHalf a) (Real.toNNReal u) -
              (Q γ - α) * u))) else 0)
            ∂(lateralProjectedGMC γ (A ω) (M ω)).map (fun s => s - (T : ℝ)) := by
  filter_upwards [reflected_removed_carrier_projection P γ A M N heq] with ω hω a T
  rw [reflected_copied_inner_radial_polar γ α a (N ω) hω.1 T, hω.2]
  exact reflected_inner_polar_restart γ (Q γ - α) a _ T

end DOZZ.Proofs
