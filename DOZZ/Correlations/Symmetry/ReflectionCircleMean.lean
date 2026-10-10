/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.RepinnedCircleCovariance
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace DOZZ.Proofs

/-- Circle integration can be expressed on a fixed origin circle. -/
theorem symmetryReflection_circle_translate (f : ℂ → ℝ) (hf : Measurable f) (x : ℂ) (r : ℝ) :
    (∫ z, f z ∂circleMeasure x r) = ∫ z, f (z + x) ∂circleMeasure 0 r := by
  have hfx : Measurable (fun z => f (z + x)) := hf.comp (measurable_id.add_const x)
  rw [integral_circleMeasure_eq_circleAverage x r f hf,
    integral_circleMeasure_eq_circleAverage 0 r _ hfx,
    Real.circleAverage_eq_circleAverage_zero_one (f := f) (c := x) (R := Real.exp (-r)),
    Real.circleAverage_eq_circleAverage_zero_one (f := fun z => f (z + x))
      (c := 0) (R := Real.exp (-r))]
  congr 1
  funext z
  simp only [add_zero]

/-- The bounded continuous circle mean of reflection's pinning potential. -/
noncomputable def symmetryCirclePotentialMean (r : ℝ) : BoundedContinuousFunction ℂ ℝ := by
  let F : ℂ → ℝ := fun x => ∫ z, symmetryReflectionPotential z ∂circleMeasure x r
  have hF : Continuous F := by
    have he : F = fun x => ∫ z, symmetryReflectionPotential (z + x) ∂circleMeasure 0 r := by
      funext x
      exact symmetryReflection_circle_translate _ symmetryReflectionPotential_continuous.measurable x r
    rw [he]
    let := circleMeasure_isProbability (0 : ℂ) r
    rw [continuous_iff_continuousAt]
    intro x
    apply continuousAt_of_dominated (bound := fun _ => Real.log 2)
    · exact .of_forall (fun y =>
        (symmetryReflectionPotential_continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    · exact .of_forall (fun y => ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs]
        exact symmetryReflectionPotential_bound (z + y)))
    · exact integrable_const _
    · exact ae_of_all _ (fun z =>
        (symmetryReflectionPotential_continuous.comp (continuous_const.add continuous_id)).continuousAt)
  have hbound (x : ℂ) : |F x| ≤ Real.log 2 := by
    let := circleMeasure_isProbability x r
    have hi : Integrable (fun z => symmetryReflectionPotential z) (circleMeasure x r) :=
      integrable_circleMeasure_of_circleIntegrable x r symmetryReflectionPotential_continuous.measurable
        symmetryReflectionPotential_continuous.continuousOn.circleIntegrable'
    calc
      _ ≤ ∫ z, |symmetryReflectionPotential z| ∂circleMeasure x r := abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℂ, Real.log 2 ∂circleMeasure x r :=
        integral_mono hi.norm (integrable_const _) (symmetryReflectionPotential_bound)
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  exact BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (2 * Real.log 2) (fun x y => by
    change dist (F x) (F y) ≤ _
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith only [hbound x, hbound y]))

theorem symmetryCirclePotentialMean_apply (r : ℝ) (x : ℂ) :
    symmetryCirclePotentialMean r x = ∫ z, symmetryReflectionPotential z ∂circleMeasure x r := rfl

theorem symmetryCirclePotentialMean_bound (r : ℝ) (x : ℂ) :
    |symmetryCirclePotentialMean r x| ≤ Real.log 2 := by
  let := circleMeasure_isProbability x r
  rw [symmetryCirclePotentialMean_apply]
  have hi : Integrable (fun z => symmetryReflectionPotential z) (circleMeasure x r) :=
    integrable_circleMeasure_of_circleIntegrable x r symmetryReflectionPotential_continuous.measurable
      symmetryReflectionPotential_continuous.continuousOn.circleIntegrable'
  calc
    _ ≤ ∫ z, |symmetryReflectionPotential z| ∂circleMeasure x r := abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℂ, Real.log 2 ∂circleMeasure x r :=
      integral_mono hi.norm (integrable_const _) symmetryReflectionPotential_bound
    _ = _ := by rw [integral_const, probReal_univ, one_smul]

end DOZZ.Proofs
