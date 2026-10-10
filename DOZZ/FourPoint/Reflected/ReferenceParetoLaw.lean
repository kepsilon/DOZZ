/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.MaximumParetoLaw
/-! The exponentiated Williams reference maximum has the literal Pareto law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- The independent reference maximum used in the transported Williams model is exactly the
Pareto variable used in the signed source estimates. -/
theorem reflected_maximum_reference_pareto_law
    (B₀ : Measure BrownianPath) (hB₀ : IsBrownianReal (fun t p => p t) B₀)
    (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) :
    (brownianMaximumReferenceLaw ν).map (fun m => Real.exp (γ*m)) =
      paretoMeasure 1 (2*ν/γ) := by
  rw [← brownianPath_globalMaximum_map B₀ hB₀ ν hν,
    AEMeasurable.map_map_of_aemeasurable
      (show AEMeasurable (fun m : ℝ => Real.exp (γ*m)) (B₀.map (driftedBrownianMaximum ν)) from
        (by fun_prop : Measurable (fun m : ℝ => Real.exp (γ*m))).aemeasurable)
      (aemeasurable_driftedBrownianMaximum B₀ hB₀ ν hν)]
  exact reflected_brownian_maximum_pareto_law B₀ hB₀ γ ν hγ hν

end DOZZ.Proofs
