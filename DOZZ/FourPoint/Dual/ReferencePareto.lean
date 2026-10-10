/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.MaximumParetoLaw
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! Exact Pareto transport of the Williams reference maximum. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- The exponential of the Williams reference maximum has the exact Pareto law. -/
theorem dual_reference_maximum_exp_pareto_law (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) :
    (brownianMaximumReferenceLaw ν).map (fun m => Real.exp (γ*m)) =
      paretoMeasure 1 (2*ν/γ) := by
  rw [← brownianPath_globalMaximum_map P hB ν hν,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      (aemeasurable_driftedBrownianMaximum P hB ν hν)]
  exact reflected_brownian_maximum_pareto_law P hB γ ν hγ hν

/-- Transporting the signed scalar increment retains its genuine real integral, including
Lean's total integral convention when its parameters are not integrable. -/
theorem dual_reference_maximum_increment (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν)
    (p A b S : ℝ) :
    (∫ m, ((A+b*S*Real.exp (γ*m))^(-p)-A^(-p)) ∂brownianMaximumReferenceLaw ν) =
      ∫ w, ((A+b*S*w)^(-p)-A^(-p)) ∂paretoMeasure 1 (2*ν/γ) := by
  have hf : Measurable (fun w : ℝ => (A+b*S*w)^(-p)-A^(-p)) := by fun_prop
  rw [← dual_reference_maximum_exp_pareto_law P hB γ ν hγ hν,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

/-- Fubini transports the independent maximum in the full signed product expectation.
The two integrability bills are explicit so no total-integral fallback enters the passage. -/
theorem dual_maximum_product_increment_eq_pareto
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (W : Measure BrownianPath) (hW : IsBrownianReal (fun t p => p t) W)
    (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) (p : ℝ)
    (A b : Ω → ℝ) (S : Λ → ℝ)
    (hInt : Integrable (fun v : Ω × (ℝ × Λ) =>
      (A v.1+b v.1*(Real.exp (γ*v.2.1)*S v.2.2))^(-p)-(A v.1)^(-p))
        (P.prod ((brownianMaximumReferenceLaw ν).prod R)))
    (hPareto : Integrable (fun v : Ω × Λ => ∫ w,
      (A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p) ∂paretoMeasure 1 (2*ν/γ)) (P.prod R)) :
    (∫ v : Ω × (ℝ × Λ),
      (A v.1+b v.1*(Real.exp (γ*v.2.1)*S v.2.2))^(-p)-(A v.1)^(-p)
        ∂P.prod ((brownianMaximumReferenceLaw ν).prod R)) =
    ∫ v : Ω × Λ, (∫ w,
      (A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p) ∂paretoMeasure 1 (2*ν/γ)) ∂P.prod R := by
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  rw [integral_prod _ hInt, integral_prod _ hPareto]
  apply integral_congr_ae
  filter_upwards [hInt.prod_right_ae] with ω hω
  rw [integral_prod_symm _ hω]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [← dual_reference_maximum_increment W hW γ ν hγ hν p (A ω) (b ω) (S v)]
  apply integral_congr_ae
  filter_upwards [] with m
  congr 2
  ring

end DOZZ.Proofs
