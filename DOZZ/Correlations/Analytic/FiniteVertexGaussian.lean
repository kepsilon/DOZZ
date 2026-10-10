/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.CircleAverageGaussian

/-! Finite-dimensional Gaussian laws for the vertex coordinates. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- A finite collection of circle-average vertex coordinates has a Gaussian vector law. -/
theorem circle_vertex_hasGaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (r : Fin N → ℝ) :
    HasGaussianLaw (fun ω i => Xc ω (z i) (r i)) P := by
  have hp := (circleAverage_isGaussianProcess P X Xc hX hXc).1
  have hparam : IsGaussianProcess (fun i : Fin N => fun ω => Xc ω (z i) (r i)) P := by
    simpa only [Function.comp_def] using hp.comp_right (fun i => (z i, r i))
  apply hasGaussianLaw_pi_of_linearCombinations (fun i ω => Xc ω (z i) (r i))
  · exact fun i => hparam.aemeasurable i
  · intro a
    have hscaled := hparam.smul a
    simpa only [smul_eq_mul] using hscaled.hasGaussianLaw_fun_sum (I := Finset.univ)

end DOZZ.Proofs
