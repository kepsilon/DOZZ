/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CirclePotential
public import DOZZ.GFFStructure.CircleCovariance

/-! The equator correction in the vertex increment argument. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- Circle mean of the regular equator pin. -/
noncomputable def equatorCircleMean (z : ℂ) (r : ℝ) : ℝ :=
  ∫ w, Real.log (normPlus w) ∂circleMeasure z r

/-- Change in the regular pin when the logarithmic cutoff increases by one. -/
noncomputable def equatorCircleDelta (z : ℂ) (r : ℝ) : ℝ :=
  equatorCircleMean z (r + 1) - equatorCircleMean z r

/-- The concentric covariance retains both equator circle means. -/
theorem circle_covariance_concentric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (r s : ℝ) :
    covariance (fun ω => Xc ω z r) (fun ω => Xc ω z s) P =
      min r s + equatorCircleMean z r + equatorCircleMean z s := by
  rw [circleAverage_covariance P X Xc hX hc]
  simp only [sub_self, nnnorm_zero, circleLogPotential_concentric, neg_neg]
  simp only [equatorCircleMean, integral_log_normPlus_circleMeasure_eq_closed]



/-- Separated circle covariances consist of the logarithmic interaction and the two regular pins. -/
theorem circle_covariance_separated
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (r s : ℝ) (hsep : Real.exp (-r) + Real.exp (-s) ≤ ‖x - y‖) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P =
      -Real.log ‖x - y‖ + equatorCircleMean x r + equatorCircleMean y s := by
  rw [circleAverage_covariance P X Xc hX hc,
    circleLogPotential_of_radii_le_distance _ _ hsep]
  simp only [equatorCircleMean, integral_log_normPlus_circleMeasure_eq_closed,
    coe_nnnorm]

/-- A finite increment has the same regular-pin covariance with every separated old vertex. -/
theorem circle_increment_separated_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (r s : ℝ) (hsep : Real.exp (-r) + Real.exp (-s) ≤ ‖x - y‖) :
    covariance (fun ω => Xc ω x (r + 1) - Xc ω x r) (fun ω => Xc ω y s) P =
      equatorCircleDelta x r := by
  let := hX.1
  have hs := covariance_fun_sub_left (hc.2.1 x (r + 1)) (hc.2.1 x r) (hc.2.1 y s)
  have hsep' : Real.exp (-(r + 1)) + Real.exp (-s) ≤ ‖x - y‖ :=
    by linarith [exp_neg_add_le_exp_neg (r₀ := r) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hs, circle_covariance_separated P X Xc hX hc x y (r + 1) s hsep',
    circle_covariance_separated P X Xc hX hc x y r s hsep]
  unfold equatorCircleDelta
  ring


end DOZZ.Proofs
