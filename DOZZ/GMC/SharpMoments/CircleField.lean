/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
public import DOZZ.Statements.GMC.IsCenteredGaussianField
public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.Annulus.PositiveRoot

/-! # The circle-average field at a fixed radius as a Gaussian field

At each radius the circle average is a jointly measurable centered Gaussian field on the plane,
and every cutoff chaos mass is the corresponding continuum Wick mass against the reference
measure. Its covariance is the double circle average of the equator kernel, which on a bounded
chart is `log (1 / max ‖x - y‖ e^{-r})` up to a uniform constant, and which is nonnegative as soon
as the two circles stay within unit distance. These are the inputs for every Kahane comparison
of cutoff chaoses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

open CirclePotential

/-- The circle average at a fixed radius is a jointly measurable centered Gaussian field. -/
theorem circleAverage_isCenteredGaussianField
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) :
    IsCenteredGaussianField P (fun ω x => Xc ω x r) :=
  ⟨hXc.1 r, fun _ x => circleAverage_finite_family_jointly_gaussian P X hX Xc hXc
    (fun i => (x i, r))⟩

/-- A cutoff chaos mass on a measurable set is the continuum Wick mass of the circle field
against the restricted reference measure. -/
theorem regularizedGMC_apply_eq_fieldChaosMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (ω : Ω) :
    regularizedGMC P Xc γ r ω A =
      fieldChaosMass P (fun ω x => Xc ω x r) (gmcReferenceMeasure.restrict A)
        (fun _ => 1) γ ω := by
  let _ := hX.1
  rw [regularizedGMC_mass_eq_wick_lintegral P X Xc hXc γ r A hA ω, fieldChaosMass]
  apply lintegral_congr
  intro x
  simp [gmcCircleWickDensity]

/-- A weighted cutoff chaos mass on a measurable set is the continuum Wick mass of the circle
field with that weight against the restricted reference measure. -/
theorem regularizedGMC_weighted_eq_fieldChaosMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (w : ℂ → ℝ≥0) (hw : Measurable w) (ω : Ω) :
    (∫⁻ x in A, (w x : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) =
      fieldChaosMass P (fun ω x => Xc ω x r) (gmcReferenceMeasure.restrict A) w γ ω := by
  let _ := hX.1
  have hW : Measurable (gmcCircleWickDensity P Xc γ r ω) :=
    (measurable_gmcCircleWickDensity P X Xc hXc γ r).comp
      (measurable_const.prodMk measurable_id)
  rw [regularizedGMC_eq_reference_withDensity_PositiveRoot P X Xc hXc γ r ω, restrict_withDensity hA,
    lintegral_withDensity_eq_lintegral_mul _ hW (by fun_prop), fieldChaosMass]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, gmcCircleWickDensity]
  exact mul_comm _ _

/-- The covariance of two circle averages at a common radius is the double circle average of
the equator kernel. -/
theorem circleField_covariance_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (x y : ℂ) (r : ℝ) :
    ∫ ω, Xc ω x r * Xc ω y r ∂P = circleKernel x r y r :=
  isCircleAverage_covariance P X hX Xc hXc x y r r

/-- On a bounded chart the circle covariance is at most `log (1 / max ‖x - y‖ e^{-r})` plus the
uniform chart remainder. -/
theorem circleField_covariance_le_log
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (x y : ℂ) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ∫ ω, Xc ω x r * Xc ω y r ∂P ≤
      Real.log (1 / max ‖x - y‖ (Real.exp (-r))) + (Real.log 3 + 2 * Real.log (1 + R)) := by
  rw [circleField_covariance_eq P X hX Xc hXc x y r]
  have h := abs_circleKernel_sub_log_le R hR x y hx hy r r hr hr
  rw [max_self] at h
  linarith [(abs_le.mp h).2]

/-- On a bounded chart the circle covariance is at least `log (1 / max ‖x - y‖ e^{-r})` minus the
uniform chart remainder. -/
theorem circleField_covariance_ge_log
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (x y : ℂ) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    Real.log (1 / max ‖x - y‖ (Real.exp (-r))) - (Real.log 3 + 2 * Real.log (1 + R)) ≤
      ∫ ω, Xc ω x r * Xc ω y r ∂P := by
  rw [circleField_covariance_eq P X hX Xc hXc x y r]
  have h := abs_circleKernel_sub_log_le R hR x y hx hy r r hr hr
  rw [max_self] at h
  linarith [(abs_le.mp h).1]

/-- Circle covariances are nonnegative as soon as the two circles stay within unit distance. -/
theorem circleField_covariance_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (x y : ℂ) (r : ℝ)
    (hclose : ‖x - y‖ + 2 * Real.exp (-r) ≤ 1) :
    0 ≤ ∫ ω, Xc ω x r * Xc ω y r ∂P := by
  rw [circleField_covariance_eq P X hX Xc hXc x y r, circleKernel_eq]
  have ha : 0 < Real.exp (-r) := Real.exp_pos _
  have hreg : 0 ≤ regAvg y r := by
    unfold regAvg
    have hI : CircleIntegrable (fun v => Real.log (normPlus v)) y (Real.exp (-r)) :=
      continuous_log_normPlus.continuousOn.circleIntegrable'
    have := Real.circleAverage_mono (circleIntegrable_const 0 y (Real.exp (-r))) hI
      (fun v _ => log_normPlus_nonneg v)
    rwa [Real.circleAverage_const] at this
  have hpoint : ∀ u ∈ Metric.sphere x |Real.exp (-r)|, 0 ≤ innerPot y r u := by
    intro u hu
    rw [mem_sphere_iff_norm, abs_of_pos ha] at hu
    have huy : ‖u - y‖ ≤ 1 := by
      have := norm_sub_le_norm_sub_add_norm_sub u x y
      linarith
    have hmax : max ‖u - y‖ (Real.exp (-r)) ≤ 1 :=
      max_le huy (by linarith [norm_nonneg (x - y)])
    have hlog : Real.log (max ‖u - y‖ (Real.exp (-r))) ≤ 0 :=
      Real.log_nonpos (le_max_of_le_right ha.le) hmax
    unfold innerPot
    linarith [log_normPlus_nonneg u]
  have hI : CircleIntegrable (innerPot y r) x (Real.exp (-r)) :=
    (continuous_innerPot y r).continuousOn.circleIntegrable'
  have := Real.circleAverage_mono (circleIntegrable_const 0 x (Real.exp (-r))) hI hpoint
  rwa [Real.circleAverage_const] at this

end DOZZ.Proofs
