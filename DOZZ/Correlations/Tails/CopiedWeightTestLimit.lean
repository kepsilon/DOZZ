/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ActualPinTestLimit
public import DOZZ.Correlations.Tails.BoundedPinCoefficient
public import DOZZ.Correlations.Tails.TranslatedField

/-! The literal copied local pin weight in the actual translated GMC cutoff limit. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The compact-test cutoff limit retains the literal local regression coefficient. -/
theorem copied_pin_weight_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (Y : Ω → Distr) (Yc : Ω → ℂ → ℝ → ℝ)
    (hY : IsEquatorGFF P Y) (hYc : IsCircleAverage P Y Yc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P Y γ N)
    (z : ℂ) (hz : 2 ≤ ‖z‖)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfs : tsupport (f : ℂ → ℝ) ⊆ Metric.closedBall 0 1) :
    TendstoInMeasure (P.prod P)
      (fun (n : ℕ) q => ∫ x, f x * Real.exp (γ * localPinCoefficient z x *
        (Xc q.2 z 0-Xc q.1 z 0)) ∂regularizedGMC P Yc γ n q.1)
      atTop (fun q => ∫ x, f x * Real.exp (γ * localPinCoefficient z x *
        (Xc q.2 z 0-Xc q.1 z 0)) ∂N q.1) := by
  let cγ : BoundedContinuousFunction ℂ ℝ := γ • boundedPinCoefficient z
  have hfun (t : ℝ) (x : ℂ) : f x * Real.exp (cγ x*t) =
      f x * Real.exp (γ * localPinCoefficient z x * t) := by
    by_cases hx : f x = 0
    · simp only [hx, zero_mul]
    · have hs : x ∈ Metric.closedBall (0 : ℂ) 1 :=
        hfs (subset_tsupport _ (Function.mem_support.mpr hx))
      have hn : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hs
      change f x * Real.exp ((γ * boundedPinCoefficient z x)*t) = _
      rw [bounded_pin_coefficient_eq z x hz hn]
  have h := actual_copied_pin_test_limit P X Xc hX hc Y Yc hY hYc γ hγ hγ2 N hN
    z hz f cγ hfc
  simpa only [hfun] using h

/-- Specialization to the actual translated and re-pinned source GMC, with its literal
circle averages `Xc(z+x,r)-Xc(z,0)`. -/
theorem translated_copied_pin_weight_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (z : ℂ) (hz : 2 ≤ ‖z‖)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfs : tsupport (f : ℂ → ℝ) ⊆ Metric.closedBall 0 1) :
    TendstoInMeasure (P.prod P)
      (fun (n : ℕ) q => ∫ x, f x * Real.exp (γ * localPinCoefficient z x *
        (Xc q.2 z 0-Xc q.1 z 0)) ∂regularizedGMC P
          (fun ω x r => Xc ω (z+x) r-Xc ω z 0) γ n q.1)
      atTop (fun q => ∫ x, f x * Real.exp (γ * localPinCoefficient z x *
        (Xc q.2 z 0-Xc q.1 z 0)) ∂N q.1) :=
  copied_pin_weight_test_limit P X Xc hX hc
    (translatedField X Xc z) (fun ω x r => Xc ω (z+x) r-Xc ω z 0)
      (translated_field_isEquatorGFF P X Xc hX hc z)
      (translated_field_circleAverage P X Xc hX hc z) γ hγ hγ2 N hN z hz f hfc hfs


end DOZZ.Proofs
