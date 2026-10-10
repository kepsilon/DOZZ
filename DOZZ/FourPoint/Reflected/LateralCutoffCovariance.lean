/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.LateralSeparation
public import DOZZ.Brownian.Lateral.CircleRegularization
import Mathlib.Tactic

/-! # Actual lateral cutoff covariances on separated charts

This identifies the off-diagonal limit with the literal plane lateral kernel,
then makes the identification uniform on compact sets. It is the finite-cutoff
input to the conditional Kahane comparison.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace DOZZ.Proofs

/-- The radial point kernel on a lateral chart is the actual unclamped origin covariance. -/
theorem reflected_clamped_point_covariance_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x y : ℂ)
    (hx : x ∈ originLateralChart ρ) (hy : y ∈ originLateralChart ρ) :
    clampedRadialPointCovariance hc ρ x y = originRadialCovariance (-Real.log ‖x‖) y := by
  change 2 * ρ < ‖x‖ at hx
  change 2 * ρ < ‖y‖ at hy
  unfold clampedRadialPointCovariance
  rw [clampedLogRadius_eq ρ x (by linarith only [hx, hρ]),
    clampedLogRadius_eq ρ y (by linarith only [hy, hρ]),
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _)]
  exact origin_circle_radial_covariance X Xc hX hc _ y

/-- Actual finite cutoff covariances tend uniformly to the lateral plane kernel off diagonal. -/
theorem reflected_lateral_cutoff_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) (s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ ε ε', 0 < ε → ε ≤ min d ρ →
      0 < ε' → ε' ≤ min d ρ → ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
      |gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
          (fun ω => originLateralCircleRegularization Xc ρ ω ε' y) -
        (gffKernel x y - originRadialCovariance (-Real.log ‖x‖) y)| < η := by
  obtain ⟨δ, hδ, hR⟩ := originCircleRadialL2_uniform_mixed_covariance_approx
    P X Xc hX hc ρ hρ K hK (η / 2) (half_pos hη)
  let d := min δ (min (s / 4) (η / 4))
  have hd : 0 < d := lt_min hδ (lt_min (by positivity) (by positivity))
  refine ⟨d, hd, ?_⟩
  intro ε ε' hε hεd hε' hε'd x hx y hy hxy
  have hdδ : d ≤ δ := min_le_left _ _
  have hds : d ≤ s / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdη : d ≤ η / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hεδ : ε ≤ min δ ρ := le_min
    ((hεd.trans (min_le_left _ _)).trans hdδ) (hεd.trans (min_le_right _ _))
  have hε'δ : ε' ≤ min δ ρ := le_min
    ((hε'd.trans (min_le_left _ _)).trans hdδ) (hε'd.trans (min_le_right _ _))
  have hεs : ε ≤ s / 4 := (hεd.trans (min_le_left _ _)).trans hds
  have hε's : ε' ≤ s / 4 := (hε'd.trans (min_le_left _ _)).trans hds
  have hεη : ε ≤ η / 4 := (hεd.trans (min_le_left _ _)).trans hdη
  have hε'η : ε' ≤ η / 4 := (hε'd.trans (min_le_left _ _)).trans hdη
  have hrad := hR ε ε' hε hεδ hε' hε'δ x hx y hy
  have hcircle := abs_circleKernel_sub_gffKernel_le x y (Real.log (1 / ε)) (Real.log (1 / ε')) (by
    rw [exp_neg_log_one_div hε, exp_neg_log_one_div hε']
    linarith only [hεs, hε's, hs, hxy])
  rw [exp_neg_log_one_div hε, exp_neg_log_one_div hε'] at hcircle
  rw [originLateralCircleRegularization_gaussianCovariance P X Xc hX hc hm ρ hρ,
    originCircleLateralL2_covariance_expansion P X Xc hX hc ρ ρ hρ hρ x y _ _
      (originLateralChart_cutoff_lower ρ ε x (hKU hx) hε (hεd.trans (min_le_right _ _)))
      (originLateralChart_cutoff_lower ρ ε' y (hKU hy) hε' (hε'd.trans (min_le_right _ _))),
    ← gaussianCovariance_circleL2_eq P X Xc hX hc,
    isCircleAverage_covariance P X hX Xc hc]
  rw [reflected_clamped_point_covariance_eq P X Xc hX hc ρ hρ x y (hKU hx) (hKU hy)] at hrad
  have halg : ∀ A B C D : ℝ, (A - B) - (C - D) = (A - C) - (B - D) := by
    intros; ring
  rw [halg]
  have habs := abs_sub
    (circleKernel x (Real.log (1 / ε)) y (Real.log (1 / ε')) - gffKernel x y)
    (covariance (originCircleRadialL2 hc ρ x (Real.log (1 / ε)))
      (originCircleRadialL2 hc ρ y (Real.log (1 / ε'))) P -
        originRadialCovariance (-Real.log ‖x‖) y)
  exact (habs.trans_lt (add_lt_add_of_le_of_lt hcircle hrad)).trans_le
    (by linarith only [hεη, hε'η])

/-- The actual cutoff cross-covariance bound is the radius ratio plus an arbitrary cutoff error. -/
theorem reflected_lateral_cutoff_cross_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) (R s η : ℝ) (hR : R ≤ 1 / 2)
    (hs : 0 < s) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ ε ε', 0 < ε → ε ≤ min d ρ →
      0 < ε' → ε' ≤ min d ρ → ∀ x ∈ K, ∀ y ∈ K,
      s ≤ ‖x - y‖ → ‖y‖ ≤ R * ‖x‖ →
      |gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
        (fun ω => originLateralCircleRegularization Xc ρ ω ε' y)| ≤ 2 * R + η := by
  obtain ⟨d, hd, hb⟩ := reflected_lateral_cutoff_uniform P X Xc hX hc hm ρ hρ K hK hKU s η hs hη
  refine ⟨d, hd, ?_⟩
  intro ε ε' hε hεd hε' hε'd x hx y hy hxy hrelative
  have hlimit := hb ε ε' hε hεd hε' hε'd x hx y hy hxy
  have hkernel := reflected_lateral_cross_bound_relative x y R
    (originLateralChart_ne_zero ρ hρ x (hKU hx))
    (originLateralChart_ne_zero ρ hρ y (hKU hy)) hR hrelative
  have htri := abs_sub_le
    (gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
      (fun ω => originLateralCircleRegularization Xc ρ ω ε' y))
    (gffKernel x y - originRadialCovariance (-Real.log ‖x‖) y) 0
  simp only [sub_zero] at htri
  simpa only [add_comm] using
    (htri.trans (add_le_add hlimit.le hkernel))

end DOZZ.Proofs
