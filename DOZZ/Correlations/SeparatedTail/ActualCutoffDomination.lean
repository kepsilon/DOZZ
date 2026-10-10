/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.DirichletMoment
public import DOZZ.Correlations.SeparatedTail.WickDomination

/-! The domination step of `DOZZ.separatedSingularMass_joint_tail` applied to the literal equator
weighted cutoff mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The circle split and Green covariance in the exterior-pinned Markov theorem
`DOZZ.exists_exteriorPinned_markov_uniform` supply the actual weighted-cutoff comparison, with
its correlated scalar retained. -/
theorem separatedTail_actual_cutoff_mass_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (Dc H : Ω → ℂ → ℝ) (L : Ω → ℝ) (c : ℂ) (R δ γ α : ℝ)
    (hR : 1 < R) (hpin : ‖c‖+5/4 ≤ R) (hδ : 0 < δ) (hδ4 : δ < 1/4) (hγ : 0 < γ)
    (hfield : IsCenteredGaussianField P (fun ω x => Dc ω (separatedTail_diskPoint c x)))
    (hH : Measurable (fun q : Ω × ℂ => H q.1 q.2)) (hL : Measurable L)
    (hsplit : ∀ x ∈ ball c 1, (fun ω => Xc ω x (Real.log (1/δ))) =ᵐ[P]
      fun ω => Dc ω x+H ω x-L ω)
    (hDc : ∀ x y, ‖x-c‖+δ < 5/4 → ‖y-c‖+δ < 5/4 →
      (∫ ω, Dc ω x*Dc ω y ∂P) =
        ∫ v, ∫ w, diskGreenKernel c (5/4) (by norm_num) v w
          ∂circleMeasure y (Real.log (1/δ)) ∂circleMeasure x (Real.log (1/δ))) :
    ∀ᵐ ω ∂P, cutoffWeightedGmcBallMass P Xc γ α c 1 δ ω ≤
      ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2))*separatedTail_harmonicEnvelope c H L γ ω *
        fieldChaosMass P (fun ω x => Dc ω (separatedTail_diskPoint c x))
          (gmcReferenceMeasure.restrict (ball c 1)) (separatedTail_softWeight γ α δ c) γ ω := by
  let _ : IsProbabilityMeasure P := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let ν := gmcReferenceMeasure.restrict (ball c 1)
  have hscale : Real.exp (-Real.log (1/δ)) = δ := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hs : ∀ᵐ x ∂ν, (fun ω => Xc ω x (Real.log (1/δ))) =ᵐ[P]
      fun ω => Dc ω (separatedTail_diskPoint c x)+H ω x-L ω := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    simpa only [separatedTail_diskPoint, ite_eq_left hx] using hsplit x hx
  have hcommon := separatedTail_circle_split_ae_sample P ν _ _ H L hfield.1 (hc.1 _) hH hL hs
  have hv : ∀ᵐ x ∂ν, |(∫ ω, Xc ω x (Real.log (1/δ))^2 ∂P)-
      (∫ ω, Dc ω (separatedTail_diskPoint c x)^2 ∂P)| ≤ 4+2*R := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    have hn : ‖x-c‖ ≤ 1 := (mem_ball_iff_norm.mp hx).le
    have hh := separatedTail_circle_covariance_discrepancy P X hX Xc hc
      (fun ω x _ => Dc ω x) c R (Real.log (1/δ)) hR hpin
      (by simpa only [hscale] using hDc) x x hn hn (by simpa only [hscale] using hδ4)
    simpa only [separatedTail_diskPoint, ite_eq_left hx, pow_two] using hh
  have henv : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      ENNReal.ofReal (Real.exp (γ*(H ω x-L ω))) ≤ separatedTail_harmonicEnvelope c H L γ ω :=
    ae_of_all P fun ω => (ae_restrict_mem isOpen_ball.measurableSet).mono fun x hx =>
      separatedTail_exp_harmonic_sub_le_envelope c H L γ hγ.le ω x (ball_subset_closedBall hx)
  have h := separatedTail_fieldChaosMass_le_of_circle_split P ν _ _ H L
    (separatedTail_harmonicEnvelope c H L γ) (separatedTail_softWeight γ α δ c)
    (separatedTail_softWeight_measurable γ α δ c) hfield γ (4+2*R) hcommon hv henv
  have heq (ω : Ω) : fieldChaosMass P (fun ω x => Xc ω x (Real.log (1/δ))) ν
      (separatedTail_softWeight γ α δ c) γ ω = cutoffWeightedGmcBallMass P Xc γ α c 1 δ ω := by
    rw [← regularizedGMC_weighted_eq_fieldChaosMass P X hX Xc hc γ _ _
      isOpen_ball.measurableSet _ (separatedTail_softWeight_measurable γ α δ c)]
    rfl
  simpa only [heq] using h

end DOZZ.Proofs
