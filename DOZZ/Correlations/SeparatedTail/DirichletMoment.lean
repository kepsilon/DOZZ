/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.DirichletCutoff
public import DOZZ.Correlations.SeparatedTail.FieldComparison
public import DOZZ.GMC.SharpMoments.LimitWeightedFatou
public import Mathlib.MeasureTheory.Measure.Prod

/-! The Dirichlet moments for the separated joint-tail estimate come from the equator weighted
cutoff bound `DOZZ.equatorGFF_GMC_weighted_cutoff_bound` by finite Kahane. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The softened singular weight is bounded and globally measurable. -/
noncomputable def separatedTail_softWeight (γ α s : ℝ) (c x : ℂ) : ℝ≥0 :=
  ((‖x-c‖+s)^(-γ*α)).toNNReal

theorem separatedTail_softWeight_measurable (γ α s : ℝ) (c : ℂ) :
    Measurable (separatedTail_softWeight γ α s c) :=
  (limitWeightedFatou_weight_measurable (-γ*α) s).comp (measurable_id.sub_const c)

theorem separatedTail_softWeight_bounded (γ α s : ℝ) (c : ℂ) (he : -γ*α ≤ 0) (hs : 0 < s) :
    ∃ b : ℝ≥0, ∀ x, separatedTail_softWeight γ α s c x ≤ b :=
  ⟨(s^(-γ*α)).toNNReal, fun x => limitWeightedFatou_weight_le he hs (x-c)⟩

/-- A Dirichlet circle cutoff moment is bounded by the literal equator cutoff moment.
The same reference density and softened weight are used on both sides. -/
theorem separatedTail_dirichlet_cutoff_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (Dc : Ω → ℂ → ℝ → ℝ) (c : ℂ) (R δ γ α t : ℝ)
    (hR : 1 < R) (hpin : ‖c‖+5/4 ≤ R) (hδ : 0 < δ) (hδ4 : δ < 1/4)
    (he : -γ*α ≤ 0) (ht : 0 < t)
    (hfield : IsCenteredGaussianField P (fun ω x => Dc ω (separatedTail_diskPoint c x) (Real.log (1/δ))))
    (hDc : ∀ x y, ‖x-c‖+δ < 5/4 → ‖y-c‖+δ < 5/4 →
      (∫ ω, Dc ω x (Real.log (1/δ))*Dc ω y (Real.log (1/δ)) ∂P) =
        ∫ v, ∫ w, diskGreenKernel c (5/4) (by norm_num) v w
          ∂circleMeasure y (Real.log (1/δ)) ∂circleMeasure x (Real.log (1/δ))) :
    (∫⁻ ω, fieldChaosMass P (fun ω x => Dc ω (separatedTail_diskPoint c x) (Real.log (1/δ)))
      (gmcReferenceMeasure.restrict (ball c 1)) (separatedTail_softWeight γ α δ c) γ ω ^ t ∂P) ≤
      ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*|t^2-t|)) *
        (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ α c 1 δ ω ^ t ∂P) := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hscale : Real.exp (-Real.log (1/δ)) = δ := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hcomp (x y : ℂ) (hx : x ∈ ball c 1) (hy : y ∈ ball c 1) :
      |(∫ ω, Dc ω (separatedTail_diskPoint c x) (Real.log (1/δ))*
        Dc ω (separatedTail_diskPoint c y) (Real.log (1/δ)) ∂P)-
        (∫ ω, Xc ω x (Real.log (1/δ))*Xc ω y (Real.log (1/δ)) ∂P)| ≤ 4+2*R := by
    simp only [separatedTail_diskPoint, ite_eq_left hx, ite_eq_left hy]
    rw [abs_sub_comm]
    exact separatedTail_circle_covariance_discrepancy P X hX Xc hc Dc c R (Real.log (1/δ)) hR hpin
      (by simpa only [hscale] using hDc) x y (mem_ball_iff_norm.mp hx).le
      (mem_ball_iff_norm.mp hy).le (by simpa only [hscale] using hδ4)
  have hcov : ∀ᵐ xy ∂(gmcReferenceMeasure.restrict (ball c 1)).prod
      (gmcReferenceMeasure.restrict (ball c 1)),
      |(∫ ω, Dc ω (separatedTail_diskPoint c xy.1) (Real.log (1/δ))*
        Dc ω (separatedTail_diskPoint c xy.2) (Real.log (1/δ)) ∂P)-
        (∫ ω, Xc ω xy.1 (Real.log (1/δ))*Xc ω xy.2 (Real.log (1/δ)) ∂P)| ≤ 4+2*R := by
    have hmem : ∀ᵐ xy : ℂ × ℂ ∂(gmcReferenceMeasure.restrict (ball c 1)).prod
        (gmcReferenceMeasure.restrict (ball c 1)), xy.1 ∈ ball c 1 ∧ xy.2 ∈ ball c 1 :=
      (Measure.ae_prod_iff_ae_ae ((isOpen_ball.measurableSet.preimage measurable_fst).inter
        (isOpen_ball.measurableSet.preimage measurable_snd))).mpr
        ((ae_restrict_mem isOpen_ball.measurableSet).mono fun x hx =>
          (ae_restrict_mem isOpen_ball.measurableSet).mono fun y hy => ⟨hx,hy⟩)
    exact hmem.mono fun xy hxy => hcomp xy.1 xy.2 hxy.1 hxy.2
  have hdiag : ∀ᵐ x ∂gmcReferenceMeasure.restrict (ball c 1),
      |(∫ ω, Dc ω (separatedTail_diskPoint c x) (Real.log (1/δ))^2 ∂P)-
        (∫ ω, Xc ω x (Real.log (1/δ))^2 ∂P)| ≤ 4+2*R := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    simpa only [pow_two] using hcomp x x hx hx
  have hb := separatedTail_fieldChaosMoment_le_of_covariance_discrepancy P P _ _ hfield
    (circleAverage_isCenteredGaussianField P X hX Xc hc _)
    (gmcReferenceMeasure.restrict (ball c 1)) (separatedTail_softWeight γ α δ c)
    (separatedTail_softWeight_measurable γ α δ c) (separatedTail_softWeight_bounded γ α δ c he hδ)
    γ (4+2*R) t (by linarith) ht hcov hdiag
  have heq (ω : Ω) : fieldChaosMass P (fun ω x => Xc ω x (Real.log (1/δ)))
      (gmcReferenceMeasure.restrict (ball c 1)) (separatedTail_softWeight γ α δ c) γ ω =
      cutoffWeightedGmcBallMass P Xc γ α c 1 δ ω := by
    rw [← regularizedGMC_weighted_eq_fieldChaosMass P X hX Xc hc γ _ _
      isOpen_ball.measurableSet _ (separatedTail_softWeight_measurable γ α δ c)]
    rfl
  simpa only [heq] using hb

end DOZZ.Proofs
