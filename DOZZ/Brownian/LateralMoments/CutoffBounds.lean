/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.ArbitraryCenter
public import DOZZ.GMC.Annulus.BallCover

/-! Cutoff-uniform moments on bounded sets retaining one nonempty disk. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- A finite small-disk cover gives positive cutoff moments; retaining one small disk
instead gives every negative cutoff moment. The estimate uses one fixed charge. -/
theorem latmom_cutoff_bounded_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (g : ℝ) (hg : 0 < g) (hg2 : g < 2)
    (O : Set ℂ) (hO : Bornology.IsBounded O)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1/8)
    (hball : Metric.ball c ρ ⊆ O) (p : ℝ) (hp : p < 4 / g ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
      gmcMassMoment P (regularizedGMC P Xc g r) O p ≤ C := by
  classical
  by_cases hp0 : 0 ≤ p
  · obtain ⟨t, _, htfin, hcover⟩ := finite_cover_balls_of_compact hO.isCompact_closure
      (by norm_num : (0 : ℝ) < 1/16)
    let S := htfin.toFinset
    have hOS : O ⊆ ⋃ x ∈ S, Metric.ball x (1/16) := by
      intro x hx
      simpa only [S, Finite.mem_toFinset] using hcover (subset_closure hx)
    have hSne : S.Nonempty := by
      have hc : c ∈ O := hball (Metric.mem_ball_self hρ)
      have hcS := hOS hc
      simp only [mem_iUnion] at hcS
      obtain ⟨z, hzS, _⟩ := hcS
      exact ⟨z, hzS⟩
    have hex : ∀ z : ℂ, ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
        gmcMassMoment P (regularizedGMC P Xc g r) (Metric.ball z (1/16)) p ≤ K :=
      fun z => regularizedGMC_ball_moment_uniform_any_center
        P X hX Xc hXc g hg hg2 z (1/16) (by norm_num) (by norm_num) p hp
    choose K hK hKb using hex
    refine ⟨(S.card : ℝ≥0∞)^p * ∑ z ∈ S, K z,
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0 (ENNReal.natCast_ne_top _))
        (ENNReal.sum_lt_top.mpr (fun z _ => hK z)), ?_⟩
    intro r hr
    have hm (z : ℂ) : AEMeasurable
        (fun ω => regularizedGMC P Xc g r ω (Metric.ball z (1/16)) ^ p) P :=
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc g r)).aemeasurable.pow_const p
    have hpoint (ω : Ω) : regularizedGMC P Xc g r ω O ^ p ≤
        (S.card : ℝ≥0∞)^p * ∑ z ∈ S, regularizedGMC P Xc g r ω (Metric.ball z (1/16))^p := by
      calc
        _ ≤ (∑ z ∈ S, regularizedGMC P Xc g r ω (Metric.ball z (1/16)))^p :=
          ENNReal.rpow_le_rpow ((measure_mono hOS).trans (measure_biUnion_finset_le _ _)) hp0
        _ ≤ _ := ennreal_finset_sum_rpow_le_card_rpow_sum S hSne _ p hp0
    calc
      _ ≤ ∫⁻ ω, (S.card : ℝ≥0∞)^p *
          ∑ z ∈ S, regularizedGMC P Xc g r ω (Metric.ball z (1/16))^p ∂P :=
        lintegral_mono hpoint
      _ = (S.card : ℝ≥0∞)^p * ∑ z ∈ S,
          gmcMassMoment P (regularizedGMC P Xc g r) (Metric.ball z (1/16)) p := by
        rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum S (fun z _ => hm z)),
          lintegral_finsetSum' S (fun z _ => hm z)]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => hKb z r hr)) (by positivity)
  · obtain ⟨C, hC, hCb⟩ := regularizedGMC_ball_moment_uniform_any_center
      P X hX Xc hXc g hg hg2 c ρ hρ hρ8 p hp
    refine ⟨C, hC, fun r hr => le_trans ?_ (hCb r hr)⟩
    apply lintegral_mono
    intro ω
    change (regularizedGMC P Xc g r ω O)^p ≤
      (regularizedGMC P Xc g r ω (Metric.ball c ρ))^p
    have hh := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
      (show regularizedGMC P Xc g r ω (Metric.ball c ρ) ≤ regularizedGMC P Xc g r ω O from
        measure_mono hball) (neg_nonneg.mpr (lt_of_not_ge hp0).le))
    simpa only [← ENNReal.rpow_neg, neg_neg] using hh

end DOZZ.Proofs
end
