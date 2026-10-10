/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency
public import DOZZ.GMC.Moments.InversionLaw
public import DOZZ.GMC.Annulus.BallCover

/-! # Probabilistic pieces of the global extended moment

Limiting chaos has almost surely no atom at any given point, because the moments of order `1/2`
of shrinking disks tend to zero. The power weight at infinity integrated over the exterior of a
disk is the weighted local mass of the inverted measure at the origin, so the inversion law turns
its moments into weighted local moments at the origin. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Every `IsGMCOf` version almost surely has no atom at a given point. -/
theorem gmc_singleton_mass_eq_zero_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (z : ℂ) :
    ∀ᵐ ω ∂P, M ω {z} = 0 := by
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hp4 : (1 / 2 : ℝ) < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  obtain ⟨C, -, hCb⟩ := gmc_ball_moment_sharp_upper_center P X hX γ hγ hγ2 M hM z (1 / 2) hp4
  set ξ : ℝ := 2 * (1 / 2) + γ ^ 2 * (1 / 2) / 2 - γ ^ 2 * (1 / 2) ^ 2 / 2 with hξ
  have hξpos : 0 < ξ := by
    rw [hξ]
    nlinarith
  have hmeas : AEMeasurable (fun ω => M ω {z}) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM {z} (measurableSet_singleton z)
  have hle : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 8 →
      ∫⁻ ω, M ω {z} ^ (1 / 2 : ℝ) ∂P ≤ ENNReal.ofReal (C * ρ ^ ξ) := by
    intro ρ hρ hρ8
    refine le_trans ?_ (hCb ρ hρ hρ8)
    apply lintegral_mono
    intro ω
    exact ENNReal.rpow_le_rpow
      (measure_mono (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hρ))) (by norm_num)
  have htend : Tendsto (fun ρ : ℝ => ENNReal.ofReal (C * ρ ^ ξ)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => C * ρ ^ ξ) (𝓝[>] 0) (𝓝 (C * (0 : ℝ) ^ ξ)) :=
      (((Real.continuousAt_rpow_const 0 ξ (Or.inr hξpos.le)).tendsto).const_mul C).mono_left
        nhdsWithin_le_nhds
    rw [Real.zero_rpow hξpos.ne', mul_zero] at h1
    simpa using ENNReal.tendsto_ofReal h1
  have hzero : ∫⁻ ω, M ω {z} ^ (1 / 2 : ℝ) ∂P = 0 := by
    refine le_antisymm (ge_of_tendsto htend ?_) zero_le
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with ρ hρ
    exact hle ρ hρ.1 hρ.2.le
  have hae := (lintegral_eq_zero_iff' (hmeas.pow_const _)).mp hzero
  filter_upwards [hae] with ω hω
  rcases ENNReal.rpow_eq_zero_iff.mp hω with h | h
  · exact h.1
  · exact absurd h.2 (by norm_num)

/-- Every positive power of a finite sum is bounded by the sum of the powers times a power of the
cardinality. -/
theorem ennreal_finset_sum_rpow_le_card_rpow_sum_of_pos
    {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ≥0∞) ^ p * ∑ i ∈ S, (f i) ^ p := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS, ENNReal.zero_rpow_of_pos hp]
  · exact ennreal_finset_sum_rpow_le_card_rpow_sum S hS f p hp.le

/-- The power weight at infinity, integrated over the exterior of a disk, is bounded by the
weighted local mass of the inverted measure at the origin. -/
theorem exterior_lintegral_le_inversion_weighted (μ : Measure ℂ) (γ αinf : ℝ) {Rr : ℝ}
    (hRr : 0 < Rr) :
    ∫⁻ x in {x : ℂ | Rr < ‖x‖}, ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂μ ≤
      weightedGmcBallMass γ (μ.map (fun x => x⁻¹)) αinf 0 (1 / Rr) := by
  have hE : MeasurableSet {x : ℂ | Rr < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have hB : MeasurableSet (Metric.ball (0 : ℂ) (1 / Rr)) := Metric.isOpen_ball.measurableSet
  set g : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) (1 / Rr)).indicator
    (fun u => ENNReal.rpow (ENNReal.ofReal ‖u - 0‖) (-γ * αinf)) with hg
  have hgm : Measurable g :=
    ((ENNReal.continuous_rpow_const (y := -γ * αinf)).measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.sub_const 0).norm)).indicator hB
  unfold weightedGmcBallMass
  rw [← lintegral_indicator hB, lintegral_map hgm measurable_inv, ← lintegral_indicator hE]
  apply lintegral_mono
  intro x
  by_cases hx : Rr < ‖x‖
  · have hxpos : 0 < ‖x‖ := hRr.trans hx
    have hxinv : x⁻¹ ∈ Metric.ball (0 : ℂ) (1 / Rr) := by
      rw [Metric.mem_ball, dist_zero_right, norm_inv, one_div]
      exact (inv_lt_inv₀ hxpos hRr).mpr hx
    dsimp only
    rw [Set.indicator_of_mem (show x ∈ {x : ℂ | Rr < ‖x‖} from hx), hg,
      Set.indicator_of_mem hxinv, sub_zero, norm_inv, ENNReal.ofReal_inv_of_pos hxpos]
    rw [show -γ * αinf = -(γ * αinf) by ring]
    rw [ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow, ENNReal.rpow_neg, ENNReal.inv_rpow, inv_inv]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℂ | Rr < ‖x‖} from hx)]
    exact zero_le

/-- Positive moments of the exterior power-weight integral are bounded by the weighted local
moment at the origin with the charge at infinity. -/
theorem gmc_exterior_moment_le_weighted
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (αinf : ℝ) {Rr : ℝ} (hRr : 0 < Rr) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ ω, (∫⁻ x in {x : ℂ | Rr < ‖x‖}, ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂M ω) ^ t
        ∂P ≤ weightedGmcBallMoment P M γ αinf 0 (1 / Rr) t := by
  set H : Measure ℂ → ℝ≥0∞ := fun μ =>
    ENNReal.rpow (weightedGmcBallMass γ μ αinf 0 (1 / Rr)) t with hH
  have hB : MeasurableSet (Metric.ball (0 : ℂ) (1 / Rr)) := Metric.isOpen_ball.measurableSet
  have hHm : Measurable H := by
    have hw : Measurable fun μ : Measure ℂ => weightedGmcBallMass γ μ αinf 0 (1 / Rr) := by
      have hf : Measurable ((Metric.ball (0 : ℂ) (1 / Rr)).indicator
          (fun u => ENNReal.rpow (ENNReal.ofReal ‖u - 0‖) (-γ * αinf))) :=
        ((ENNReal.continuous_rpow_const (y := -γ * αinf)).measurable.comp
          (ENNReal.measurable_ofReal.comp (measurable_id.sub_const 0).norm)).indicator hB
      have heq : (fun μ : Measure ℂ => weightedGmcBallMass γ μ αinf 0 (1 / Rr)) = fun μ =>
          ∫⁻ u, (Metric.ball (0 : ℂ) (1 / Rr)).indicator
            (fun u => ENNReal.rpow (ENNReal.ofReal ‖u - 0‖) (-γ * αinf)) u ∂μ := by
        funext μ
        exact (lintegral_indicator hB _).symm
      rw [heq]
      exact Measure.measurable_lintegral hf
    exact (ENNReal.continuous_rpow_const (y := t)).measurable.comp hw
  have hinv := equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM H hHm
  calc ∫⁻ ω, (∫⁻ x in {x : ℂ | Rr < ‖x‖}, ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂M ω) ^ t
        ∂P ≤ ∫⁻ ω, H ((M ω).map (fun x => x⁻¹)) ∂P := by
        apply lintegral_mono
        intro ω
        exact ENNReal.rpow_le_rpow (exterior_lintegral_le_inversion_weighted (M ω) γ αinf hRr) ht
    _ = weightedGmcBallMoment P M γ αinf 0 (1 / Rr) t := hinv

end DOZZ.Proofs
