/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffConvergence
public import DOZZ.GMC.SharpMoments.MomentConvergence
public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass

/-! # Weighted local moments of limiting chaos from cutoff weighted bounds

A uniform bound on the moments of the cutoff weighted masses `cutoffWeightedGmcBallMass` bounds
the weighted local moment of the limiting chaos. For a fixed softening `s > 0` of the distance
weight the weight is bounded, so the weighted cutoff masses converge in probability along the
integer cutoffs and Fatou in probability transfers the bound once `exp (-n) ≤ s`. As the softening
vanishes, the softened weighted masses increase to the weighted local mass, and monotone
convergence removes the softening. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Along the integer cutoffs, `Real.exp (-n)` is eventually below any positive threshold. -/
theorem limitWeightedFatou_exists_nat_exp_neg_le {s : ℝ} (hs : 0 < s) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Real.exp (-(n : ℝ)) ≤ s := by
  have h : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (h.eventually (ge_mem_nhds hs))

/-- A larger softening gives a smaller softened distance weight when the exponent is
nonpositive. -/
theorem limitWeightedFatou_ofReal_rpow_le {a s s' e : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (hss : s ≤ s') (he : e ≤ 0) :
    ENNReal.ofReal ((a + s') ^ e) ≤ ENNReal.ofReal ((a + s) ^ e) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) he)

/-- The softened distance weight is a measurable function of the displacement. -/
theorem limitWeightedFatou_weight_measurable (e s : ℝ) :
    Measurable fun y : ℂ => ((‖y‖ + s) ^ e).toNNReal :=
  measurable_real_toNNReal.comp ((measurable_norm.add_const s).pow_const e)

/-- The softened distance weight with a nonpositive exponent is bounded by its value at the
origin. -/
theorem limitWeightedFatou_weight_le {e s : ℝ} (he : e ≤ 0) (hs : 0 < s) (y : ℂ) :
    ((‖y‖ + s) ^ e).toNNReal ≤ (s ^ e).toNNReal :=
  Real.toNNReal_le_toNNReal
    (Real.rpow_le_rpow_of_nonpos hs (by linarith [norm_nonneg y]) he)

/-- The softened distance weight, shifted to the center `z`, is a measurable extended
nonnegative function. -/
theorem limitWeightedFatou_ofReal_weight_measurable (z : ℂ) (e s : ℝ) :
    Measurable fun x : ℂ => ENNReal.ofReal ((‖x - z‖ + s) ^ e) :=
  ENNReal.measurable_ofReal.comp (((measurable_id.sub_const z).norm.add_const s).pow_const e)

/-- Fatou in probability for boundedly weighted cutoff masses: a bound on the `t`th moments of
the cutoff masses for all large integer cutoffs bounds the `t`th moment of the limit. -/
theorem limitWeightedFatou_bounded_weight_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : ℂ) (ρ : ℝ) (w : ℂ → ℝ≥0) (hw : Measurable w) (c : ℝ≥0) (hwc : ∀ y, w y ≤ c)
    (t : ℝ) (C : ℝ≥0∞) (n₀ : ℕ)
    (hbound : ∀ n : ℕ, n₀ ≤ n →
      ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω) ^ t ∂P
        ≤ C) :
    ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂M ω) ^ t ∂P ≤ C := by
  have hB : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
  have hwm : Measurable fun x : ℂ => (w (x - z) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_id.sub_const z))
  refine momentConv_lintegral_rpow_limit_le P
    (fun (n : ℕ) ω => ∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞)
      ∂regularizedGMC P Xc γ ((n + n₀ : ℕ) : ℝ) ω)
    (fun ω => ∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂M ω)
    (fun n => ?_) (fun n => ?_) ?_
    ((regularizedGMC_weighted_mass_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc z ρ w hw c
      hwc).comp (tendsto_add_atTop_nat n₀))
    t C (fun n => hbound _ (Nat.le_add_left n₀ n))
  · have hm : Measurable fun ω => ∫⁻ x, (Metric.ball z ρ).indicator
        (fun x => (w (x - z) : ℝ≥0∞)) x ∂regularizedGMC P Xc γ ((n + n₀ : ℕ) : ℝ) ω :=
      (Measure.measurable_lintegral (hwm.indicator hB)).comp
        (regularizedGMC_measurable P X hX Xc hXc γ _)
    refine hm.aemeasurable.congr (Eventually.of_forall fun ω => ?_)
    simp only [lintegral_indicator hB]
  · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ ((n + n₀ : ℕ) : ℝ)] with ω hω
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (weightedSetLIntegral_le_const_mul _ z ρ w c hwc)
  · refine Eventually.of_forall fun ω => ?_
    have := hM.1 ω
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (weightedSetLIntegral_le_const_mul _ z ρ w c hwc)

/-- Fatou in probability for a fixed softening `s` of the distance weight: the cutoff weighted
bounds at cutoffs `δ ≤ s` bound the `t`th moment of the softened weighted mass of the limit. -/
theorem limitWeightedFatou_softened_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α : ℝ) (hα : 0 ≤ α) (z : ℂ) (ρ : ℝ) (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0∞)
    (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ)
    (hC : ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      ∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z ρ δ ω) t ∂P ≤ C) :
    ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, ENNReal.ofReal ((‖x - z‖ + s) ^ (-γ * α)) ∂M ω) ^ t ∂P
      ≤ C := by
  have he : -γ * α ≤ 0 := by linarith [mul_nonneg hγ.le hα]
  obtain ⟨n₀, hn₀⟩ := limitWeightedFatou_exists_nat_exp_neg_le hs
  refine limitWeightedFatou_bounded_weight_moment_le P X hX γ hγ hγ2 M hM Xc hXc z ρ
    (fun y => ((‖y‖ + s) ^ (-γ * α)).toNNReal) (limitWeightedFatou_weight_measurable _ _)
    ((s ^ (-γ * α)).toNNReal) (fun y => limitWeightedFatou_weight_le he hs y) t C n₀ ?_
  intro n hn
  have hδ : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hδs : Real.exp (-(n : ℝ)) ≤ s := hn₀ n hn
  have hlog : Real.log (1 / Real.exp (-(n : ℝ))) = (n : ℝ) := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  refine le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ ht) (hC _ hδ (hδs.trans hsρ))
  unfold cutoffWeightedGmcBallMass
  rw [hlog]
  exact lintegral_mono fun x => limitWeightedFatou_ofReal_rpow_le (norm_nonneg _) hδ hδs he

/-- The softened weighted disk mass decreases as the softening increases when the exponent is
nonpositive. -/
theorem limitWeightedFatou_mass_mono (μ : Measure ℂ) (z : ℂ) (ρ e : ℝ) (he : e ≤ 0) {s s' : ℝ}
    (hs : 0 < s) (hss : s ≤ s') :
    ∫⁻ x in Metric.ball z ρ, ENNReal.ofReal ((‖x - z‖ + s') ^ e) ∂μ ≤
      ∫⁻ x in Metric.ball z ρ, ENNReal.ofReal ((‖x - z‖ + s) ^ e) ∂μ :=
  lintegral_mono fun _ => limitWeightedFatou_ofReal_rpow_le (norm_nonneg _) hs hss he

/-- As the softening vanishes through positive values, the softened distance weight converges
to the extended power weight, including at the origin. -/
theorem limitWeightedFatou_weight_tendsto {a : ℝ} (ha : 0 ≤ a) (e : ℝ) {ε : ℕ → ℝ}
    (hε : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m => ENNReal.ofReal ((a + ε m) ^ e)) atTop
      (𝓝 (ENNReal.rpow (ENNReal.ofReal a) e)) := by
  have h1 : Tendsto (fun m => ENNReal.ofReal a + ENNReal.ofReal (ε m)) atTop
      (𝓝 (ENNReal.ofReal a + 0)) := by
    refine tendsto_const_nhds.add ?_
    simpa using ENNReal.tendsto_ofReal hε0
  have h2 := h1.ennrpow_const e
  rw [add_zero] at h2
  refine h2.congr fun m => ?_
  rw [← ENNReal.ofReal_add ha (hε m).le,
    ENNReal.ofReal_rpow_of_pos (add_pos_of_nonneg_of_pos ha (hε m))]

/-- The softened weighted disk masses converge to the weighted local mass as the softening
vanishes monotonically through positive values. -/
theorem limitWeightedFatou_mass_tendsto (μ : Measure ℂ) (γ α : ℝ) (hγ : 0 < γ) (hα : 0 ≤ α)
    (z : ℂ) (ρ : ℝ) {ε : ℕ → ℝ} (hε : ∀ m, 0 < ε m) (hεanti : Antitone ε)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ x in Metric.ball z ρ,
      ENNReal.ofReal ((‖x - z‖ + ε m) ^ (-γ * α)) ∂μ) atTop
      (𝓝 (weightedGmcBallMass γ μ α z ρ)) := by
  have he : -γ * α ≤ 0 := by linarith [mul_nonneg hγ.le hα]
  unfold weightedGmcBallMass
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun m => (limitWeightedFatou_ofReal_weight_measurable z _ _).aemeasurable)
    (Eventually.of_forall fun x m m' hmm' => ?_) (Eventually.of_forall fun x => ?_)
  · exact limitWeightedFatou_ofReal_rpow_le (norm_nonneg _) (hε m') (hεanti hmm') he
  · exact limitWeightedFatou_weight_tendsto (norm_nonneg _) _ hε hε0

/-- A uniform bound on the cutoff weighted moments at a nonnegative charge bounds the weighted
local moment of the limiting chaos. -/
theorem weightedGmcBallMoment_le_of_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α : ℝ) (hα : 0 ≤ α) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (t : ℝ) (ht : 0 < t) (C : ℝ≥0∞)
    (hC : ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      ∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z ρ δ ω) t ∂P ≤ C) :
    weightedGmcBallMoment P M γ α z ρ t ≤ C := by
  have he : -γ * α ≤ 0 := by linarith [mul_nonneg hγ.le hα]
  have hB : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
  set ε : ℕ → ℝ := fun m => ρ * (1 / ((m : ℝ) + 1)) with hεdef
  have hεpos : ∀ m, 0 < ε m := fun m => mul_pos hρ (by positivity)
  have hεle : ∀ m, ε m ≤ ρ := fun m => by
    have h : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    simpa only [hεdef, mul_one] using mul_le_mul_of_nonneg_left h hρ.le
  have hεanti : Antitone ε := fun m m' hmm' => by
    have hcast : (m : ℝ) ≤ m' := Nat.cast_le.mpr hmm'
    have h : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left h hρ.le
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [hεdef, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ρ
  have hFatou : ∀ m : ℕ, ∫⁻ ω, (∫⁻ x in Metric.ball z ρ,
      ENNReal.ofReal ((‖x - z‖ + ε m) ^ (-γ * α)) ∂M ω) ^ t ∂P ≤ C := fun m =>
    limitWeightedFatou_softened_moment_le P X hX γ hγ hγ2 M hM Xc hXc α hα z ρ t ht.le C (ε m)
      (hεpos m) (hεle m) hC
  have hlim : Tendsto (fun m : ℕ => ∫⁻ ω, (∫⁻ x in Metric.ball z ρ,
      ENNReal.ofReal ((‖x - z‖ + ε m) ^ (-γ * α)) ∂M ω) ^ t ∂P) atTop
      (𝓝 (∫⁻ ω, (weightedGmcBallMass γ (M ω) α z ρ) ^ t ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun m => ?_)
      (Eventually.of_forall fun ω m m' hmm' => ?_) (Eventually.of_forall fun ω => ?_)
    · exact (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
        (limitWeightedFatou_ofReal_weight_measurable z _ _) _ hB).pow_const t
    · exact ENNReal.rpow_le_rpow (limitWeightedFatou_mass_mono (M ω) z ρ _ he (hεpos m')
        (hεanti hmm')) ht.le
    · exact (limitWeightedFatou_mass_tendsto (M ω) γ α hγ hα z ρ hεpos hεanti hε0).ennrpow_const t
  exact le_of_tendsto' hlim hFatou

end DOZZ.Proofs
