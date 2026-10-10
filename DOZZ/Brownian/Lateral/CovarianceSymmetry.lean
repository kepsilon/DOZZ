/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.CircleRegularization
public import DOZZ.GMC.Moments.CircleScale
public import DOZZ.GFFStructure.PoissonEnergy

/-! Covariance symmetries of the actual orthogonal lateral circle family. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Inversion preserves the dimensionless lateral separation. -/
theorem origin_lateral_normalized_separation_inversion
    (w v : ℂ) (hw : w ≠ 0) (hv : v ≠ 0) :
    max ‖w⁻¹‖ ‖v⁻¹‖ / ‖w⁻¹ - v⁻¹‖ = max ‖w‖ ‖v‖ / ‖w - v‖ := by
  have ha : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hb : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hdiff : w⁻¹ - v⁻¹ = (v - w) / (w * v) := by field_simp
  rw [norm_inv, norm_inv, hdiff, norm_div, norm_mul, norm_sub_rev v w]
  rcases le_total ‖w‖ ‖v‖ with h | h
  · rw [max_eq_right h, max_eq_left (inv_le_inv₀ hb ha |>.mpr h)]
    field_simp
  · rw [max_eq_left h, max_eq_right (inv_le_inv₀ ha hb |>.mpr h)]
    field_simp


/-- The radial circle covariance is the double integral of its scalar kernel. -/
theorem originCircleRadialL2_double_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (x y : ℂ) (r s : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) (hy : σ ≤ ‖y‖ - Real.exp (-s)) :
    covariance (originCircleRadialL2 hc ρ x r) (originCircleRadialL2 hc σ y s) P =
      ∫ w, ∫ v, originRadialCovariance (-Real.log ‖w‖) v
        ∂circleMeasure y s ∂circleMeasure x r := by
  rw [originCircleRadialL2_covariance P X Xc hX hc ρ hρ]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae x r ρ hx] with w hw
  rw [covariance_comm, originCircleRadialL2_covariance P X Xc hX hc σ hσ]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae y s σ hy] with v hv
  rw [covariance_comm,
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _),
    clampedLogRadius_eq ρ w hw, clampedLogRadius_eq σ v hv]
  dsimp only
  rw [origin_circle_radial_covariance X Xc hX hc]

/-- The scalar radial kernel is integrable on every valid circle. -/
theorem originRadialCovariance_circle_integrable (σ : ℝ) (hσ : 0 < σ)
    (y : ℂ) (s t : ℝ) (hy : σ ≤ ‖y‖ - Real.exp (-s)) :
    Integrable (fun v => originRadialCovariance t v) (circleMeasure y s) := by
  let f : ℂ → ℝ := fun v => min t (clampedLogRadius σ v) + max 0 (-t) +
    max 0 (-clampedLogRadius σ v)
  have hf : Continuous f := by
    exact ((continuous_const.min (continuous_clampedLogRadius σ hσ)).add
      continuous_const).add (continuous_const.max (continuous_clampedLogRadius σ hσ).neg)
  apply (integrable_continuous_circleMeasure y s f hf).congr
  filter_upwards [circle_norm_lower_ae y s σ hy] with v hv
  dsimp [f, originRadialCovariance]
  rw [clampedLogRadius_eq σ v hv, neg_neg]

/-- Averaging the radial kernel is integrable on the other valid circle. -/
theorem originRadialCovariance_double_circle_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (x y : ℂ) (r s : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) (hy : σ ≤ ‖y‖ - Real.exp (-s)) :
    Integrable (fun w => ∫ v, originRadialCovariance (-Real.log ‖w‖) v
      ∂circleMeasure y s) (circleMeasure x r) := by
  let : IsProbabilityMeasure P := hX.1
  let V := originCircleRadialL2 hc σ y s
  have hi := (innerSL ℝ V).integrable_comp
    (integrable_clampedRadialCircleL2 P X Xc hX hc ρ hρ x r)
  apply hi.congr
  filter_upwards [circle_norm_lower_ae x r ρ hx] with w hw
  change inner ℝ V (circleAverageL2 hc (0, clampedLogRadius ρ w)) = _
  rw [real_inner_comm]
  have he := covariance_L2_eq (circleAverageL2 hc (0, clampedLogRadius ρ w)) V
  rw [circleAverageL2_integral_eq_zero P X Xc hX hc, zero_mul, sub_zero] at he
  rw [← he, covariance_comm,
    originCircleRadialL2_covariance P X Xc hX hc σ hσ]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae y s σ hy] with v hv
  rw [covariance_comm,
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _),
    clampedLogRadius_eq ρ w hw, clampedLogRadius_eq σ v hv]
  dsimp only
  rw [origin_circle_radial_covariance X Xc hX hc]

/-- Exact circle covariance after the radial pin terms have been removed. -/
theorem originCircleLateralL2_covariance_kernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (x y : ℂ) (r s : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) (hy : σ ≤ ‖y‖ - Real.exp (-s)) :
    covariance (originCircleLateralL2 hc ρ x r) (originCircleLateralL2 hc σ y s) P =
      ∫ w, ∫ v, gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v
        ∂circleMeasure y s ∂circleMeasure x r := by
  rw [originCircleLateralL2_covariance_expansion P X Xc hX hc ρ σ hρ hσ x y r s hx hy,
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _),
    circleAverage_covariance_integral P X Xc hX hc,
    originCircleRadialL2_double_covariance P X Xc hX hc ρ σ hρ hσ x y r s hx hy]
  have hf : Integrable (fun w => ∫ v, gffKernel w v ∂circleMeasure y s)
      (circleMeasure x r) := by
    simp_rw [integral_gffKernel_circleMeasure]
    exact integrable_continuous_circleMeasure x r _
      (((continuous_const.max (continuous_const.sub continuous_id).norm).log
        (fun _ => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))).neg.add
          CirclePotential.continuous_log_normPlus |>.add continuous_const)
  rw [← integral_sub hf
    (originRadialCovariance_double_circle_integrable P X Xc hX hc ρ σ hρ hσ x y r s hx hy)]
  apply integral_congr_ae
  exact ae_of_all _ fun w => (integral_sub (integrable_gffKernel_circleMeasure y w s)
    (originRadialCovariance_circle_integrable σ hσ y s (-Real.log ‖w‖) hy)).symm

/-- The distance of a circle from zero scales together with its inactive clamp. -/
theorem originCircleCutoff_dilation_lower (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (x : ℂ) (r : ℝ) (hx : ρ ≤ ‖x‖ - Real.exp (-r)) :
    c * ρ ≤ ‖(c : ℂ) * x‖ - Real.exp (-(r - Real.log c)) := by
  have hn : ‖(c : ℂ)‖ = c := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have he : Real.exp (-(r - Real.log c)) = c * Real.exp (-r) := by
    have ha : -(r - Real.log c) = Real.log c + -r := by ring
    rw [ha, Real.exp_add, Real.exp_log hc]
  rw [norm_mul, hn, he, ← mul_sub]
  exact mul_le_mul_of_nonneg_left hx hc.le

/-- Dilation of a valid orthogonal circle includes the same dilation of its clamp. -/
noncomputable def originCircleCutoff_dilation (c : ℝ) (hc : 0 < c)
    (p : OriginCircleCutoff) : OriginCircleCutoff :=
  ⟨(c * p.val.1, (c * p.val.2.1, p.val.2.2 - Real.log c)),
    mul_pos hc p.property.1,
    originCircleCutoff_dilation_lower c hc _ _ _ p.property.2⟩

/-- Actual lateral circle covariances are invariant under every positive common dilation. -/
theorem originCircleLateralL2_covariance_dilation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℝ) (hpos : 0 < c) (p q : OriginCircleCutoff) :
    covariance
      (originCircleLateralL2 hc (c * p.val.1) (c * p.val.2.1) (p.val.2.2 - Real.log c))
      (originCircleLateralL2 hc (c * q.val.1) (c * q.val.2.1) (q.val.2.2 - Real.log c)) P =
    covariance (originCircleLateralL2 hc p.val.1 p.val.2.1 p.val.2.2)
      (originCircleLateralL2 hc q.val.1 q.val.2.1 q.val.2.2) P := by
  let : IsProbabilityMeasure (circleMeasure q.val.2.1 q.val.2.2) := circleMeasure_isProbability _ _
  let F : ℂ → ℂ → ℝ := fun w v => gffKernel w v -
    originRadialCovariance (-Real.log ‖w‖) v
  have hF : Measurable (fun z : ℂ × ℂ => F z.1 z.2) := by
    dsimp [F, gffKernel, originRadialCovariance, normPlus]
    fun_prop
  have hscale : Measurable (fun z : ℂ => (c : ℂ) * z) := by fun_prop
  have hinner (w : ℂ) :
      (∫ v, F w v ∂circleMeasure (c * q.val.2.1) (q.val.2.2 - Real.log c)) =
        ∫ v, F w (c * v) ∂circleMeasure q.val.2.1 q.val.2.2 := by
    rw [circleMeasure_scale hpos]
    exact integral_map hscale.aemeasurable
      ((hF.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable)
  have ho : Measurable (fun w => ∫ v, F w (c * v)
      ∂circleMeasure q.val.2.1 q.val.2.2) := by
    have hf : Measurable (fun z : ℂ × ℂ => F z.1 (c * z.2)) :=
      hF.comp (f := fun z : ℂ × ℂ => (z.1, (c : ℂ) * z.2))
        (measurable_fst.prodMk (hscale.comp measurable_snd))
    exact hf.stronglyMeasurable.integral_prod_right'.measurable
  rw [originCircleLateralL2_covariance_kernel P X Xc hX hc
      (c * p.val.1) (c * q.val.1) (mul_pos hpos p.property.1) (mul_pos hpos q.property.1)
      _ _ _ _ (originCircleCutoff_dilation_lower c hpos _ _ _ p.property.2)
      (originCircleCutoff_dilation_lower c hpos _ _ _ q.property.2),
    originCircleLateralL2_covariance_kernel P X Xc hX hc
      p.val.1 q.val.1 p.property.1 q.property.1 _ _ _ _ p.property.2 q.property.2]
  change (∫ w, ∫ v, F w v ∂circleMeasure (c * q.val.2.1) (q.val.2.2 - Real.log c)
    ∂circleMeasure (c * p.val.2.1) (p.val.2.2 - Real.log c)) = _
  simp_rw [hinner]
  rw [circleMeasure_scale hpos, integral_map hscale.aemeasurable ho.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae _ _ _ p.property.2] with w hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (p.property.1.trans_le hw)
  apply integral_congr_ae
  let : NullSingletonClass (circleMeasure q.val.2.1 q.val.2.2) := circleMeasure_noAtoms _ _
  filter_upwards [circle_norm_lower_ae _ _ _ q.property.2,
    (circleMeasure q.val.2.1 q.val.2.2).ae_ne w] with v hv hsep
  exact origin_lateralKernel_dilation (c : ℂ) w v (by exact_mod_cast hpos.ne') hw0
    (norm_pos_iff.mp (q.property.1.trans_le hv)) hsep.symm

/-- The same covariance identity in the literal centered second-moment normalization. -/
theorem originCircleLateralL2_dilation_gaussianCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℝ) (hpos : 0 < c) (p q : OriginCircleCutoff) :
    gaussianCovariance P
      (originCircleLateralL2 hc (c * p.val.1) (c * p.val.2.1) (p.val.2.2 - Real.log c))
      (originCircleLateralL2 hc (c * q.val.1) (c * q.val.2.1) (q.val.2.2 - Real.log c)) =
    gaussianCovariance P (originCircleLateralL2 hc p.val.1 p.val.2.1 p.val.2.2)
      (originCircleLateralL2 hc q.val.1 q.val.2.1 q.val.2.2) := by
  have he := originCircleLateralL2_covariance_dilation P X Xc hX hc c hpos p q
  simpa only [gaussianCovariance, covariance, originCircleLateralL2_integral_eq_zero P X Xc hX hc,
    mul_pos hpos p.property.1, mul_pos hpos q.property.1, p.property.1, q.property.1,
    sub_zero] using he

/-- Every finite vector of actual orthogonal circle cutoffs has the dilation-invariant law. -/
theorem originCircleLateralL2_dilation_fdd_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℝ) (hpos : 0 < c) (n : ℕ) (p : Fin n → OriginCircleCutoff) :
    P.map (fun ω i => originCircleLateralL2 hc (c * (p i).val.1)
      (c * (p i).val.2.1) ((p i).val.2.2 - Real.log c) ω) =
    P.map (fun ω i => originCircleLateralL2 hc (p i).val.1 (p i).val.2.1 (p i).val.2.2 ω) := by
  classical
  apply map_eq_of_centeredJointlyGaussian_of_covariance_eq
  · exact originCircleLateralL2_centeredJointlyGaussian P X Xc hX hc n
      (fun i => originCircleCutoff_dilation c hpos (p i))
  · exact originCircleLateralL2_centeredJointlyGaussian P X Xc hX hc n p
  · intro i j
    exact originCircleLateralL2_dilation_gaussianCovariance P X Xc hX hc c hpos (p i) (p j)


/-- Dilation invariance for the actual measurable regularizer on a valid spatial chart. -/
theorem originLateralCircleRegularization_dilation_fdd_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ c ε : ℝ) (hρ : 0 < ρ) (hcpos : 0 < c) (hε : 0 < ε) (hερ : ε ≤ ρ)
    (n : ℕ) (xs : Fin n → ℂ) (hxs : ∀ i, xs i ∈ originLateralChart ρ) :
    P.map (fun ω i => originLateralCircleRegularization Xc (c * ρ) ω (c * ε) (c * xs i)) =
      P.map (fun ω i => originLateralCircleRegularization Xc ρ ω ε (xs i)) := by
  let p : Fin n → OriginCircleCutoff := fun i =>
    ⟨(ρ, xs i, Real.log (1 / ε)), hρ,
      originLateralChart_cutoff_lower ρ ε (xs i) (hxs i) hε hερ⟩
  have hr : Real.log (1 / (c * ε)) = Real.log (1 / ε) - Real.log c := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv,
      Real.log_mul hcpos.ne' hε.ne']
    ring
  calc
    _ = P.map (fun ω i => originCircleLateralL2 hc (c * ρ) (c * xs i)
        (Real.log (1 / ε) - Real.log c) ω) := by
      apply Measure.map_congr
      filter_upwards [ae_all_iff.mpr fun i => clampedCircleLateralSample_ae_eq
        P X Xc hX hc hm (c * ρ) (mul_pos hcpos hρ) (c * xs i)
          (Real.log (1 / (c * ε)))] with ω hω
      exact funext fun i => by
        rw [← hr]
        exact (hω i).symm
    _ = _ := originCircleLateralL2_dilation_fdd_law P X Xc hX hc c hcpos n p
    _ = _ := by
      apply Measure.map_congr
      filter_upwards [ae_all_iff.mpr fun i => clampedCircleLateralSample_ae_eq
        P X Xc hX hc hm ρ hρ (xs i) (Real.log (1 / ε))] with ω hω
      exact funext hω

/-- The finite Wick normalization is preserved by the same chart dilation. -/
theorem originLateralCircleRegularization_dilation_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ c ε : ℝ) (hρ : 0 < ρ) (hcpos : 0 < c) (hε : 0 < ε) (hερ : ε ≤ ρ)
    (x : ℂ) (hx : x ∈ originLateralChart ρ) :
    gaussianVariance P (fun ω => originLateralCircleRegularization Xc (c * ρ) ω (c * ε) (c * x)) =
      gaussianVariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x) := by
  have h := originLateralCircleRegularization_dilation_fdd_law P X Xc hX hc hm
    ρ c ε hρ hcpos hε hερ 1 (fun _ => x) (fun _ => hx)
  have hs := congrArg (fun μ : Measure (Fin 1 → ℝ) => ∫ v, (v 0) ^ 2 ∂μ) h
  have hml : Measurable (fun ω (i : Fin 1) =>
      originLateralCircleRegularization Xc (c * ρ) ω (c * ε) (c * x)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (originLateralCircleRegularization_measurableAtScale Xc hm (c * ρ)
      (mul_pos hcpos hρ) (c * ε)).comp (measurable_id.prodMk measurable_const)
  have hmr : Measurable (fun ω (i : Fin 1) => originLateralCircleRegularization Xc ρ ω ε x) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (originLateralCircleRegularization_measurableAtScale Xc hm ρ hρ ε).comp
      (measurable_id.prodMk measurable_const)
  rw [integral_map hml.aemeasurable ((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable,
    integral_map hmr.aemeasurable ((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable] at hs
  simpa only [gaussianVariance, gaussianCovariance, pow_two] using hs

/-- Radial projection commutes with inversion as reflection of the cylinder. -/
theorem logRadiusProjection_inversion (F : Measure ℂ) :
    (F.map (fun z : ℂ => z⁻¹)).map (fun z => -Real.log ‖z‖) =
      (F.map (fun z => -Real.log ‖z‖)).map (fun s : ℝ => -s) := by
  have hm : Measurable (fun z : ℂ => -Real.log ‖z‖) := by fun_prop
  rw [Measure.map_map hm measurable_inv,
    Measure.map_map measurable_neg hm]
  congr 1
  funext z
  simp only [Function.comp_apply, norm_inv, Real.log_inv]

/-- Radial projection commutes with nonzero dilation as translation of the cylinder;
the zero atom is excluded explicitly because logarithmic radius is defined as zero there. -/
theorem logRadiusProjection_dilation (F : Measure ℂ) (hF : F {0} = 0)
    (c : ℝ) (hc : 0 < c) :
    (F.map (fun z : ℂ => (c : ℂ) * z)).map (fun z => -Real.log ‖z‖) =
      (F.map (fun z => -Real.log ‖z‖)).map (fun s : ℝ => s - Real.log c) := by
  have hm : Measurable (fun z : ℂ => -Real.log ‖z‖) := by fun_prop
  have hscale : Measurable (fun z : ℂ => (c : ℂ) * z) := by fun_prop
  have hshift : Measurable (fun s : ℝ => s - Real.log c) := by fun_prop
  rw [Measure.map_map hm hscale, Measure.map_map hshift hm]
  apply Measure.map_congr
  have hzero : ∀ᵐ z ∂F, z ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hF
  filter_upwards [hzero] with z hz
  dsimp only [Function.comp_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
    Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hz)]
  ring

/-- The planar reference density transforms with the inverse square Jacobian. -/
theorem originLateralPlaneDensity_dilation (c : ℝ) (hc : 0 < c) (x : ℂ) :
    originLateralPlaneDensity (c * x) = c ^ (-2 : ℝ) * originLateralPlaneDensity x := by
  unfold originLateralPlaneDensity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
    Real.mul_rpow hc.le (norm_nonneg x)]


/-- Positive dilation carries precisely the chart with the dilated clamp. -/
theorem originLateralChart_dilation_mem (ρ c : ℝ) (hc : 0 < c) (x : ℂ) :
    (c : ℂ) * x ∈ originLateralChart (c * ρ) ↔ x ∈ originLateralChart ρ := by
  change 2 * (c * ρ) < ‖(c : ℂ) * x‖ ↔ 2 * ρ < ‖x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have he : 2 * (c * ρ) = c * (2 * ρ) := by ring
  rw [he, mul_lt_mul_iff_right₀ hc]



end DOZZ.Proofs
