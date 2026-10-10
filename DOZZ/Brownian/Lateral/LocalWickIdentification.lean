/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.UniformWeightLimit
public import DOZZ.GMC.Moments.InversionAdmissibleVersion

/-!
# Identifying the local radial-removed plane chaos

The exact finite-cutoff Wick factorization, followed by the proved finite radial-factor
limit, identifies the independent local lateral measure with the radial removal of the
actual plane GMC. All cutoffs use the original circle-average witness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions InnerProductSpace RealInnerProductSpace

namespace DOZZ.Proofs

/-- The actual finite circle Wick density is the product of the local lateral Wick
density and its exact finite radial reinsertion factor, at every valid chart point. -/
theorem originCircle_cutoff_wick_reinsertion_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (A : Ω → TwoSidedPath) (hA : A =ᵐ[P] originRadialPath Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (x : ℂ)
    (hx : x ∈ originLateralChart ρ) (hr : Real.exp (-r) ≤ ρ) :
    ∀ᵐ ω ∂P,
      normPlus x ^ (-4 : ℝ) * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) =
      originLateralPlaneDensity x * originRadialCutoffReinsertionWeight hc ρ γ r (A ω) x *
        Real.exp (γ * originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x -
          γ ^ 2 / 2 * gaussianVariance P
            (fun ω' => originLateralCircleRegularization Xc ρ ω' (Real.exp (-r)) x)) := by
  have hxU : 2 * ρ < ‖x‖ := hx
  have hxρ : ρ ≤ ‖x‖ := by linarith only [hxU, hρ]
  have hbound : ρ ≤ ‖x‖ - Real.exp (-r) := by linarith only [hxU, hr]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hρ.trans_le hxρ)
  have hCY := circleAverageL2_ae_eq hc (x, r)
  have hLY := clampedCircleLateralSample_ae_eq P X Xc hX hc hm ρ hρ x r
  have hRY := originCircleRadialL2_ae_eq P X Xc hX hc hm ρ hρ x r
  have hCV : gaussianVariance P (circleAverageL2 hc (x, r)) =
      gaussianVariance P (fun ω => Xc ω x r) := by
    unfold gaussianVariance gaussianCovariance
    apply integral_congr_ae
    filter_upwards [hCY] with ω hω
    rw [hω]
  have hLV : gaussianVariance P (originCircleLateralL2 hc ρ x r) =
      gaussianVariance P (fun ω => originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x) := by
    unfold gaussianVariance gaussianCovariance
    apply integral_congr_ae
    filter_upwards [hLY] with ω hω
    have hl : originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x =
        clampedCircleLateralSample Xc ρ ω x r := by
      simp only [originLateralCircleRegularization, one_div, Real.log_inv, Real.log_exp, neg_neg]
    rw [hl, hω]
  filter_upwards [originCircleLateralL2_wick_factorization P X Xc hX hc ρ hρ x r γ hbound,
    hCY, hLY, hRY, hA, originRadialPath_eval_ae hcont] with ω hw hC hL hR hAω hpath
  have hl : originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x =
      clampedCircleLateralSample Xc ρ ω x r := by
    simp only [originLateralCircleRegularization, one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hrad : (∫ z, (A ω) (clampedLogRadius ρ z) ∂circleMeasure x r) =
      originCircleRadialL2 hc ρ x r ω := by
    rw [hR, hAω]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => hpath _)
  rw [hC, hL, hCV, hLV, ← hl] at hw
  rw [hw]
  have hd := originRadialCutoffReinsertionWeight_density_identity hc ρ γ r (A ω) x hx0 hxρ
  rw [hrad] at hd
  calc _ = (normPlus x ^ (-4 : ℝ) *
        Real.exp (γ * originCircleRadialL2 hc ρ x r ω -
          γ ^ 2 / 2 * gaussianVariance P (originCircleRadialL2 hc ρ x r))) *
        Real.exp (γ * originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x -
          γ ^ 2 / 2 * gaussianVariance P
            (fun ω' => originLateralCircleRegularization Xc ρ ω' (Real.exp (-r)) x)) := by ring
    _ = _ := by rw [hd]

/-- Write the admissible cutoff integral against planar volume with its reference
density. This identity is valid even when a particular signed section is not integrable. -/
theorem regularizedLogChaosTestMass_eq_density_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Set ℂ) (dens : ℂ → ℝ) (hm : Measurable dens) (hpos : ∀ x, 0 ≤ dens x)
    (Y : Ω → ℝ → ℂ → ℝ) (γ r : ℝ) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) :
    regularizedLogChaosTestMass P U dens Y γ r ω f =
      ∫ x in U, dens x * f x * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Y ω' (Real.exp (-r)) x)) := by
  unfold regularizedLogChaosTestMass logRegularizationReference
  have hd : Measurable (fun x => ENNReal.ofReal (dens x)) := ENNReal.measurable_ofReal.comp hm
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hpos x)]
  unfold gaussianVariance gaussianCovariance
  simp only [pow_two, mul_assoc]

/-- The exact finite Wick density identity integrates to equality of the original
circle test mass and the lateral mass with the actual finite radial-weighted test. -/
theorem originCircle_cutoff_wick_reinsertion_density_integral_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (A : Ω → TwoSidedPath) (hAm : Measurable A) (hA : A =ᵐ[P] originRadialPath Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (hr : Real.exp (-r) ≤ ρ)
    (f : ℂ → ℝ) :
    ∀ᵐ ω ∂P,
      (∫ x in originLateralChart ρ, f x * (normPlus x ^ (-4 : ℝ) *
        Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r)))) =
      ∫ x in originLateralChart ρ, f x * (originLateralPlaneDensity x *
        originRadialCutoffReinsertionWeight hc ρ γ r (A ω) x *
        Real.exp (γ * originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x -
          γ ^ 2 / 2 * gaussianVariance P
            (fun ω' => originLateralCircleRegularization Xc ρ ω' (Real.exp (-r)) x))) := by
  let _ := hX.1
  let U := originLateralChart ρ
  let C : Ω → ℂ → ℝ := fun ω x => normPlus x ^ (-4 : ℝ) * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
    gaussianVariance P (fun ω' => Xc ω' x r))
  let L : Ω → ℂ → ℝ := fun ω x => originLateralPlaneDensity x *
    originRadialCutoffReinsertionWeight hc ρ γ r (A ω) x *
      Real.exp (γ * originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => originLateralCircleRegularization Xc ρ ω' (Real.exp (-r)) x))
  have hdC : Measurable (fun x : ℂ => normPlus x ^ (-4 : ℝ)) := by
    fun_prop [normPlus]
  have hdL : Measurable originLateralPlaneDensity := by
    fun_prop [originLateralPlaneDensity]
  have hvC : Measurable (fun x : ℂ => gaussianVariance P (fun ω => Xc ω x r)) := by
    unfold gaussianVariance gaussianCovariance
    exact ((hc.1 r).comp measurable_swap).mul ((hc.1 r).comp measurable_swap)
      |>.stronglyMeasurable.integral_prod_right.measurable
  have hY := originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ
  have hvL := admissibleLogRegularization_variance_measurable P U
    originLateralPlaneDensity (min ρ 1) (originLateralCircleRegularization Xc ρ) hY (Real.exp (-r))
  have harg : Measurable (fun p : Ω × ℂ => (A p.1, (p.2, r))) :=
    (hAm.comp measurable_fst).prodMk (measurable_snd.prodMk (measurable_const :
      Measurable (fun _ : Ω × ℂ => r)))
  have hW : Measurable (fun p : Ω × ℂ => originRadialCutoffReinsertionWeight hc ρ γ r (A p.1) p.2) := by
    change Measurable ((fun p : TwoSidedPath × (ℂ × ℝ) =>
      originRadialCutoffReinsertionWeight hc ρ γ p.2.2 p.1 p.2.1) ∘ fun p : Ω × ℂ => (A p.1, (p.2, r)))
    exact (continuous_originRadialCutoffReinsertionWeight_joint P X Xc hX hc ρ γ hρ).measurable.comp harg
  have hmC : Measurable (fun p : Ω × ℂ => C p.1 p.2) :=
    (hdC.comp measurable_snd).mul (((hc.1 r).const_mul γ).sub
      ((hvC.comp measurable_snd).const_mul (γ ^ 2 / 2))).exp
  have hmL : Measurable (fun p : Ω × ℂ => L p.1 p.2) :=
    ((hdL.comp measurable_snd).mul hW).mul
      (((hY.measurableAtScale _).const_mul γ).sub
        ((hvL.comp measurable_snd).const_mul (γ ^ 2 / 2))).exp
  have heq : ∀ᵐ ω ∂P, ∀ᵐ x ∂volume.restrict U, C ω x = L ω x := by
    have hset : MeasurableSet {p : Ω × ℂ | C p.1 p.2 = L p.1 p.2} :=
      measurableSet_eq_fun hmC hmL
    apply (Measure.ae_ae_comm (μ := P) (ν := volume.restrict U)
      (p := fun ω x => C ω x = L ω x) hset).2
    filter_upwards [ae_restrict_mem (isOpen_originLateralChart ρ).measurableSet] with x hx
    exact originCircle_cutoff_wick_reinsertion_ae P X Xc hX hc hm hcont A hA ρ γ r hρ x hx hr
  filter_upwards [heq] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with x hx
  exact congrArg (fun z : ℝ => f x * z) hx

/-- The exact finite Wick density identity integrates to equality of the original
circle test mass and the lateral mass with the actual finite radial-weighted test. -/
theorem originCircle_cutoff_wick_reinsertion_test_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (A : Ω → TwoSidedPath) (hAm : Measurable A) (hA : A =ᵐ[P] originRadialPath Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (hr : Real.exp (-r) ≤ ρ)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    (fun ω => regularizedLogChaosTestMass P (originLateralChart ρ)
      (fun x => normPlus x ^ (-4 : ℝ)) (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f) =ᵐ[P]
    fun ω => regularizedLogChaosTestMass P (originLateralChart ρ) originLateralPlaneDensity
      (originLateralCircleRegularization Xc ρ) γ r ω
        (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (A ω) f hfc) := by
  let U := originLateralChart ρ
  have hdC : Measurable (fun x : ℂ => normPlus x ^ (-4 : ℝ)) := by
    fun_prop [normPlus]
  have hdL : Measurable originLateralPlaneDensity := by
    fun_prop [originLateralPlaneDensity]
  have hpC (x : ℂ) : 0 ≤ normPlus x ^ (-4 : ℝ) := Real.rpow_nonneg
    (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))) _
  have hpL (x : ℂ) : 0 ≤ originLateralPlaneDensity x := Real.rpow_nonneg (norm_nonneg _) _
  filter_upwards [originCircle_cutoff_wick_reinsertion_density_integral_ae
    P X Xc hX hc hm hcont A hAm hA ρ γ r hρ hr f] with ω hω
  have hcut : Real.log (1 / Real.exp (-r)) = r := by
    simp only [one_div, Real.log_inv, Real.log_exp, neg_neg]
  calc regularizedLogChaosTestMass P U (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f =
      ∫ x in U, f x * (normPlus x ^ (-4 : ℝ) *
        Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r))) := by
          rw [regularizedLogChaosTestMass_eq_density_integral P U _ hdC hpC]
          simp only [hcut]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    _ = ∫ x in U, f x * (originLateralPlaneDensity x *
        originRadialCutoffReinsertionWeight hc ρ γ r (A ω) x *
        Real.exp (γ * originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x -
          γ ^ 2 / 2 * gaussianVariance P
            (fun ω' => originLateralCircleRegularization Xc ρ ω' (Real.exp (-r)) x))) := hω
    _ = regularizedLogChaosTestMass P U originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ r ω
          (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (A ω) f hfc) := by
          rw [regularizedLogChaosTestMass_eq_density_integral P U _ hdL hpL]
          apply integral_congr_ae
          filter_upwards [] with x
          change _ = originLateralPlaneDensity x *
            (f x * originRadialCutoffReinsertionWeight hc ρ γ r (A ω) x) * _
          ring

/-- The independent local chaos reconstructs every compact test integral of the actual
GMC when multiplied by the radial reinsertion weight. -/
theorem exists_originLateralChartGMC_reinsertion_test_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ N ∧
      IndepFun (originRadialPath Xc) N P ∧
      ∀ (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)),
        tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ →
        (fun ω => ∫ x, f x ∂M ω) =ᵐ[P]
          fun ω => ∫ x, originRadialWeightedTest ρ γ hρ (originRadialPath Xc ω) f hfc x ∂N ω := by
  obtain ⟨N, hN, hi, hw⟩ := exists_originLateralChartGMC_cutoff_weighted_limit
    P X Xc hX hc hm hcont ρ hρ γ hγ hγ2
  obtain ⟨Mc, hMc, _, hMcEq⟩ := isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM
    Xc hc (originLateralChart ρ) (isOpen_originLateralChart ρ)
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  let A := hA.mk (originRadialPath Xc)
  have hAm : Measurable A := hA.measurable_mk
  have hAe : A =ᵐ[P] originRadialPath Xc := hA.ae_eq_mk.symm
  refine ⟨N, hN, hi, ?_⟩
  intro f hfc hfU
  let F : ℝ → Ω → ℝ := fun r ω => regularizedLogChaosTestMass P (originLateralChart ρ)
    (fun x => normPlus x ^ (-4 : ℝ)) (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f
  let G : ℝ → Ω → ℝ := fun r ω => regularizedLogChaosTestMass P (originLateralChart ρ)
    originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω
      (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (originRadialPath Xc ω) f hfc)
  have hFG : ∀ᶠ r : ℝ in atTop, G r =ᵐ[P] F r := by
    filter_upwards [eventually_ge_atTop (-Real.log ρ)] with r hr
    have hcut : Real.exp (-r) ≤ ρ := by
      calc Real.exp (-r) ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.mpr (by linarith only [hr])
        _ = ρ := Real.exp_log hρ
    have heq := originCircle_cutoff_wick_reinsertion_test_ae P X Xc hX hc hm hcont A hAm hAe
      ρ γ r hρ hcut f hfc
    filter_upwards [heq, hAe] with ω hω hAω
    change regularizedLogChaosTestMass P (originLateralChart ρ) originLateralPlaneDensity
      (originLateralCircleRegularization Xc ρ) γ r ω
        (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (originRadialPath Xc ω) f hfc) = F r ω
    rw [← hAω, ← hω]
  have htN : TendstoInMeasure P F atTop (fun ω =>
      ∫ x, originRadialWeightedTest ρ γ hρ (originRadialPath Xc ω) f hfc x ∂N ω) :=
    TendstoInMeasure.congr' hFG EventuallyEq.rfl (hw f hfc hfU)
  have htM : TendstoInMeasure P F atTop (fun ω => ∫ x, f x ∂Mc ω) := hMc.2.2.2 f hfc hfU
  have htest := tendstoInMeasure_ae_unique htM htN
  filter_upwards [htest, hMcEq] with ω hω hMω
  rw [← hMω] at hω
  rw [← integral_restrict_eq_integral_of_zero_on_compl (M ω) (originLateralChart ρ)
    (isOpen_originLateralChart ρ).measurableSet f
    (boundedContinuousFunction_eq_zero_off_tsupport_subset f (originLateralChart ρ) hfU)]
  exact hω

/-- Reinserting a continuous radial weight preserves compact finiteness. -/
theorem originLateralReinsertedMeasure_compact_lt_top
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (N : Measure ℂ)
    (K : Set ℂ) (hK : IsCompact K) (hN : N K < ⊤) :
    (N.withDensity (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x))) K < ⊤ := by
  have hw : Continuous (originRadialReinsertionWeight ρ γ A) :=
    (continuous_originRadialReinsertionWeight ρ γ hρ).comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hw.continuousOn
  rw [withDensity_apply _ hK.measurableSet]
  have hb : (∫⁻ x in K, ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x) ∂N) ≤
      ENNReal.ofReal C * N K := by
    calc _ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂N := by
           apply lintegral_mono_ae
           filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
           exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hx))
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)

/-- Reinsertion keeps a chart-supported measure supported in the same chart. -/
theorem originLateralReinsertedMeasure_compl
    (ρ γ : ℝ) (A : TwoSidedPath) (N : Measure ℂ) (U : Set ℂ) (hN : N Uᶜ = 0) :
    (N.withDensity (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x))) Uᶜ = 0 :=
  withDensity_absolutelyContinuous N _ hN

/-- Integration against the reinserted measure equals integration of the literal
radial-weighted compact test against the original lateral measure. -/
theorem originLateralReinsertedMeasure_test_integral
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (N : Measure ℂ)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    (∫ x, f x ∂N.withDensity (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x))) =
      ∫ x, originRadialWeightedTest ρ γ hρ A f hfc x ∂N := by
  have hm : Measurable (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_originRadialReinsertionWeight ρ γ hρ).comp
        (continuous_const.prodMk continuous_id)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (originRadialReinsertionWeight_pos ρ γ A x).le, smul_eq_mul,
    originRadialWeightedTest_apply]
  exact mul_comm _ _

/-- The independent local lateral chaos reinserts to the actual GMC as measures, on one
common probability-one event, by countable compact measure determination. -/
theorem exists_originLateralChartGMC_reinserted_measure_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ N ∧
      IndepFun (originRadialPath Xc) N P ∧
      ∀ᵐ ω ∂P,
        (N ω).withDensity (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ
          (originRadialPath Xc ω) x)) = (M ω).restrict (originLateralChart ρ) := by
  obtain ⟨N, hN, hi, htest⟩ := exists_originLateralChartGMC_reinsertion_test_identity
    P X Xc hX hc hm hcont ρ γ hρ hγ hγ2 M hM
  obtain ⟨K, hKc, hKU, _, _, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests (originLateralChart ρ) (isOpen_originLateralChart ρ)
  let Nr : Ω → Measure ℂ := fun ω => (N ω).withDensity
    (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ (originRadialPath Xc ω) x))
  let Mr : Ω → Measure ℂ := fun ω => (M ω).restrict (originLateralChart ρ)
  have hEach : ∀ nm : ℕ × ℕ,
      (fun ω => ∫ x, f nm x ∂Nr ω) =ᵐ[P] fun ω => ∫ x, f nm x ∂Mr ω := by
    intro nm
    filter_upwards [htest (f nm) (hf nm.1 nm.2).1 (hf nm.1 nm.2).2.2] with ω hω
    rw [originLateralReinsertedMeasure_test_integral ρ γ hρ _ _ (f nm) (hf nm.1 nm.2).1]
    rw [integral_restrict_eq_integral_of_zero_on_compl (M ω) (originLateralChart ρ)
      (isOpen_originLateralChart ρ).measurableSet (f nm)
      (boundedContinuousFunction_eq_zero_off_tsupport_subset (f nm) _ (hf nm.1 nm.2).2.2)]
    exact hω.symm
  refine ⟨N, hN, hi, ?_⟩
  filter_upwards [ae_all_iff.mpr hEach] with ω hω
  have hMfin := hM.1 ω
  have hMcompl : Mr ω (originLateralChart ρ)ᶜ = 0 := by
    rw [Measure.restrict_apply (isOpen_originLateralChart ρ).measurableSet.compl]
    simp only [Set.compl_inter_self, measure_empty]
  exact admissible_countable_tests_determine_chart_measures (originLateralChart ρ)
    (isOpen_originLateralChart ρ) (Nr ω) (Mr ω)
    (originLateralReinsertedMeasure_compl ρ γ _ _ _ (hN.2.1 ω)) hMcompl
    (fun L hL hLU => originLateralReinsertedMeasure_compact_lt_top ρ γ hρ _ _ L hL
      (hN.2.2.1 ω L hL hLU))
    (fun L hL _ => by
      change (M ω).restrict (originLateralChart ρ) L < ⊤
      exact measure_lt_top _ _)
    K hKc hKU hKcofinal f (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩)
    (fun n g hg hgs δ hδ => hdense n g hg hgs δ hδ) (fun n m => hω (n, m))

/-- On a chart-supported measure, reinsertion followed by the exact radial
removal density recovers the original measure. -/
theorem originLateralReinsertedMeasure_removal
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (N : Measure ℂ)
    (hN : N (originLateralChart ρ)ᶜ = 0) :
    (N.withDensity (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x))).withDensity
      (lateralRadialWeight γ A) = N := by
  have hf : Measurable (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_originRadialReinsertionWeight ρ γ hρ).comp
        (continuous_const.prodMk continuous_id)).measurable
  have hg : Measurable (lateralRadialWeight γ A) := by
    have harg : Measurable (fun x : ℂ => ((γ, A), x)) := measurable_const.prodMk measurable_id
    change Measurable ((fun p : (ℝ × TwoSidedPath) × ℂ => lateralRadialWeight p.1.1 p.1.2 p.2) ∘
      fun x : ℂ => ((γ, A), x))
    exact measurable_lateralRadialWeight.comp harg
  rw [← withDensity_mul N hf hg]
  have hchart : ∀ᵐ x ∂N, x ∈ originLateralChart ρ := by
    rw [ae_iff]
    exact hN
  have heq : (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x) *
      lateralRadialWeight γ A x) =ᵐ[N] (1 : ℂ → ℝ≥0∞) := by
    filter_upwards [hchart] with x hx
    exact originRadialReinsertionWeight_removal_mul ρ γ hρ A x hx
  change N.withDensity (fun x => ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x) *
    lateralRadialWeight γ A x) = N
  rw [withDensity_congr_ae heq, withDensity_one]

/-- The independent local chaos is the actual radial-removed plane GMC on its chart,
with all measures identified on one common probability-one event. -/
theorem exists_originLateralChartGMC_radial_removed_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ N ∧
      IndepFun (originRadialPath Xc) N P ∧
      ∀ᵐ ω ∂P, N ω = ((M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))).restrict
        (originLateralChart ρ) := by
  obtain ⟨N, hN, hi, heq⟩ := exists_originLateralChartGMC_reinserted_measure_identity
    P X Xc hX hc hm hcont ρ γ hρ hγ hγ2 M hM
  refine ⟨N, hN, hi, ?_⟩
  filter_upwards [heq] with ω hω
  have hcancel := originLateralReinsertedMeasure_removal ρ γ hρ (originRadialPath Xc ω)
    (N ω) (hN.2.1 ω)
  rw [hω, ← restrict_withDensity (isOpen_originLateralChart ρ).measurableSet] at hcancel
  exact hcancel.symm

end DOZZ.Proofs
