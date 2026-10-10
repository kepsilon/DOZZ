/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.HigherScales
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Higher reference moments prevent loss of the first moment in the GMC limit. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A bounded higher moment gives uniform absolute continuity of the first-moment integrals.
The restricted Holder estimate retains the strictly positive measure exponent. -/
theorem gmc_unifIntegrable_of_higher_moment
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ι → Ω → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) P)
    (q : ℝ) (hq : 1 < q) (C : ℝ≥0∞) (hC : C < ∞)
    (hbound : ∀ i, ∫⁻ ω, ‖F i ω‖ₑ ^ q ∂P ≤ C) :
    UnifIntegrable F 1 P := by
  have hq0 : 0 < q := by linarith
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith)
  have ha : 0 < 1 - 1 / q := by
    have h := (div_lt_one hq0).mpr hq
    linarith
  have hnorm (i : ι) : eLpNorm (F i) (ENNReal.ofReal q) P ≤ C ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq0).ne'
      ENNReal.ofReal_ne_top (hF i), ENNReal.toReal_ofReal hq0.le]
    exact ENNReal.rpow_le_rpow (hbound i) (by positivity)
  have hscale : Tendsto (fun ε : ℝ≥0∞ => C ^ (1 / q) * ε ^ (1 - 1 / q))
      (𝓝 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := C ^ (1 / q))
      ((ENNReal.continuous_rpow_const (y := 1 - 1 / q)).tendsto (0 : ℝ≥0∞))
      (Or.inr (ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1 / q) hC.ne).ne)
    rw [ENNReal.zero_rpow_of_pos ha, mul_zero] at h
    exact h
  apply UnifIntegrable.mk_iff.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
  · intro ε
    exact zero_le
  · intro ε
    refine iSup_le fun i => iSup_le fun s => iSup_le fun _hs => iSup_le fun hε => ?_
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s) hqE (hF i).restrict
    simp only [ENNReal.toReal_one, div_one, ENNReal.toReal_ofReal hq0.le,
      Measure.restrict_apply_univ] at h
    exact h.trans (mul_le_mul'
      ((eLpNorm_restrict_le (F i) (ENNReal.ofReal q) P s).trans (hnorm i))
      (ENNReal.rpow_le_rpow hε ha.le))

/-- Convergence in measure and a bounded higher moment preserve expectations. -/
theorem gmc_integral_limit_of_higher_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (G : Ω → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hconv : TendstoInMeasure P F atTop G)
    (q : ℝ) (hq : 1 < q) (C : ℝ≥0∞) (hC : C < ∞)
    (hbound : ∀ n, ∫⁻ ω, ‖F n ω‖ₑ ^ q ∂P ≤ C) :
    Integrable G P ∧ Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, G ω ∂P)) := by
  have hui := gmc_unifIntegrable_of_higher_moment P F hF q hq C hC hbound
  have hq0 : 0 < q := by linarith
  have hnorm (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal q) P < ∞ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq0).ne'
      ENNReal.ofReal_ne_top (hF n), ENNReal.toReal_ofReal hq0.le]
    exact (ENNReal.rpow_le_rpow (hbound n) (by positivity)).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hC.ne)
  have hmem (n : ℕ) : MemLp (F n) 1 P := by
    have hhigh : MemLp (F n) (ENNReal.ofReal q) P := hnorm n
    exact hhigh.mono_exponent (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith))
  have hUI : UniformIntegrable F 1 P := by
    refine ⟨hui, ?_⟩
    let B := (C ^ (1 / q)).toNNReal
    have hB : (B : ℝ≥0∞) = C ^ (1 / q) := ENNReal.coe_toNNReal
      (ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1 / q) hC.ne).ne
    refine ⟨B, fun n => ?_⟩
    rw [hB]
    have hhigh : eLpNorm (F n) (ENNReal.ofReal q) P ≤ C ^ (1 / q) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq0).ne'
        ENNReal.ofReal_ne_top (hF n), ENNReal.toReal_ofReal hq0.le]
      exact ENNReal.rpow_le_rpow (hbound n) (by positivity)
    exact ((eLpNorm_le_eLpNorm_of_exponent_le
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith))).trans hhigh)
  have hG := hUI.integrable_of_tendstoInMeasure hconv
  refine ⟨hG, ?_⟩
  apply tendsto_integral_of_L1' G (Eventually.of_forall (fun n => (hmem n).integrable le_rfl))
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hF
    (memLp_one_iff_integrable.mpr hG) hui hconv


/-- There is always an order above one and below the sharp critical value at a subcritical
charge. This is the order used to retain the first moment in the limiting chaos. -/
theorem gmc_subcritical_higher_order_exists {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 1 < q ∧ q < 4 / γ ^ 2 := by
  have hsq : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hc : 1 < 4 / γ ^ 2 := (lt_div_iff₀ hsq).mpr (by nlinarith)
  exact ⟨(1 + 4 / γ ^ 2) / 2, by linarith, by linarith⟩

/-- The open-ball continuous approximants retain their exact reference expectations for any GMC
version. Higher cutoff moments supply Vitali convergence, rather than a hypothesis asserting that
the limiting first moment is already known. -/
theorem gmc_reference_ball_approx_expected_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, openBallApprox 0 R k x ∂M ω) ∂P =
      ∫⁻ x, ENNReal.ofReal (openBallApprox 0 R k x) ∂gmcReferenceMeasure := by
  let _ := hX.1
  obtain ⟨Xc, hXc, hlimit⟩ := hM.2
  obtain ⟨q, hq, hcrit⟩ := gmc_subcritical_higher_order_exists hγ hγ2
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform
    P X hX Xc hXc γ q hγ hq hcrit hR hRsmall
  let f : BoundedContinuousFunction ℂ ℝ := openBallApprox 0 R k
  let F : ℕ → Ω → ℝ := fun n ω => ∫ x, f x ∂regularizedGMC P Xc γ n ω
  let G : Ω → ℝ := fun ω => ∫ x, f x ∂M ω
  have hf0 (x : ℂ) : 0 ≤ f x := (openBallApproxFun_bounds 0 R k x).1
  have hF0 (n : ℕ) (ω : Ω) : 0 ≤ F n ω := integral_nonneg hf0
  have hG0 (ω : Ω) : 0 ≤ G ω := integral_nonneg hf0
  have hF (n : ℕ) : AEMeasurable (F n) P := by
    have hzero : ∀ x, x ∉ Metric.closedBall (0 : ℂ) R → f x = 0 :=
      boundedContinuousFunction_eq_zero_off_tsupport_subset f (Metric.closedBall 0 R)
        (openBallApprox_tsupport_subset 0 R k)
    have hunit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1 := by
      intro x hx
      have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      linarith
    exact regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ n
      (Metric.closedBall 0 R) Metric.isClosed_closedBall.measurableSet hunit
        f f.continuous.measurable hzero
  have hconv : TendstoInMeasure P F atTop G :=
    (hlimit f).comp tendsto_natCast_atTop_atTop
  have hmoment (n : ℕ) : (∫⁻ ω, ‖F n ω‖ₑ ^ q ∂P) ≤ C := by
    calc
      (∫⁻ ω, ‖F n ω‖ₑ ^ q ∂P) ≤
          gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball 0 R) q := by
        apply lintegral_mono_ae
        filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hfin
        let _ := hfin
        rw [Real.enorm_of_nonneg (hF0 n ω)]
        exact ENNReal.rpow_le_rpow
          (gmc_ball_approx_ofReal_integral_le_mass (regularizedGMC P Xc γ n ω) 0 R k)
          (by linarith)
      _ ≤ C := hbound n (Nat.cast_nonneg n)
  obtain ⟨hGint, hmeans⟩ := gmc_integral_limit_of_higher_moment P F G
    (fun n => (hF n).aestronglyMeasurable) hconv q hq C hC hmoment
  let a : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure
  have ha : a < ∞ := by
    let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
    have hint := f.integrable (μ := gmcReferenceMeasure)
    change (∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure) < ∞
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)]
    exact ENNReal.ofReal_lt_top
  have hE (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) = a := by
    calc
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) =
          ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (f x) ∂regularizedGMC P Xc γ n ω ∂P := by
        apply lintegral_congr_ae
        filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hfin
        let _ := hfin
        exact ofReal_integral_eq_lintegral_ofReal
          (f.integrable (μ := regularizedGMC P Xc γ n ω)) (ae_of_all _ hf0)
      _ = a := regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ n _
        (ENNReal.measurable_ofReal.comp f.continuous.measurable)
  have hFint (n : ℕ) : Integrable (F n) P := by
    refine ⟨(hF n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hF0 n)), hE n]
    exact ha
  have hmeanEq (n : ℕ) : (∫ ω, F n ω ∂P) = a.toReal := by
    have h := ofReal_integral_eq_lintegral_ofReal (hFint n) (ae_of_all _ (hF0 n))
    rw [hE n] at h
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hF0 n))] using ht
  have hGmean : (∫ ω, G ω ∂P) = a.toReal :=
    tendsto_nhds_unique hmeans (by simpa only [hmeanEq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a.toReal) atTop (𝓝 a.toReal)))
  rw [← ofReal_integral_eq_lintegral_ofReal hGint (ae_of_all _ hG0), hGmean]
  exact ENNReal.ofReal_toReal ha.ne


/-- Nonnegative bounded continuous test integrals of finite random measures are measurable
whenever the random measure is measurable almost everywhere. -/
theorem gmc_nonnegative_test_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : AEMeasurable M P) (hfinite : ∀ ω, IsFiniteMeasure (M ω))
    (f : BoundedContinuousFunction ℂ ℝ) (hf : ∀ x, 0 ≤ f x) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  have h := ((Measure.measurable_lintegral
    (ENNReal.measurable_ofReal.comp f.continuous.measurable)).comp_aemeasurable hM).ennreal_toReal
  apply h.congr
  filter_upwards with ω
  let _ := hfinite ω
  have he := ofReal_integral_eq_lintegral_ofReal (f.integrable (μ := M ω)) (ae_of_all _ hf)
  change (∫⁻ x, ENNReal.ofReal (f x) ∂M ω).toReal = ∫ x, f x ∂M ω
  rw [← he, ENNReal.toReal_ofReal (integral_nonneg hf)]

/-- Every small reference ball has exactly its reference mean under an arbitrary GMC version.
The second limit is dominated by the ball mass, whose first moment was already bounded by Fatou. -/
theorem gmc_reference_ball_expected_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∫⁻ ω, M ω (Metric.ball 0 R) ∂P = gmcReferenceMeasure (Metric.ball 0 R) := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let F : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ENNReal.ofReal (∫ x, openBallApprox 0 R k x ∂M ω)
  have hmeas (k : ℕ) : AEMeasurable (F k) P := ENNReal.measurable_ofReal.comp_aemeasurable
    (gmc_nonnegative_test_integral_aemeasurable P M
      (gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM) hM.1 (openBallApprox 0 R k)
      (fun x => (openBallApproxFun_bounds 0 R k x).1))
  have hdom (k : ℕ) : F k ≤ᵐ[P] fun ω => M ω (Metric.ball 0 R) := by
    filter_upwards with ω
    let _ := hM.1 ω
    exact gmc_ball_approx_ofReal_integral_le_mass (M ω) 0 R k
  obtain ⟨q, hq, hc⟩ := gmc_subcritical_higher_order_exists hγ hγ2
  have hfin : (∫⁻ ω, M ω (Metric.ball 0 R) ∂P) ≠ ∞ := by
    have h := gmc_reference_nonnegative_moment_finite P X hX γ 1 hγ
      (by norm_num) (lt_trans hq hc) M hM hR hRsmall
    change (∫⁻ ω, (M ω (Metric.ball 0 R)) ^ (1 : ℝ) ∂P) < ∞ at h
    simpa only [ENNReal.rpow_one] using h.ne
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (M ω (Metric.ball 0 R))) := by
    filter_upwards with ω
    let _ := hM.1 ω
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (openBallApprox_integral_tendsto 0 R (M ω))
    simpa only [Function.comp_def, F, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hleft := tendsto_lintegral_of_dominated_convergence'
    (fun ω => M ω (Metric.ball 0 R)) hmeas hdom hfin hlim
  have href : Tendsto (fun k : ℕ => ∫⁻ ω, F k ω ∂P) atTop
      (𝓝 (gmcReferenceMeasure (Metric.ball 0 R))) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (openBallApprox_integral_tendsto 0 R gmcReferenceMeasure)
    have he (k : ℕ) : (∫⁻ ω, F k ω ∂P) =
        ENNReal.ofReal (∫ x, openBallApprox 0 R k x ∂gmcReferenceMeasure) := by
      rw [gmc_reference_ball_approx_expected_mass P X hX γ hγ hγ2 M hM hR hRsmall k]
      exact (ofReal_integral_eq_lintegral_ofReal
        ((openBallApprox 0 R k).integrable (μ := gmcReferenceMeasure))
        (ae_of_all _ (fun x => (openBallApproxFun_bounds 0 R k x).1))).symm
    simpa only [Function.comp_def, he, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  exact tendsto_nhds_unique hleft href

/-- The reference intensity on a ball in the unit chart is strictly positive. -/
theorem gmc_reference_ball_intensity_pos {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    0 < gmcReferenceMeasure (Metric.ball (0 : ℂ) R) := by
  have he := gmcReferenceMeasure_restrict_unit_chart (Metric.ball (0 : ℂ) R)
    Metric.isOpen_ball.measurableSet (fun x hx => by
      have h : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact h.le.trans hR1)
  have hv := congrArg (fun μ : Measure ℂ => μ Set.univ) he
  simp only [Measure.restrict_apply_univ] at hv
  rw [hv, Complex.volume_ball]
  have hr : 0 < ENNReal.ofReal R := ENNReal.ofReal_pos.mpr hR
  exact ENNReal.mul_pos (pow_ne_zero 2 hr.ne') (ENNReal.coe_pos.mpr NNReal.pi_pos).ne'

/-- Every positive power of a reference ball has positive expectation. The argument requires
positive mean, rather than an unproved almost-sure positivity claim. -/
theorem gmc_reference_ball_positive_moment_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R p : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hp : 0 < p) :
    0 < gmcMassMoment P M (Metric.ball 0 R) p := by
  have hm : AEMeasurable (fun ω => M ω (Metric.ball 0 R)) P :=
    (Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp_aemeasurable
      (gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM)
  have hpow : AEMeasurable (fun ω => (M ω (Metric.ball 0 R)) ^ p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hm
  apply pos_iff_ne_zero.mpr
  intro hz
  have he : (fun ω => (M ω (Metric.ball 0 R)) ^ p) =ᵐ[P] 0 :=
    (lintegral_eq_zero_iff' hpow).mp hz
  have hzero : (fun ω => M ω (Metric.ball 0 R)) =ᵐ[P] 0 := by
    filter_upwards [he] with ω hω
    exact (ENNReal.rpow_eq_zero_iff_of_pos hp).mp hω
  have hmean : (∫⁻ ω, M ω (Metric.ball 0 R) ∂P) = 0 := by
    simpa only [Pi.zero_apply, lintegral_zero] using lintegral_congr_ae hzero
  rw [gmc_reference_ball_expected_mass P X hX γ hγ hγ2 M hM hR hRsmall] at hmean
  exact (gmc_reference_ball_intensity_pos hR (by linarith)).ne' hmean



/-- At nonpositive orders a finite mass cannot have zero extended power. This includes zero
mass at negative order, whose extended power is infinite. -/
theorem gmc_finite_mass_nonpositive_power_ne_zero (μ : Measure ℂ) [IsFiniteMeasure μ]
    (A : Set ℂ) {p : ℝ} (hp : p ≤ 0) : ENNReal.rpow (μ A) p ≠ 0 := by
  intro hzero
  rcases ENNReal.rpow_eq_zero_iff.mp hzero with h | h
  · exact (not_lt_of_ge hp) h.2
  · exact (measure_ne_top μ A) h.1

/-- Reference moments are positive at every real order, without presupposing that any
negative moment is finite. -/
theorem gmc_reference_ball_moment_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (p : ℝ) :
    0 < gmcMassMoment P M (Metric.ball 0 R) p := by
  let _ := hX.1
  by_cases hp : 0 < p
  · exact gmc_reference_ball_positive_moment_pos P X hX γ hγ hγ2 M hM hR hRsmall hp
  · have hm : AEMeasurable (fun ω => M ω (Metric.ball 0 R)) P :=
      (Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp_aemeasurable
        (gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM)
    have hpow : AEMeasurable (fun ω => (M ω (Metric.ball 0 R)) ^ p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hm
    apply pos_iff_ne_zero.mpr
    intro hz
    have he : (fun ω => (M ω (Metric.ball 0 R)) ^ p) =ᵐ[P] 0 :=
      (lintegral_eq_zero_iff' hpow).mp hz
    have hfalse : ∀ᵐ ω ∂P, False := by
      filter_upwards [he] with ω hω
      let _ := hM.1 ω
      exact gmc_finite_mass_nonpositive_power_ne_zero (M ω) (Metric.ball 0 R) (le_of_not_gt hp) hω
    obtain ⟨ω, hω⟩ := hfalse.exists
    exact hω





end DOZZ.Proofs
