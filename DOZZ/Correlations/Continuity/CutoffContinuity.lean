/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Assembly.CircleUniformL1
public import DOZZ.Correlations.Continuity.ChartTests
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open DOZZ.Assembly
namespace DOZZ.Proofs

/-- Fixed-cutoff Wick test integrals are continuous in the charge on any finite
reference measure. The spatial domination uses the mean-one normalization. -/
theorem admissibleCutoffIntegral_L1_continuous_finite_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hν : logRegularizationReference U dens Set.univ ≠ ⊤)
    (r : ℝ) (hr : Real.exp (-r) ≤ ε₀)
    (L : ℝ) (g : ℂ → ℝ) (hg : Measurable g) (hgL : ∀ x, |g x| ≤ L)
    (γ₀ : ℝ) :
    Tendsto (fun γ => ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r g ω -
        admissibleCutoffIntegral P U dens Y γ₀ r g ω| ∂P) (𝓝 γ₀) (𝓝 0) := by
  set ε := Real.exp (-r) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  let D : ℝ → ℂ → ℝ≥0∞ := fun γ x => ∫⁻ ω, ENNReal.ofReal
    |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
      Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)| ∂P
  have hv : Measurable (fun x => ∫ ω', Y ω' ε x ^ 2 ∂P) := by
    have heq : (fun x => ∫ ω', Y ω' ε x ^ 2 ∂P) =
        fun x => gaussianVariance P (fun ω => Y ω ε x) := by
      funext x
      unfold gaussianVariance gaussianCovariance
      simp only [pow_two]
    rw [heq]
    exact admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε
  have hfield : Measurable (fun q : Ω × ℂ => Y q.1 ε q.2) := hY.measurableAtScale ε
  have hjoint (γ : ℝ) : Measurable (fun q : ℂ × Ω => ENNReal.ofReal
      |Real.exp (γ * Y q.2 ε q.1 - γ ^ 2 / 2 * ∫ ω', Y ω' ε q.1 ^ 2 ∂P) -
        Real.exp (γ₀ * Y q.2 ε q.1 - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε q.1 ^ 2 ∂P)|) := by
    have h1 : Measurable (fun q : ℂ × Ω => Y q.2 ε q.1) := hfield.comp measurable_swap
    have h2 : Measurable (fun q : ℂ × Ω => ∫ ω', Y ω' ε q.1 ^ 2 ∂P) := hv.comp measurable_fst
    fun_prop
  have hDmeas (γ : ℝ) : Measurable (D γ) := (hjoint γ).lintegral_prod_right'
  have hDle (γ : ℝ) (x : ℂ) : D γ x ≤ 2 := by
    calc D γ x ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (γ * Y ω ε x - γ ^ 2 / 2 *
          ∫ ω', Y ω' ε x ^ 2 ∂P)) + ENNReal.ofReal (Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 *
          ∫ ω', Y ω' ε x ^ 2 ∂P))) ∂P := by
          apply lintegral_mono
          intro ω
          beta_reduce
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          rw [abs_le]
          constructor <;> linarith [Real.exp_pos (γ * Y ω ε x - γ ^ 2 / 2 *
            ∫ ω', Y ω' ε x ^ 2 ∂P), Real.exp_pos (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 *
            ∫ ω', Y ω' ε x ^ 2 ∂P)]
      _ = 1 + 1 := by
          simp only [ofReal_exp_eq_admissibleLogWickWeight]
          rw [lintegral_add_left (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY γ
            ε x), lintegral_admissibleLogWickWeight P U dens ε₀ Y hY γ ε hε hr x,
            lintegral_admissibleLogWickWeight P U dens ε₀ Y hY γ₀ ε hε hr x]
      _ = 2 := by norm_num
  -- the expected difference is bounded by the integrated weight difference
  have hbound (γ : ℝ) : ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r g ω -
      admissibleCutoffIntegral P U dens Y γ₀ r g ω| ∂P ≤
      ENNReal.ofReal L * ∫⁻ x, D γ x ∂logRegularizationReference U dens := by
    have hpt (ω : Ω) : ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r g ω -
        admissibleCutoffIntegral P U dens Y γ₀ r g ω| ≤
        ENNReal.ofReal L * ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂logRegularizationReference U dens := by
      unfold admissibleCutoffIntegral
      refine (ofReal_abs_integral_sub_le_lintegral _ _ _
        (admissibleCutoff_integrand_measurable P U dens ε₀ Y hY γ r g hg ω)
        (admissibleCutoff_integrand_measurable P U dens ε₀ Y hY γ₀ r g hg ω)).trans ?_
      have hFx : Measurable (fun x => ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|) :=
        (hjoint γ).comp (f := fun x : ℂ => (x, ω)) (measurable_id.prodMk measurable_const)
      rw [← lintegral_const_mul _ hFx]
      apply lintegral_mono
      intro x
      beta_reduce
      rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hgL x)) _
    have hint : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂logRegularizationReference U dens ∂P =
        ∫⁻ x, D γ x ∂logRegularizationReference U dens := by
      apply lintegral_lintegral_swap
      exact ((hjoint γ).comp measurable_swap).aemeasurable
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal L * ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂logRegularizationReference U dens ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal L * ∫⁻ ω, ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂logRegularizationReference U dens ∂P := by
          have hΦ : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal
              |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
                Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
              ∂logRegularizationReference U dens) :=
            ((hjoint γ).comp measurable_swap).lintegral_prod_right'
          rw [lintegral_const_mul _ hΦ]
      _ = _ := by rw [hint]
  have hDlim : Tendsto (fun γ => ∫⁻ x, D γ x ∂logRegularizationReference U dens)
      (𝓝 γ₀) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := logRegularizationReference U dens) (f := fun _ => 0) (fun _ => 2)
      (Eventually.of_forall hDmeas) (Eventually.of_forall fun γ => ae_of_all _ (hDle γ))
      (by
        rw [lintegral_const]
        exact ENNReal.mul_ne_top (by norm_num) hν)
      (ae_of_all _ fun x => admissible_wick_weight_L1_continuous P U dens ε₀ Y hY ε hε hr x γ₀)
    simpa using h
  have hmul : Tendsto (fun γ => ENNReal.ofReal L *
      ∫⁻ x, D γ x ∂logRegularizationReference U dens) (𝓝 γ₀) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) hDlim
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    hbound


/-- A bounded measurable spatial test family continuous pointwise in its parameter
can vary simultaneously with the charge in the circle cutoff integral. -/
theorem regularizedGMC_testFamily_L1_continuous
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (r : ℝ) (hr : 0 ≤ r) (γ : T → ℝ) (hγ : Continuous γ)
    (f : T → ℂ → ℝ) (hf : ∀ q, Measurable (f q))
    (hfc : ∀ x, Continuous (fun q => f q x)) (L : ℝ)
    (hL : ∀ q x, |f q x| ≤ L) (q₀ : T) :
    Tendsto (fun q => ∫⁻ ω, ENNReal.ofReal
      |∫ x, f q x ∂regularizedGMC P Xc (γ q) r ω -
        ∫ x, f q₀ x ∂regularizedGMC P Xc (γ q₀) r ω| ∂P) (𝓝 q₀) (𝓝 0) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hν : logRegularizationReference Set.univ circleDensity Set.univ ≠ ⊤ := by
    rw [logRegularizationReference_univ_circleDensity]
    exact gmcReferenceMeasure_univ_ne_top
  have hfixed := admissibleCutoffIntegral_L1_continuous_finite_reference P Set.univ
    circleDensity 1 (circleRegularization Xc) (circleRegularization_admissible P X hX Xc hXc)
    hν r (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)) L (f q₀) (hf q₀) (hL q₀) (γ q₀)
  have hfixed' : Tendsto (fun q => ∫⁻ ω, ENNReal.ofReal
      |∫ x, f q₀ x ∂regularizedGMC P Xc (γ q) r ω -
        ∫ x, f q₀ x ∂regularizedGMC P Xc (γ q₀) r ω| ∂P) (𝓝 q₀) (𝓝 0) := by
    simpa only [Function.comp_def, integral_regularizedGMC_eq_admissibleCutoffIntegral P X hX Xc hXc]
      using hfixed.comp (hγ.tendsto q₀)
  have htest : Tendsto (fun q => ∫⁻ x, ENNReal.ofReal |f q x - f q₀ x|
      ∂gmcReferenceMeasure) (𝓝 q₀) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := gmcReferenceMeasure) (f := fun _ => 0) (fun _ => ENNReal.ofReal (2 * L))
      (Eventually.of_forall fun q => ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp ((hf q).sub (hf q₀))))
      (Eventually.of_forall fun q => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
        ((abs_sub _ _).trans (by linarith [hL q x, hL q₀ x])))
      (by
        rw [lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top gmcReferenceMeasure_univ_ne_top)
      (ae_of_all _ fun x => by
        have hh := ENNReal.tendsto_ofReal (((hfc x).tendsto q₀).sub_const (f q₀ x) |>.abs)
        simpa only [Function.comp_apply, Pi.sub_apply, sub_self, abs_zero, ENNReal.ofReal_zero] using hh)
    simpa only [Function.comp_apply, Pi.sub_apply, lintegral_zero] using h
  have hvar (q : T) : ∫⁻ ω, ENNReal.ofReal
      |∫ x, f q x ∂regularizedGMC P Xc (γ q) r ω -
        ∫ x, f q₀ x ∂regularizedGMC P Xc (γ q) r ω| ∂P ≤
        ∫⁻ x, ENNReal.ofReal |f q x - f q₀ x| ∂gmcReferenceMeasure := by
    calc _ ≤ ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f q x - f q₀ x|
          ∂regularizedGMC P Xc (γ q) r ω ∂P :=
        lintegral_mono fun ω => ofReal_abs_integral_sub_le_lintegral _ _ _ (hf q) (hf q₀)
      _ = _ := regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc (γ q) r _
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp ((hf q).sub (hf q₀))))
  have hsum := htest.add hfixed'
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun q => ?_)
  exact (lintegral_ofReal_abs_sub_le_add P _
    (fun ω => ∫ x, f q₀ x ∂regularizedGMC P Xc (γ q) r ω) _
    (regularizedGMC_integral_measurable P X hX Xc hXc _ r _ (hf q)).aemeasurable
    (regularizedGMC_integral_measurable P X hX Xc hXc _ r _ (hf q₀)).aemeasurable).trans
      (add_le_add (hvar q) le_rfl)

/-- The bounded real test against the original circle cutoff measure. -/
noncomputable def continuityCutoffTest {N : ℕ} (partition : GMCChartPartition)
    (r : ℝ) (c : ContinuityCoulombParameter N) (x : ℂ) : ℝ :=
  continuityFiniteCutoffTest partition r c x + continuityInfinityCutoffTest partition r c x⁻¹

theorem continuityCutoffTest_nonneg {N : ℕ} (partition : GMCChartPartition)
    (r : ℝ) (c : ContinuityCoulombParameter N) (x : ℂ) :
    0 ≤ continuityCutoffTest partition r c x :=
  add_nonneg (continuityFiniteCutoffTest_nonneg _ _ _ _)
    (continuityInfinityCutoffTest_nonneg _ _ _ _)

theorem continuityCutoffTest_measurable {N : ℕ} (partition : GMCChartPartition)
    (r : ℝ) (c : ContinuityCoulombParameter N) : Measurable (continuityCutoffTest partition r c) :=
  ((continuityFiniteCutoffTest_continuous partition r).comp
    (continuous_const.prodMk continuous_id)).measurable.add
    (((continuityInfinityCutoffTest_continuous partition r).comp
      (continuous_const.prodMk continuous_id)).measurable.comp measurable_inv)

/-- The real part of the cutoff mass `DOZZ.regularizedCoulombMass` is exactly the integral of its
bounded single-chart real test. This identity also respects the integral totalizations. -/
theorem regularizedCoulombMass_real_eq_integral_test
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition) (r : ℝ) (c : ContinuityCoulombParameter N) (ω : Ω) :
    (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω).toReal =
      ∫ x, continuityCutoffTest partition r c x ∂regularizedGMC P Xc c.1 r ω := by
  rw [regularizedCoulombMass_eq_lintegral P X hX Xc hXc]
  simp_rw [coulombCutoffWeight_eq_ofReal_continuityCutoffTest]
  change (∫⁻ x, ENNReal.ofReal (continuityCutoffTest partition r c x)
    ∂regularizedGMC P Xc c.1 r ω).toReal = _
  have h := integral_toReal
    (ENNReal.measurable_ofReal.comp (continuityCutoffTest_measurable partition r c)).aemeasurable
    (ae_of_all (regularizedGMC P Xc c.1 r ω) (fun _ => ENNReal.ofReal_lt_top))
  simpa only [Function.comp_apply, ENNReal.toReal_ofReal (continuityCutoffTest_nonneg partition r c _)] using h.symm

/-- At a fixed cutoff, the actual chartwise Coulomb mass is continuous in all
couplings, roots and charges in `L¹(P)` on every compact parameter set. -/
theorem regularizedCoulombMass_L1_continuous_on_compact
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition) (r : ℝ) (hr : 0 ≤ r)
    (S : Set (ContinuityCoulombParameter N)) (hS : IsCompact S) (c₀ : S) :
    Tendsto (fun c : S => ∫⁻ ω, ENNReal.ofReal
      |(regularizedCoulombMass P Xc c.val.1 partition c.val.2.2.1 c.val.2.1 c.val.2.2.2 r ω).toReal -
        (regularizedCoulombMass P Xc c₀.val.1 partition c₀.val.2.2.1 c₀.val.2.1 c₀.val.2.2.2 r ω).toReal|
        ∂P) (𝓝 c₀) (𝓝 0) := by
  obtain ⟨L, _hL0, hL⟩ := continuityCutoffTests_uniform_bound partition r S hS
  have hfc : ∀ x, Continuous (fun c : S => continuityCutoffTest partition r c.val x) := by
    intro x
    exact ((continuityFiniteCutoffTest_continuous partition r).comp
      (continuous_subtype_val.prodMk continuous_const)).add
      ((continuityInfinityCutoffTest_continuous partition r).comp
        (continuous_subtype_val.prodMk continuous_const))
  have hb : ∀ c : S, ∀ x, |continuityCutoffTest partition r c.val x| ≤ 2 * L := by
    intro c x
    exact (abs_add_le _ _).trans (by linarith [(hL c.val c.property x).1,
      (hL c.val c.property x⁻¹).2])
  have h := regularizedGMC_testFamily_L1_continuous P X hX Xc hXc r hr
    (fun c : S => c.val.1) (continuous_fst.comp continuous_subtype_val)
    (fun c : S => continuityCutoffTest partition r c.val)
    (fun c => continuityCutoffTest_measurable partition r c.val) hfc (2 * L) hb c₀
  simpa only [regularizedCoulombMass_real_eq_integral_test P X hX Xc hXc] using h

/-- The actual extended cutoff mass is measurable for every fixed parameter. -/
theorem continuity_regularizedCoulombMass_measurable
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition) (r : ℝ) (c : ContinuityCoulombParameter N) :
    Measurable (fun ω => regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω) := by
  have h := (Measure.measurable_lintegral
    (measurable_coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r)).comp
      (regularizedGMC_measurable P X hX Xc hXc c.1 r)
  simpa only [Function.comp_def, regularizedCoulombMass_eq_lintegral P X hX Xc hXc] using h

/-- The bounded chart tests make the actual cutoff mass finite almost surely. -/
theorem continuity_regularizedCoulombMass_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition) (r : ℝ) (c : ContinuityCoulombParameter N) :
    ∀ᵐ ω ∂P, regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω ≠ ⊤ := by
  obtain ⟨L, _hL0, hL⟩ := continuityCutoffTests_uniform_bound partition r {c} isCompact_singleton
  have hb (x : ℂ) : continuityCutoffTest partition r c x ≤ 2 * L :=
    (le_abs_self _).trans ((abs_add_le _ _).trans (by
      linarith [(hL c rfl x).1, (hL c rfl x⁻¹).2]))
  filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc c.1 r] with ω hω
  let _ : IsFiniteMeasure (regularizedGMC P Xc c.1 r ω) := hω
  rw [regularizedCoulombMass_eq_lintegral P X hX Xc hXc]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 * L))
    (measure_ne_top (regularizedGMC P Xc c.1 r ω) Set.univ)) ?_
  calc _ ≤ ∫⁻ _x, ENNReal.ofReal (2 * L) ∂regularizedGMC P Xc c.1 r ω :=
      lintegral_mono fun x => by
        rw [coulombCutoffWeight_eq_ofReal_continuityCutoffTest]
        exact ENNReal.ofReal_le_ofReal (hb x)
    _ = _ := lintegral_const _

end DOZZ.Proofs
