/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.WickReinsertion
public import DOZZ.GMC.CompatibleAdmissibleGMCUnique

/-!
# Uniform compact changes of a Wick test

The mean-one Wick identity controls cutoff integrals uniformly in the regularization
scale. Consequently uniform changes of a test on a common compact support can be passed
through the chaos limit. This is the finite radial-factor step in local reinsertion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions InnerProductSpace RealInnerProductSpace

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- The cutoff expectation controls a uniform change of compact continuous tests, at
every allowed cutoff, with exactly the reference mass of their common support. -/
theorem regularizedLogChaosTestMass_L1_test_difference_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (γ r : ℝ)
    (hr : Real.exp (-r) ≤ ε₀)
    (f g : BoundedContinuousFunction ℂ ℝ)
    (hfK : tsupport (f : ℂ → ℝ) ⊆ K) (hgK : tsupport (g : ℂ → ℝ) ⊆ K)
    (δ : ℝ) (hδ : ∀ x, |f x - g x| ≤ δ) :
    ∫⁻ ω, ENNReal.ofReal |regularizedLogChaosTestMass P U dens Y γ r ω f -
      regularizedLogChaosTestMass P U dens Y γ r ω g| ∂P ≤
        ENNReal.ofReal δ * logRegularizationReference U dens K := by
  have hf0 : ∀ x ∉ K, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hfK h))
  have hg0 : ∀ x ∉ K, g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hgK h))
  have hfI := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU γ r hr
    ‖f‖ f f.continuous.measurable (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) hf0
  have hgI := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU γ r hr
    ‖g‖ g g.continuous.measurable (fun x => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x) hg0
  have hb : ∀ᵐ ω ∂P, ENNReal.ofReal |regularizedLogChaosTestMass P U dens Y γ r ω f -
      regularizedLogChaosTestMass P U dens Y γ r ω g| ≤
        chartMass P U dens K Y γ r (fun x => |f x - g x|) ω := by
    filter_upwards [hfI, hgI] with ω hfω hgω
    unfold regularizedLogChaosTestMass
    rw [← integral_sub hfω hgω]
    have heq : (fun x => f x * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
        ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) -
        g x * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
        ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)) =
        fun x => (f x - g x) * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
          ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) := by
      funext x
      ring
    rw [heq]
    have he := enorm_integral_le_lintegral_enorm (μ := logRegularizationReference U dens)
      (fun x => (f x - g x) * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
        ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P))
    simp only [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at he
    rw [lintegral_cutoff_integrand_eq_chartMass P U dens Y K γ r _ (fun x => abs_nonneg _)
      (fun x hx => by rw [hf0 x hx, hg0 x hx, sub_self, abs_zero]) ω] at he
    exact he
  exact (lintegral_mono_ae hb).trans
    (lintegral_chartMass_le P U dens ε₀ Y hY K γ r hr δ
      (fun x => |f x - g x|)
      (continuous_abs.measurable.comp (f.continuous.measurable.sub g.continuous.measurable)) hδ)

/-- Uniformly converging tests on a common compact chart have vanishing cutoff error
in expected absolute value, even though the cutoff varies with the test. -/
theorem tendsto_regularizedLogChaosTestMass_L1_test_difference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (γ : ℝ)
    (f : ℝ → BoundedContinuousFunction ℂ ℝ) (g : BoundedContinuousFunction ℂ ℝ)
    (hfK : ∀ r, tsupport (f r : ℂ → ℝ) ⊆ K) (hgK : tsupport (g : ℂ → ℝ) ⊆ K)
    (hfg : ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop, ∀ x, |f r x - g x| ≤ δ) :
    Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal
      |regularizedLogChaosTestMass P U dens Y γ r ω (f r) -
        regularizedLogChaosTestMass P U dens Y γ r ω g| ∂P) atTop (𝓝 0) := by
  have hσ := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  let σ := logRegularizationReference U dens K
  have hσ' : σ ≠ ⊤ := hσ
  have hc : ∀ᶠ r : ℝ in atTop, Real.exp (-r) ≤ ε₀ := by
    filter_upwards [eventually_ge_atTop (-Real.log ε₀)] with r hr
    calc Real.exp (-r) ≤ Real.exp (Real.log ε₀) := Real.exp_le_exp.mpr (by linarith only [hr])
      _ = ε₀ := Real.exp_log hY.cutoffPositive
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  by_cases hηtop : η = ⊤
  · exact ⟨0, fun _ _ => hηtop ▸ le_top⟩
  have hηr := ENNReal.toReal_pos hη.ne' hηtop
  let δ := η.toReal / (σ.toReal + 1)
  have hδ : 0 < δ := div_pos hηr (by positivity)
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((hfg δ hδ).and hc)
  refine ⟨R, fun r hr => ?_⟩
  have hb := regularizedLogChaosTestMass_L1_test_difference_le P U dens ε₀ Y hY K hK hKU
    γ r (hR r hr).2 (f r) g (hfK r) hgK δ ((hR r hr).1)
  apply hb.trans
  change ENNReal.ofReal δ * σ ≤ η
  rw [← ENNReal.ofReal_toReal hσ', ← ENNReal.ofReal_mul hδ.le,
    ← ENNReal.ofReal_toReal hηtop]
  apply ENNReal.ofReal_le_ofReal
  calc δ * σ.toReal ≤ δ * (σ.toReal + 1) :=
         mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le
    _ = η.toReal := div_mul_cancel₀ _ (by positivity : σ.toReal + 1 ≠ 0)

/-- A uniformly varying compact test may replace the fixed test in an admissible GMC
limit. The result uses only the mean-one finite Wick identity. -/
theorem regularizedLogChaosTestMass_varying_test_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ)
    (N : Ω → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : ℝ → BoundedContinuousFunction ℂ ℝ) (g : BoundedContinuousFunction ℂ ℝ)
    (hfK : ∀ r, tsupport (f r : ℂ → ℝ) ⊆ K) (hgK : tsupport (g : ℂ → ℝ) ⊆ K)
    (hfg : ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop, ∀ x, |f r x - g x| ≤ δ) :
    TendstoInMeasure P (fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω (f r)) atTop
      (fun ω => ∫ x, g x ∂N ω) := by
  let F : ℝ → Ω → ℝ := fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω (f r)
  let G : ℝ → Ω → ℝ := fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω g
  let H : Ω → ℝ := fun ω => ∫ x, g x ∂N ω
  have hmF (r : ℝ) : Measurable (F r) :=
    admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r (f r) (f r).continuous.measurable
  have hmG (r : ℝ) : Measurable (G r) :=
    admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r g g.continuous.measurable
  have hl1 := tendsto_regularizedLogChaosTestMass_L1_test_difference P U dens ε₀ Y hY
    K hK hKU γ f g hfK hgK hfg
  have hz : TendstoInMeasure P (fun r ω => G r ω - F r ω) atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P _ _
      (fun r => ((hmG r).sub (hmF r)).aestronglyMeasurable) aestronglyMeasurable_const
    change Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal |G r ω - F r ω - 0| ∂P) atTop (𝓝 0)
    simpa only [sub_zero, abs_sub_comm] using hl1
  have hg : TendstoInMeasure P G atTop H :=
    hN.2.2.2 g (hK.of_isClosed_subset (isClosed_tsupport _) hgK) (hgK.trans hKU)
  have ht := tendstoInMeasure_sub P G (fun r ω => G r ω - F r ω) H (fun _ => 0) hg hz
  have heq : (fun r ω => G r ω - (G r ω - F r ω)) = F := by
    funext r ω
    ring
  simpa only [heq, sub_zero] using ht

/-- Exponentiation preserves uniform convergence on a compact set when the limiting
exponent is continuous. Compactness keeps both exponents in one bounded interval. -/
theorem uniform_exp_approx_on_compact
    (K : Set ℂ) (hK : IsCompact K) (F : ℝ → ℂ → ℝ) (G : ℂ → ℝ) (hG : Continuous G)
    (hFG : ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop, ∀ x ∈ K, |F r x - G x| < δ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, ∀ x ∈ K,
      |Real.exp (F r x) - Real.exp (G x)| < η := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hG.norm.continuousOn
  let B := |C| + 1
  have hGB (x : ℂ) (hx : x ∈ K) : |G x| ≤ |C| :=
    (hC (mem_image_of_mem _ hx)).trans (le_abs_self C)
  have huc : UniformContinuousOn Real.exp (Icc (-B) B) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_exp.continuousOn
  intro η hη
  obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  filter_upwards [hFG (min δ 1) (lt_min hδ zero_lt_one)] with r hr x hx
  have hdiff : |F r x - G x| < δ := (hr x hx).trans_le (min_le_left _ _)
  have hFbound : |F r x| ≤ B := by
    calc |F r x| = |(F r x - G x) + G x| := by congr 1; ring
      _ ≤ |F r x - G x| + |G x| := abs_add_le _ _
      _ ≤ 1 + |C| := add_le_add ((hr x hx).le.trans (min_le_right _ _)) (hGB x hx)
      _ = B := by dsimp [B]; ring
  have hFmem : F r x ∈ Icc (-B) B := abs_le.mp hFbound
  have hGmem : G x ∈ Icc (-B) B := abs_le.mp ((hGB x hx).trans (by dsimp [B]; linarith))
  have h := hclose (F r x) hFmem (G x) hGmem (by simpa only [Real.dist_eq] using hdiff)
  simpa only [Real.dist_eq] using h

/-- For every fixed continuous radial path the finite radial factor converges uniformly
on any compact local chart, with its literal Gaussian variance and reference correction. -/
theorem originRadialCutoffReinsertionWeight_uniform_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : γ ≠ 0) (A : TwoSidedPath)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, ∀ x ∈ K,
      |originRadialCutoffReinsertionWeight hc ρ γ r A x -
        originRadialReinsertionWeight ρ γ A x| < η := by
  let F : ℝ → ℂ → ℝ := fun r x =>
    γ * (∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) -
      γ ^ 2 / 2 * gaussianVariance P (originCircleRadialL2 hc ρ x r) -
        2 * |clampedLogRadius ρ x|
  let G : ℂ → ℝ := fun x => γ * A (clampedLogRadius ρ x) - γ * Q γ * |clampedLogRadius ρ x|
  have hG : Continuous G :=
    (continuous_const.mul (A.continuous.comp (continuous_clampedLogRadius ρ hρ))).sub
      (continuous_const.mul (continuous_clampedLogRadius ρ hρ).abs)
  have hFG : ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, ∀ x ∈ K, |F r x - G x| < η := by
    intro η hη
    let δ := η / (|γ| + |γ ^ 2 / 2| + 1)
    have hden : 0 < |γ| + |γ ^ 2 / 2| + 1 := by positivity
    have hδ : 0 < δ := div_pos hη hden
    obtain ⟨ε₁, hε₁, hrad⟩ := integral_circleMeasure_uniform_approx
      (fun z => A (clampedLogRadius ρ z))
      (A.continuous.comp (continuous_clampedLogRadius ρ hρ)) K hK δ hδ
    obtain ⟨ε₂, hε₂, hvar⟩ := originCircleRadialL2_uniform_variance_approx
      P X Xc hX hc ρ hρ K hK hKU δ hδ
    have ht := (tendsto_order.mp Real.tendsto_exp_neg_atTop_nhds_zero).2
      (min ε₁ (min ε₂ ρ)) (lt_min hε₁ (lt_min hε₂ hρ))
    filter_upwards [ht] with r hr x hx
    have hr₁ : Real.exp (-r) ≤ ε₁ := hr.le.trans (min_le_left _ _)
    have hr₂ : Real.exp (-r) ≤ min ε₂ ρ := hr.le.trans (min_le_right _ _)
    have hb₁ : |(∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) -
        A (clampedLogRadius ρ x)| < δ := by
      simpa only [Real.norm_eq_abs] using hrad r hr₁ x hx
    have hb₂ := hvar (Real.exp (-r)) (Real.exp_pos _) hr₂ x hx
    simp only [one_div, Real.log_inv, Real.log_exp, neg_neg] at hb₂
    have hxρ : ρ ≤ ‖x‖ := by
      have hxU : 2 * ρ < ‖x‖ := hKU hx
      linarith only [hxU, hρ]
    have heq : F r x - G x =
        γ * ((∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) - A (clampedLogRadius ρ x)) -
        γ ^ 2 / 2 * (gaussianVariance P (originCircleRadialL2 hc ρ x r) - |Real.log ‖x‖|) := by
      dsimp only [F, G]
      rw [clampedLogRadius_eq ρ x hxρ, abs_neg, gamma_mul_Q_eq γ hγ]
      ring
    rw [heq]
    have htri := abs_sub
      (γ * ((∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) - A (clampedLogRadius ρ x)))
      (γ ^ 2 / 2 * (gaussianVariance P (originCircleRadialL2 hc ρ x r) - |Real.log ‖x‖|))
    rw [abs_mul γ, abs_mul (γ ^ 2 / 2)] at htri
    calc _ ≤ |γ| * |(∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) - A (clampedLogRadius ρ x)| +
          |γ ^ 2 / 2| * |gaussianVariance P (originCircleRadialL2 hc ρ x r) - (|Real.log ‖x‖|)| := htri
      _ ≤ |γ| * δ + |γ ^ 2 / 2| * δ := add_le_add
        (mul_le_mul_of_nonneg_left hb₁.le (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb₂.le (abs_nonneg _))
      _ < (|γ| + |γ ^ 2 / 2| + 1) * δ := by
        calc _ = (|γ| + |γ ^ 2 / 2|) * δ := by ring
          _ < _ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = η := mul_div_cancel₀ _ hden.ne'
  exact uniform_exp_approx_on_compact K hK F G hG hFG

/-- Circle integration is jointly continuous in center and radius for continuous
Banach-valued integrands, by integration over the fixed angular interval. -/
theorem continuous_circleIntegral_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℂ → E) (hF : Continuous F) :
    Continuous (fun p : ℂ × ℝ => ∫ z, F z ∂circleMeasure p.1 p.2) := by
  have hi : Continuous (fun p : ℂ × ℝ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap p.1 (Real.exp (-p.2)) θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    apply hF.comp
    fun_prop [circleMap]
  have heq : (fun p : ℂ × ℝ => ∫ z, F z ∂circleMeasure p.1 p.2) =
      fun p => (2 * Real.pi)⁻¹ •
        ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap p.1 (Real.exp (-p.2)) θ) := by
    funext p
    rw [circleMeasure, integral_smul_measure,
      integral_map (measurable_circleMap p.1 (Real.exp (-p.2))).aemeasurable hF.aestronglyMeasurable,
      ← intervalIntegral.integral_of_le Real.two_pi_pos.le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  rw [heq]
  exact continuous_const.smul hi

/-- The actual radial Hilbert projection varies continuously with every cutoff circle. -/
theorem continuous_originCircleRadialL2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (fun p : ℂ × ℝ => originCircleRadialL2 hc ρ p.1 p.2) :=
  continuous_circleIntegral_banach _ (continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ)

/-- The finite radial factor is continuous in the spatial point for every continuous
radial path, so multiplication by a compact test remains a bounded continuous test. -/
theorem continuous_originRadialCutoffReinsertionWeight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) :
    Continuous (originRadialCutoffReinsertionWeight hc ρ γ r A) := by
  have hR := (continuous_originCircleRadialL2 P X Xc hX hc ρ hρ).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ => r)))
  have hv : Continuous (fun x => gaussianVariance P (originCircleRadialL2 hc ρ x r)) := by
    have heq : (fun x => gaussianVariance P (originCircleRadialL2 hc ρ x r)) =
        fun x => ⟪originCircleRadialL2 hc ρ x r, originCircleRadialL2 hc ρ x r⟫_ℝ := by
      funext x
      unfold gaussianVariance gaussianCovariance
      rw [integral_mul_eq_inner]
    rw [heq]
    exact hR.inner hR
  have ha := (continuous_circleIntegral_of_continuous (fun z => A (clampedLogRadius ρ z))
    (A.continuous.comp (continuous_clampedLogRadius ρ hρ))).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ => r)))
  exact (((ha.const_mul γ).sub (hv.const_mul (γ ^ 2 / 2))).sub
    ((continuous_clampedLogRadius ρ hρ).abs.const_mul 2)).rexp

/-- The literal finite radial-weighted compact test, with no change of its variance. -/
noncomputable def originRadialCutoffWeightedTest
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    BoundedContinuousFunction ℂ ℝ := by
  let F : ℂ → ℝ := fun x => f x * originRadialCutoffReinsertionWeight hc ρ γ r A x
  have hF : Continuous F := f.continuous.mul
    (continuous_originRadialCutoffReinsertionWeight P X Xc hX hc ρ γ r hρ A)
  have hFc : HasCompactSupport F := hfc.mul_right
  have hb := hF.bounded_above_of_compact_support hFc
  exact BoundedContinuousFunction.ofNormedAddCommGroup F hF hb.choose hb.choose_spec

/-- Both weighted tests have the same fixed compact support, with uniform error tending
to zero there and exact zero error outside it. -/
theorem originRadialCutoffWeightedTest_uniform_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : γ ≠ 0) (A : TwoSidedPath)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, ∀ x,
      |originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ A f hfc x -
        originRadialWeightedTest ρ γ hρ A f hfc x| ≤ η := by
  intro η hη
  have hδ : 0 < η / (‖f‖ + 1) := div_pos hη (by positivity)
  filter_upwards [originRadialCutoffReinsertionWeight_uniform_approx P X Xc hX hc ρ γ hρ hγ A
    (tsupport (f : ℂ → ℝ)) hfc hfU (η / (‖f‖ + 1)) hδ] with r hr x
  change |f x * originRadialCutoffReinsertionWeight hc ρ γ r A x -
    f x * originRadialReinsertionWeight ρ γ A x| ≤ η
  by_cases hx : x ∈ tsupport (f : ℂ → ℝ)
  · rw [← mul_sub, abs_mul]
    calc _ ≤ ‖f‖ * (η / (‖f‖ + 1)) := mul_le_mul
           (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (hr x hx).le
           (abs_nonneg _) (norm_nonneg _)
      _ ≤ (‖f‖ + 1) * (η / (‖f‖ + 1)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
      _ = η := mul_div_cancel₀ _ (by positivity)
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul, sub_self, abs_zero]
    exact hη.le

/-- The finite radial factor is jointly continuous in the entire continuous path,
center and logarithmic cutoff. Evaluation is continuous on the compact-open path space. -/
theorem continuous_originRadialCutoffReinsertionWeight_joint
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ : ℝ) (hρ : 0 < ρ) :
    Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      originRadialCutoffReinsertionWeight hc ρ γ p.2.2 p.1 p.2.1) := by
  have hR : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) => originCircleRadialL2 hc ρ p.2.1 p.2.2) :=
    (continuous_originCircleRadialL2 P X Xc hX hc ρ hρ).comp continuous_snd
  have hv : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      gaussianVariance P (originCircleRadialL2 hc ρ p.2.1 p.2.2)) := by
    have heq : (fun p : TwoSidedPath × (ℂ × ℝ) =>
        gaussianVariance P (originCircleRadialL2 hc ρ p.2.1 p.2.2)) =
        fun p => ⟪originCircleRadialL2 hc ρ p.2.1 p.2.2,
          originCircleRadialL2 hc ρ p.2.1 p.2.2⟫_ℝ := by
      funext p
      unfold gaussianVariance gaussianCovariance
      rw [integral_mul_eq_inner]
    rw [heq]
    exact hR.inner hR
  have hi : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), p.1 (clampedLogRadius ρ
        (circleMap p.2.1 (Real.exp (-p.2.2)) θ))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous (fun p : (TwoSidedPath × (ℂ × ℝ)) × ℝ =>
      p.1.1 (clampedLogRadius ρ (circleMap p.1.2.1 (Real.exp (-p.1.2.2)) p.2)))
    have ht : Continuous (fun p : (TwoSidedPath × (ℂ × ℝ)) × ℝ =>
        clampedLogRadius ρ (circleMap p.1.2.1 (Real.exp (-p.1.2.2)) p.2)) := by
      apply (continuous_clampedLogRadius ρ hρ).comp
      fun_prop [circleMap]
    exact continuous_eval.comp (continuous_fst.fst.prodMk ht)
  have heq : (fun p : TwoSidedPath × (ℂ × ℝ) =>
      ∫ z, p.1 (clampedLogRadius ρ z) ∂circleMeasure p.2.1 p.2.2) =
      fun p => (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        p.1 (clampedLogRadius ρ (circleMap p.2.1 (Real.exp (-p.2.2)) θ)) := by
    funext p
    have hm : Measurable (fun z => p.1 (clampedLogRadius ρ z)) :=
      (p.1.continuous.comp (continuous_clampedLogRadius ρ hρ)).measurable
    rw [integral_circleMeasure_eq_circleAverage p.2.1 p.2.2 (fun z => p.1 (clampedLogRadius ρ z)) hm,
      Real.circleAverage_def]
    rfl
  have ha : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      ∫ z, p.1 (clampedLogRadius ρ z) ∂circleMeasure p.2.1 p.2.2) := by
    rw [heq]
    exact hi.const_mul _
  exact (((ha.const_mul γ).sub (hv.const_mul (γ ^ 2 / 2))).sub
    (((continuous_clampedLogRadius ρ hρ).comp continuous_snd.fst).abs.const_mul 2)).rexp

/-- The finite radial-weighted test stays in the support of the original compact test. -/
theorem originRadialCutoffWeightedTest_tsupport_subset
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    tsupport (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ A f hfc : ℂ → ℝ) ⊆
      tsupport (f : ℂ → ℝ) := tsupport_mul_subset_left

/-- Joint measurability of a parameter-dependent compact test suffices for joint
measurability of its finite Wick integral. -/
theorem regularizedLogChaosTestMass_parameterTest_measurable
    {V E : Type*} [MeasurableSpace V] [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : E → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ r : ℝ)
    (f : V → BoundedContinuousFunction ℂ ℝ) (hf : Measurable (fun p : V × ℂ => f p.1 p.2)) :
    Measurable (fun p : V × E => regularizedLogChaosTestMass P U dens Y γ r p.2 (f p.1)) := by
  have hv : Measurable (fun x : ℂ => ∫ ξ, Y ξ (Real.exp (-r)) x ^ 2 ∂P) :=
    ((hY.measurableAtScale _).comp measurable_swap).pow_const 2
      |>.stronglyMeasurable.integral_prod_right.measurable
  have htest : Measurable (fun p : (V × E) × ℂ => f p.1.1 p.2) :=
    hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have hfield : Measurable (fun p : (V × E) × ℂ => Y p.1.2 (Real.exp (-r)) p.2) :=
    (hY.measurableAtScale _).comp (measurable_fst.snd.prodMk measurable_snd)
  exact (htest.mul ((hfield.const_mul γ).sub
    ((hv.comp measurable_snd).const_mul (γ ^ 2 / 2))).exp).stronglyMeasurable.integral_prod_right.measurable

/-- With a fixed radial path, the actual finite radial weight may be inserted into the
cutoff limit of any local lateral chaos. -/
theorem originRadialCutoffWeightedTest_tendstoInMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ν : Measure E) [IsProbabilityMeasure ν] (ε₀ : ℝ) (Y : E → ℝ → ℂ → ℝ)
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : γ ≠ 0) (A : TwoSidedPath)
    (hY : IsAdmissibleLogRegularization ν (originLateralChart ρ) originLateralPlaneDensity ε₀ Y)
    (N : E → Measure ℂ)
    (hN : IsAdmissibleGMCVersion ν (originLateralChart ρ) originLateralPlaneDensity Y γ N)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ) :
    TendstoInMeasure ν
      (fun r ξ => regularizedLogChaosTestMass ν (originLateralChart ρ) originLateralPlaneDensity
        Y γ r ξ (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ A f hfc)) atTop
      (fun ξ => ∫ x, originRadialWeightedTest ρ γ hρ A f hfc x ∂N ξ) :=
  regularizedLogChaosTestMass_varying_test_tendstoInMeasure ν (originLateralChart ρ)
    originLateralPlaneDensity ε₀ Y hY γ N hN (tsupport (f : ℂ → ℝ)) hfc hfU
    (fun r => originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ A f hfc)
    (originRadialWeightedTest ρ γ hρ A f hfc)
    (fun r => originRadialCutoffWeightedTest_tsupport_subset P X Xc hX hc ρ γ r hρ A f hfc)
    (tsupport_originRadialWeightedTest_subset ρ γ hρ A f hfc)
    (originRadialCutoffWeightedTest_uniform_approx P X Xc hX hc ρ γ hρ hγ A f hfc hfU)

/-- Independence inserts the whole actual radial path into the finite radial cutoff
weight, including its spatial circle average and exact deterministic variance. -/
theorem originRadialCutoffWeightedTest_independent_tendstoInMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (A : Ω → TwoSidedPath) (π : Ω → E) (hA : Measurable A) (hπ : Measurable π)
    (hi : IndepFun A π P) (ε₀ : ℝ) (Y : E → ℝ → ℂ → ℝ)
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : γ ≠ 0)
    (hY : IsAdmissibleLogRegularization (P.map π) (originLateralChart ρ)
      originLateralPlaneDensity ε₀ Y)
    (N : E → Measure ℂ) (hN : IsAdmissibleGMCVersion (P.map π) (originLateralChart ρ)
      originLateralPlaneDensity Y γ N)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ) :
    TendstoInMeasure P
      (fun r ω => regularizedLogChaosTestMass (P.map π) (originLateralChart ρ) originLateralPlaneDensity
        Y γ r (π ω) (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (A ω) f hfc)) atTop
      (fun ω => ∫ x, originRadialWeightedTest ρ γ hρ (A ω) f hfc x ∂N (π ω)) := by
  let F : ℝ → TwoSidedPath → E → ℝ := fun r v ξ =>
    regularizedLogChaosTestMass (P.map π) (originLateralChart ρ) originLateralPlaneDensity Y γ r ξ
      (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ v f hfc)
  let G : TwoSidedPath → E → ℝ := fun v ξ => ∫ x, originRadialWeightedTest ρ γ hρ v f hfc x ∂N ξ
  have hmF (r : ℝ) : Measurable (Function.uncurry (F r)) := by
    apply regularizedLogChaosTestMass_parameterTest_measurable (P.map π) (originLateralChart ρ)
      originLateralPlaneDensity ε₀ Y hY γ r
      (fun v => originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ v f hfc)
    have hw := (continuous_originRadialCutoffReinsertionWeight_joint P X Xc hX hc ρ γ hρ).measurable.comp
      (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const : Measurable (fun _ => r))))
    exact (f.continuous.measurable.comp measurable_snd).mul hw
  have hmG : Measurable (Function.uncurry G) :=
    originRadialWeightedTest_integral_measurable ρ γ hρ f hfc N hN.1
      (fun ξ => hN.2.2.1 ξ _ hfc hfU)
  exact tendstoInMeasure_independent_parameters P A π hA hπ hi F G hmF hmG
    (fun v => originRadialCutoffWeightedTest_tendstoInMeasure P X Xc hX hc (P.map π)
      ε₀ Y ρ γ hρ hγ v hY N hN f hfc hfU)

/-- The actual local lateral chaos admits the finite radial cutoff-weighted limit on the
original field space, while remaining independent of the whole radial path. -/
theorem exists_originLateralChartGMC_cutoff_weighted_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ N ∧
      IndepFun (originRadialPath Xc) N P ∧
      ∀ (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)),
        tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ →
        TendstoInMeasure P
          (fun r ω => regularizedLogChaosTestMass P (originLateralChart ρ)
            originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω
              (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (originRadialPath Xc ω) f hfc)) atTop
          (fun ω => ∫ x,
            originRadialWeightedTest ρ γ hρ (originRadialPath Xc ω) f hfc x ∂N ω) := by
  let _ := hX.1
  have hpath := originLateralCutoffPath_aemeasurable P Xc hm hcont ρ hρ
  let π := hpath.mk (originLateralCutoffPath Xc ρ)
  have hπm : Measurable π := hpath.measurable_mk
  have hπ : π =ᵐ[P] originLateralCutoffPath Xc ρ := hpath.ae_eq_mk.symm
  have hAm := originRadialPath_aemeasurable P X Xc hc hcont
  let A := hAm.mk (originRadialPath Xc)
  have hAm' : Measurable A := hAm.measurable_mk
  have hA : A =ᵐ[P] originRadialPath Xc := hAm.ae_eq_mk.symm
  have hi : IndepFun A π P :=
    (originRadialPath_lateralCutoffPath_indepFun P X Xc hX hc hm hcont ρ hρ).congr
      hAm.ae_eq_mk hpath.ae_eq_mk
  have hY := originLateralUniversalRegularization_admissible P X Xc hX hc hm hcont ρ hρ π hπm hπ
  obtain ⟨N, hN⟩ := admissibleLogRegularization_GMC_exists (P.map π)
    (originLateralChart ρ) originLateralPlaneDensity (Real.exp (-originLateralCutoffBaseTime ρ))
    (originLateralUniversalRegularization ρ hρ) hY γ hγ hγ2
  have hcomp := originLateralUniversalRegularization_comp_ae P Xc hcont ρ hρ π hπ
  refine ⟨fun ω => N (π ω), ?_, ?_, ?_⟩
  · exact isAdmissibleGMCVersion_map_pullback P π hπm (originLateralChart ρ)
      (isOpen_originLateralChart ρ) originLateralPlaneDensity _ (Real.exp_pos _)
      (originLateralCircleRegularization Xc ρ) (originLateralUniversalRegularization ρ hρ)
      (originLateralUniversalRegularization_measurableAtScale ρ hρ) hcomp γ N hN
  · exact (hi.congr hA EventuallyEq.rfl).comp measurable_id hN.1
  · intro f hfc hfU
    have ht := originRadialCutoffWeightedTest_independent_tendstoInMeasure P X Xc hX hc
      A π hAm' hπm hi _ (originLateralUniversalRegularization ρ hρ) ρ γ hρ hγ.ne' hY N hN f hfc hfU
    have hleft : ∀ᶠ r : ℝ in atTop,
        (fun ω => regularizedLogChaosTestMass (P.map π) (originLateralChart ρ)
          originLateralPlaneDensity (originLateralUniversalRegularization ρ hρ) γ r (π ω)
            (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (A ω) f hfc)) =ᵐ[P]
        fun ω => regularizedLogChaosTestMass P (originLateralChart ρ)
          originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω
            (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (originRadialPath Xc ω) f hfc) := by
      filter_upwards [eventually_ge_atTop (originLateralCutoffBaseTime ρ)] with r hr
      have hcut : Real.exp (-r) ≤ Real.exp (-originLateralCutoffBaseTime ρ) :=
        Real.exp_le_exp.mpr (neg_le_neg hr)
      have heq := regularizedLogChaosTestMass_randomTest_map_comp P π hπm
        (originLateralChart ρ) (isOpen_originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) (originLateralUniversalRegularization ρ hρ)
        (originLateralUniversalRegularization_measurableAtScale ρ hρ) γ r
        (fun ω => originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (A ω) f hfc)
        (hcomp.mono (fun ω hω => hω _ (Real.exp_pos _) hcut))
      filter_upwards [heq, hA] with ω hω hAω
      rw [hω, hAω]
    have hright : (fun ω => ∫ x, originRadialWeightedTest ρ γ hρ (A ω) f hfc x ∂N (π ω)) =ᵐ[P]
        fun ω => ∫ x, originRadialWeightedTest ρ γ hρ (originRadialPath Xc ω) f hfc x ∂N (π ω) := by
      filter_upwards [hA] with ω hω
      rw [hω]
    exact TendstoInMeasure.congr' hleft hright ht

end DOZZ.Proofs
