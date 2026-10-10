/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.CutoffIntegral
public import DOZZ.GMC.CircleAverage
public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import DOZZ.GMC.Construction.GMCUniqueAe
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.Construction.FatouInMeasure
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Construction.ReferenceMeasureFinite
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! The circle cutoff chaos as an admissible cutoff integral, the intensity upper bound of every circle GMC version, and continuous `L¹` approximation of bounded Borel tests. -/

@[expose] public section

/-! ### The circle cutoff chaos

The circle-average cutoff chaos as an admissible cutoff integral.

For every Borel test, the integral against `DOZZ.regularizedGMC` is the admissible cutoff integral
of the circle regularization on the whole plane. Hence the cutoff `L¹` Cauchy estimate holds for the
circle chaos, uniformly over compact charge sets and bounded Borel tests supported in a compact
set. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The circle average as an admissible regularization in the cutoff radius `ε = e^{-r}`. -/
noncomputable abbrev circleRegularization {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) :
    Ω → ℝ → ℂ → ℝ :=
  fun ω ε x => Xc ω x (Real.log (1 / ε))

/-- The reference density of the circle chaos. -/
noncomputable abbrev circleDensity : ℂ → ℝ := fun x => normPlus x ^ (-4 : ℝ)

theorem circleRegularization_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    IsAdmissibleLogRegularization P Set.univ circleDensity 1 (circleRegularization Xc) :=
  DOZZ.Proofs.isCircleAverage_admissible P X hX Xc hXc Set.univ isOpen_univ

theorem logRegularizationReference_univ_circleDensity :
    logRegularizationReference Set.univ circleDensity = gmcReferenceMeasure := by
  unfold logRegularizationReference gmcReferenceMeasure
  rw [Measure.restrict_univ]


/-- Integrals of Borel tests against the circle cutoff chaos are admissible cutoff integrals. -/
theorem integral_regularizedGMC_eq_admissibleCutoffIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (f : ℂ → ℝ) (ω : Ω) :
    ∫ x, f x ∂regularizedGMC P Xc γ r ω =
      admissibleCutoffIntegral P Set.univ circleDensity (circleRegularization Xc) γ r f ω := by
  classical
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  have hVmeas : Measurable V := by
    let _ := hX.1
    have hq : Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) :=
      ((hXc.1 r).comp measurable_swap).pow_const 2
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  have hweightMeas : Measurable (fun x : ℂ => normPlus x ^ (-4 : ℝ)) := by
    unfold normPlus
    fun_prop
  let d₀ : ℂ → ℝ := fun x => normPlus x ^ (-4 : ℝ)
  let d₁ : ℂ → ℝ := fun x =>
    Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)
  have hd₁ : Measurable d₁ := by
    have hfield : Measurable (fun x : ℂ => Xc ω x r) :=
      (hXc.1 r).comp (measurable_const.prodMk measurable_id)
    dsimp [d₁]
    fun_prop
  have he₀ : Measurable (fun x => ENNReal.ofReal (d₀ x)) :=
    ENNReal.measurable_ofReal.comp hweightMeas
  have he₁ : Measurable (fun x => ENNReal.ofReal (d₁ x)) := ENNReal.measurable_ofReal.comp hd₁
  have hd₀nonneg (x : ℂ) : 0 ≤ d₀ x :=
    Real.rpow_nonneg (le_of_lt (by simp [normPlus])) _
  have hd₁nonneg (x : ℂ) : 0 ≤ d₁ x :=
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (le_of_lt (by simp [normPlus])) _)
  have hright : admissibleCutoffIntegral P Set.univ circleDensity (circleRegularization Xc) γ r
      f ω = ∫ x, (ENNReal.ofReal (d₀ x)).toReal * (f x * Real.exp
          (γ * Xc ω x r - γ ^ 2 / 2 * V x)) ∂volume := by
    unfold admissibleCutoffIntegral
    rw [logRegularizationReference, Measure.restrict_univ,
      integral_withDensity_eq_integral_toReal_smul he₀ (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [circleRegularization, one_div, Real.log_inv, Real.log_exp, neg_neg, smul_eq_mul, V,
      d₀]
  have hleft : (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x, (ENNReal.ofReal (d₁ x)).toReal * f x ∂volume := by
    rw [regularizedGMC, integral_withDensity_eq_integral_toReal_smul he₁
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul, d₁, V]
  rw [hleft, hright]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hd₀nonneg x), ENNReal.toReal_ofReal (hd₁nonneg x)]
  simp only [d₀, d₁]
  ring

/-- The admissible cutoff integral of a Borel test is measurable in the sample. -/
theorem admissibleCutoffIntegral_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g r : ℝ) (f : ℂ → ℝ)
    (hf : Measurable f) :
    Measurable (admissibleCutoffIntegral P U dens Y g r f) := by
  have hv := admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY (Real.exp (-r))
  have hv' : Measurable (fun x => ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) := by
    have heq : (fun x => ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) =
        fun x => gaussianVariance P (fun ω => Y ω (Real.exp (-r)) x) := by
      funext x
      unfold gaussianVariance gaussianCovariance
      simp only [pow_two]
    rw [heq]; exact hv
  have hfield : Measurable (fun q : Ω × ℂ => Y q.1 (Real.exp (-r)) q.2) :=
    hY.measurableAtScale _
  have hF : Measurable (fun q : Ω × ℂ => f q.2 * Real.exp (g * Y q.1 (Real.exp (-r)) q.2 -
      g ^ 2 / 2 * ∫ ω', Y ω' (Real.exp (-r)) q.2 ^ 2 ∂P)) := by
    have h2 : Measurable (fun q : Ω × ℂ => ∫ ω', Y ω' (Real.exp (-r)) q.2 ^ 2 ∂P) :=
      hv'.comp measurable_snd
    have h3 : Measurable (fun q : Ω × ℂ => f q.2) := hf.comp measurable_snd
    fun_prop
  exact hF.stronglyMeasurable.integral_prod_right.measurable

/-- Test integrals against the circle cutoff chaos are measurable in the sample. -/
theorem regularizedGMC_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) := by
  have : IsProbabilityMeasure P := hX.1
  have heq : (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      admissibleCutoffIntegral P Set.univ circleDensity (circleRegularization Xc) γ r f := by
    funext ω
    exact integral_regularizedGMC_eq_admissibleCutoffIntegral P X hX Xc hXc γ r f ω
  rw [heq]
  exact admissibleCutoffIntegral_measurable P Set.univ circleDensity 1 _
    (circleRegularization_admissible P X hX Xc hXc) γ r f hf

/-- The circle cutoff chaos is uniformly `L¹` Cauchy over compact subcritical charge sets and
bounded Borel tests supported in a compact set. -/
theorem regularizedGMC_integral_L1_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (I : Set ℝ) (hI : IsCompact I) (hI2 : I ⊆ Ioo 0 2)
    (K : Set ℂ) (hK : IsCompact K) (L : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s → ∀ γ ∈ I, ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, |f x| ≤ L) → (∀ x ∉ K, f x = 0) →
      ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω -
        ∫ x, f x ∂regularizedGMC P Xc γ s ω| ∂P < ENNReal.ofReal ε := by
  have : IsProbabilityMeasure P := hX.1
  obtain ⟨R, hR⟩ := admissibleCutoffIntegral_L1_uniform_cauchy P Set.univ circleDensity 1 _
    (circleRegularization_admissible P X hX Xc hXc) K hK (Set.subset_univ K) I hI hI2 L ε hε
  refine ⟨R, fun r s hr hs γ hγ f hf hfL hfK => ?_⟩
  simp only [integral_regularizedGMC_eq_admissibleCutoffIntegral P X hX Xc hXc]
  exact hR r s hr hs γ hγ f hf hfL hfK

end DOZZ.Assembly

/-! ### Intensity upper bound

The intensity of any circle GMC version is at most the reference measure.

Fatou along convergence in measure gives the bound for nonnegative bounded continuous tests;
continuous ramps up to an open set give it for open sets; outer regularity of the finite reference
measure gives it for Borel sets; and the bind of the measurable version integrates every
nonnegative Borel test. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions BoundedContinuousFunction

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- A circle GMC version converges along the cutoffs of every circle-average witness. -/
theorem isGMCOf_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (f : ℂ →ᵇ ℝ) :
    TendstoInMeasure P (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
      (fun ω => ∫ x, f x ∂M ω) := by
  obtain ⟨Xc', hXc', hconv⟩ := hM.2
  refine (hconv f).congr_left (fun r => ?_)
  filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX Xc' Xc hXc' hXc γ r] with ω hω
  rw [hω]

/-- Fatou bound for a nonnegative bounded continuous test against a circle GMC version. -/
theorem isGMCOf_lintegral_ofReal_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (f : ℂ →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, f x ∂M ω) ∂P ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  apply lintegral_ofReal_limit_le_of_tendstoInMeasure P _ _ _
    (fun r => regularizedGMC_integral_measurable P X hX Xc hXc γ r f f.continuous.measurable)
    (isGMCOf_tendstoInMeasure P X hX Xc hXc γ M hM f)
  intro r
  calc ∫⁻ ω, ENNReal.ofReal (∫ x, f x ∂regularizedGMC P Xc γ r ω) ∂P ≤
        ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (f x) ∂regularizedGMC P Xc γ r ω ∂P := by
        apply lintegral_mono
        intro ω
        beta_reduce
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf)
          f.continuous.measurable.aestronglyMeasurable]
        exact ENNReal.ofReal_toReal_le
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure :=
        regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r _
          (ENNReal.measurable_ofReal.comp f.continuous.measurable)

/-- Continuous ramps increasing to the indicator of an open set with nonempty complement. -/
noncomputable def openRamp (V : Set ℂ) (n : ℕ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min 1 ((n : ℝ) * Metric.infDist x Vᶜ))
    (continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))) 1
    (fun x => by
      have h0 : 0 ≤ min 1 ((n : ℝ) * Metric.infDist x Vᶜ) :=
        le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) Metric.infDist_nonneg)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_left _ _)

theorem openRamp_apply (V : Set ℂ) (n : ℕ) (x : ℂ) :
    openRamp V n x = min 1 ((n : ℝ) * Metric.infDist x Vᶜ) := rfl

theorem openRamp_nonneg (V : Set ℂ) (n : ℕ) (x : ℂ) : 0 ≤ openRamp V n x := by
  rw [openRamp_apply]
  exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) Metric.infDist_nonneg)

theorem openRamp_le_indicator (V : Set ℂ) (n : ℕ) (x : ℂ) : ENNReal.ofReal (openRamp V n x) ≤ V.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx, openRamp_apply]
    exact ENNReal.ofReal_le_one.mpr (min_le_left _ _)
  · rw [Set.indicator_of_notMem hx, openRamp_apply,
      Metric.infDist_zero_of_mem (show x ∈ Vᶜ from hx)]
    simp

theorem openRamp_mono (V : Set ℂ) (x : ℂ) : Monotone (fun n => openRamp V n x) := by
  intro n m hnm
  simp only [openRamp_apply]
  apply min_le_min le_rfl
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) Metric.infDist_nonneg

theorem openRamp_tendsto (V : Set ℂ) (hV : IsOpen V) (hVc : Vᶜ.Nonempty) (x : ℂ) :
    Tendsto (fun n => ENNReal.ofReal (openRamp V n x)) atTop
      (𝓝 (V.indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]
    have hpos : 0 < Metric.infDist x Vᶜ :=
      (hV.isClosed_compl.notMem_iff_infDist_pos hVc).mp (fun h => h hx)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist x Vᶜ)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [openRamp_apply]
    have hn' : (1 : ℝ) ≤ (n : ℝ) * Metric.infDist x Vᶜ := by
      have h1 : 1 / Metric.infDist x Vᶜ < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
      rw [div_lt_iff₀ hpos] at h1
      linarith
    rw [min_eq_left hn', ENNReal.ofReal_one]
  · rw [Set.indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [openRamp_apply, Metric.infDist_zero_of_mem (show x ∈ Vᶜ from hx)]
    simp

/-- A measurable random measure is bounded in expectation by the reference measure on every open
set, given the bound for all nonnegative bounded continuous tests. -/
theorem lintegral_measure_isOpen_le_of_test_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure ℂ) (hN : Measurable N)
    (ν : Measure ℂ)
    (htest : ∀ f : ℂ →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (f x) ∂N ω ∂P ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν)
    (V : Set ℂ) (hV : IsOpen V) :
    ∫⁻ ω, N ω V ∂P ≤ ν V := by
  by_cases hVc : Vᶜ.Nonempty
  · have hrampMeas (n : ℕ) : Measurable (fun x => ENNReal.ofReal (openRamp V n x)) :=
      ENNReal.measurable_ofReal.comp (openRamp V n).continuous.measurable
    have hmono (ω : Ω) : Monotone (fun n => ∫⁻ x, ENNReal.ofReal (openRamp V n x) ∂N ω) :=
      fun n m hnm => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (openRamp_mono V x hnm)
    have hpoint (ω : Ω) : N ω V = ⨆ n, ∫⁻ x, ENNReal.ofReal (openRamp V n x) ∂N ω := by
      rw [← lintegral_iSup hrampMeas (fun n m hnm x =>
        ENNReal.ofReal_le_ofReal (openRamp_mono V x hnm))]
      have hlim (x : ℂ) : (⨆ n, ENNReal.ofReal (openRamp V n x)) =
          V.indicator (fun _ => (1 : ℝ≥0∞)) x :=
        tendsto_nhds_unique (tendsto_atTop_iSup fun n m hnm =>
          ENNReal.ofReal_le_ofReal (openRamp_mono V x hnm)) (openRamp_tendsto V hV hVc x)
      simp only [hlim]
      rw [lintegral_indicator_const hV.measurableSet, one_mul]
    have hmeasω (n : ℕ) : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (openRamp V n x) ∂N ω) :=
      (Measure.measurable_lintegral (hrampMeas n)).comp hN
    calc ∫⁻ ω, N ω V ∂P = ∫⁻ ω, ⨆ n, ∫⁻ x, ENNReal.ofReal (openRamp V n x) ∂N ω ∂P := by
          simp only [hpoint]
      _ = ⨆ n, ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (openRamp V n x) ∂N ω ∂P :=
          lintegral_iSup hmeasω (fun n m hnm ω => hmono ω hnm)
      _ ≤ ν V := by
          apply iSup_le
          intro n
          refine (htest (openRamp V n) (openRamp_nonneg V n)).trans ?_
          calc ∫⁻ x, ENNReal.ofReal (openRamp V n x) ∂ν ≤
                ∫⁻ x, V.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν :=
                lintegral_mono fun x => openRamp_le_indicator V n x
            _ = ν V := by rw [lintegral_indicator_const hV.measurableSet, one_mul]
  · have hVuniv : V = Set.univ := by
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hVc
      exact hVc
    subst hVuniv
    have h := htest (BoundedContinuousFunction.const ℂ 1) (fun _ => zero_le_one)
    simpa using h

/-- A measurable random measure bounded in expectation by a finite reference measure on open
sets is bounded by it on every Borel set. -/
theorem lintegral_measure_le_of_isOpen_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure ℂ)
    (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hopen : ∀ V : Set ℂ, IsOpen V → ∫⁻ ω, N ω V ∂P ≤ ν V) (A : Set ℂ) :
    ∫⁻ ω, N ω A ∂P ≤ ν A := by
  apply le_of_forall_gt
  intro c hc
  obtain ⟨V, hAV, hV, hVc⟩ := A.exists_isOpen_lt_of_lt c hc
  exact lt_of_le_of_lt ((lintegral_mono fun ω => measure_mono hAV).trans (hopen V hV)) hVc

/-- Intensity upper bound for a circle GMC version: for every nonnegative Borel test, the
expected integral against the random measure is at most its reference integral. -/
theorem isGMCOf_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, ∫⁻ x, φ x ∂M ω ∂P ≤ ∫⁻ x, φ x ∂gmcReferenceMeasure := by
  have : IsFiniteMeasure gmcReferenceMeasure :=
    ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  obtain ⟨N, hNmeas, hNfin, hMN⟩ :=
    DOZZ.Proofs.equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have htest : ∀ f : ℂ →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (f x) ∂N ω ∂P ≤
        ∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure := by
    intro f hf
    refine le_trans (le_of_eq ?_) (isGMCOf_lintegral_ofReal_integral_le P X hX γ M hM f hf)
    apply lintegral_congr_ae
    filter_upwards [hMN] with ω hω
    rw [hω, ← ofReal_integral_eq_lintegral_ofReal
      (f.integrable (N ω)) (ae_of_all _ hf)]
  have hopen := lintegral_measure_isOpen_le_of_test_bound P N hNmeas gmcReferenceMeasure htest
  have hbind : P.bind N ≤ gmcReferenceMeasure := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.bind_apply hs hNmeas.aemeasurable]
    exact lintegral_measure_le_of_isOpen_bound P N gmcReferenceMeasure hopen s
  calc ∫⁻ ω, ∫⁻ x, φ x ∂M ω ∂P = ∫⁻ ω, ∫⁻ x, φ x ∂N ω ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hMN] with ω hω
        rw [hω]
    _ = ∫⁻ x, φ x ∂P.bind N := (Measure.lintegral_bind hNmeas.aemeasurable
        hφ.aemeasurable).symm
    _ ≤ ∫⁻ x, φ x ∂gmcReferenceMeasure := lintegral_mono' hbind le_rfl

end DOZZ.Assembly

/-! ### Continuous approximation of Borel tests

Bounded Borel tests supported in a ball are `L¹`-approximated, for any finite measure on the
plane, by continuous tests with the same bound supported in a slightly larger ball.

A compactly supported continuous approximation is clamped to the bound and cut off outside the
larger ball; both operations only decrease the pointwise distance to the test. -/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

/-- Clamping to `[-L, L]`. -/
noncomputable def clampAbs (L t : ℝ) : ℝ := max (-L) (min L t)

theorem continuous_clampAbs (L : ℝ) : Continuous (clampAbs L) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clampAbs_le (L t : ℝ) (hL : 0 ≤ L) : |clampAbs L t| ≤ L := by
  unfold clampAbs
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem abs_clampAbs_le_abs (L t : ℝ) (hL : 0 ≤ L) : |clampAbs L t| ≤ |t| := by
  unfold clampAbs
  rcases le_total t (-L) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h, abs_neg, abs_of_nonneg hL,
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total t L with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (by linarith), abs_of_nonneg hL, abs_of_nonneg (by linarith)]
      exact h'

theorem abs_sub_clampAbs_le (L s t : ℝ) (hs : |s| ≤ L) : |s - clampAbs L t| ≤ |s - t| := by
  unfold clampAbs
  have hs' := abs_le.mp hs
  rcases le_total t (-L) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total t L with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (by linarith)]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

/-- The radial cutoff equal to one on the ball of radius `ρ` and vanishing off radius `ρ + 1`. -/
noncomputable def ballCutoff (ρ : ℝ) (x : ℂ) : ℝ := max 0 (min 1 (ρ + 1 - ‖x‖))

theorem continuous_ballCutoff (ρ : ℝ) : Continuous (ballCutoff ρ) := by
  unfold ballCutoff
  fun_prop

theorem ballCutoff_nonneg (ρ : ℝ) (x : ℂ) : 0 ≤ ballCutoff ρ x := le_max_left _ _

theorem ballCutoff_le_one (ρ : ℝ) (x : ℂ) : ballCutoff ρ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ballCutoff_eq_one (ρ : ℝ) (x : ℂ) (hx : ‖x‖ ≤ ρ) : ballCutoff ρ x = 1 := by
  unfold ballCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem ballCutoff_eq_zero (ρ : ℝ) (x : ℂ) (hx : ρ + 1 < ‖x‖) : ballCutoff ρ x = 0 := by
  unfold ballCutoff
  rw [max_eq_left (min_le_right _ _ |>.trans (by linarith))]

/-- Continuous `L¹` approximation of bounded Borel tests with bound and support control. -/
theorem exists_continuous_L1_approx
    (ν : Measure ℂ) [IsFiniteMeasure ν] (ρ L : ℝ) (f : ℂ → ℝ) (hf : Measurable f)
    (hfL : ∀ x, |f x| ≤ L) (hfρ : ∀ x, ρ < ‖x‖ → f x = 0) (δ : ℝ≥0∞) (hδ : δ ≠ 0) :
    ∃ h : ℂ → ℝ, Continuous h ∧ (∀ x, |h x| ≤ L) ∧ (∀ x, ρ + 1 < ‖x‖ → h x = 0) ∧
      ∫⁻ x, ENNReal.ofReal |f x - h x| ∂ν ≤ δ := by
  have hL : 0 ≤ L := (abs_nonneg _).trans (hfL 0)
  have hfint : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable L (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hfL x)
  obtain ⟨g, -, hg, hgcont, -⟩ := hfint.exists_hasCompactSupport_lintegral_sub_le hδ
  refine ⟨fun x => ballCutoff ρ x * clampAbs L (g x),
    (continuous_ballCutoff ρ).mul ((continuous_clampAbs L).comp hgcont), ?_, ?_, ?_⟩
  · intro x
    rw [abs_mul, abs_of_nonneg (ballCutoff_nonneg ρ x)]
    calc ballCutoff ρ x * |clampAbs L (g x)| ≤ 1 * L :=
          mul_le_mul (ballCutoff_le_one ρ x) (abs_clampAbs_le L _ hL) (abs_nonneg _) zero_le_one
      _ = L := one_mul L
  · intro x hx
    show ballCutoff ρ x * clampAbs L (g x) = 0
    rw [ballCutoff_eq_zero ρ x hx, zero_mul]
  · refine le_trans (lintegral_mono fun x => ?_) hg
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    show |f x - ballCutoff ρ x * clampAbs L (g x)| ≤ |f x - g x|
    by_cases hx : ‖x‖ ≤ ρ
    · rw [ballCutoff_eq_one ρ x hx, one_mul]
      exact abs_sub_clampAbs_le L (f x) (g x) (hfL x)
    · rw [hfρ x (lt_of_not_ge hx), zero_sub, abs_neg, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (ballCutoff_nonneg ρ x)]
      calc ballCutoff ρ x * |clampAbs L (g x)| ≤ 1 * |g x| :=
            mul_le_mul (ballCutoff_le_one ρ x) (abs_clampAbs_le_abs L _ hL) (abs_nonneg _)
              zero_le_one
        _ = |g x| := one_mul _

/-- The real distance of two integrals is at most the integral of the distance, for any two
measurable functions, integrable or not. -/
theorem ofReal_abs_integral_sub_le_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f h : α → ℝ) (hf : Measurable f) (hh : Measurable h) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, h x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |f x - h x| ∂μ := by
  by_cases hfi : Integrable f μ
  · by_cases hhi : Integrable h μ
    · rw [← integral_sub hfi hhi, ← Real.enorm_eq_ofReal_abs]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp_rw [Real.enorm_eq_ofReal_abs]
    · have hnot : ¬ Integrable (fun x => f x - h x) μ := by
        intro hsub
        apply hhi
        have h1 : Integrable (fun x => f x - (f x - h x)) μ := hfi.sub hsub
        exact h1.congr (ae_of_all _ fun x => sub_sub_cancel (f x) (h x))
      have htop : ∫⁻ x, ‖f x - h x‖ₑ ∂μ = ⊤ := by
        by_contra hne
        exact hnot ⟨(hf.sub hh).aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
      simp_rw [Real.enorm_eq_ofReal_abs] at htop
      rw [htop]
      exact le_top
  · by_cases hhi : Integrable h μ
    · have hnot : ¬ Integrable (fun x => f x - h x) μ := by
        intro hsub
        apply hfi
        have h1 : Integrable (fun x => (f x - h x) + h x) μ := hsub.add hhi
        exact h1.congr (ae_of_all _ fun x => sub_add_cancel (f x) (h x))
      have htop : ∫⁻ x, ‖f x - h x‖ₑ ∂μ = ⊤ := by
        by_contra hne
        exact hnot ⟨(hf.sub hh).aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
      simp_rw [Real.enorm_eq_ofReal_abs] at htop
      rw [htop]
      exact le_top
    · rw [integral_undef hfi, integral_undef hhi, sub_self, abs_zero, ENNReal.ofReal_zero]
      exact zero_le

end DOZZ.Assembly
