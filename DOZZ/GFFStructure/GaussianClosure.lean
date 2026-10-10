/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.Defs
public import DOZZ.GFFStructure.AnnularWeakLimit
public import DOZZ.GFF.Potential
public import DOZZ.GFF.EquatorField
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Gaussian closure in the given probability space

Scalar Gaussian laws are closed under L² convergence. Means, second moments and covariances
are continuous in L²; characteristic functions identify the limit, including zero variance.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace RealInnerProductSpace

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Expectation is the L² pairing with the constant one. -/
theorem integral_eq_inner_one (U : Lp ℝ 2 P) :
    (∫ ω, U ω ∂P) = ⟪U, Lp.const 2 P (1 : ℝ)⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := (2 : ℝ≥0∞)) P (1 : ℝ)] with ω hω
  change U ω = Lp.const 2 P (1 : ℝ) ω * U ω
  rw [hω]
  exact (one_mul _).symm

/-- Means converge under L² convergence. -/
theorem tendsto_integral_of_tendsto_L2 {U : ℕ → Lp ℝ 2 P} {V : Lp ℝ 2 P}
    (h : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => ∫ ω, U n ω ∂P) atTop (𝓝 (∫ ω, V ω ∂P)) := by
  simp_rw [integral_eq_inner_one]
  exact h.inner tendsto_const_nhds

omit [IsProbabilityMeasure P] in
/-- Mixed second moments are L² pairings. -/
theorem integral_mul_eq_inner (U V : Lp ℝ 2 P) :
    (∫ ω, U ω * V ω ∂P) = ⟪U, V⟫_ℝ := by
  rw [L2.inner_def]
  congr 1
  funext ω
  change U ω * V ω = V ω * U ω
  exact mul_comm _ _

/-- Covariance in L² is a continuous expression in pairings and expectations. -/
theorem covariance_L2_eq (U V : Lp ℝ 2 P) :
    covariance U V P = ⟪U, V⟫_ℝ - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P) := by
  rw [covariance_eq_sub (Lp.memLp U) (Lp.memLp V)]
  change (∫ ω, U ω * V ω ∂P) - _ = _
  rw [integral_mul_eq_inner]

/-- Covariances converge when both variables converge in L². -/
theorem tendsto_covariance_of_tendsto_L2
    {U V : ℕ → Lp ℝ 2 P} {U₀ V₀ : Lp ℝ 2 P}
    (hU : Tendsto U atTop (𝓝 U₀)) (hV : Tendsto V atTop (𝓝 V₀)) :
    Tendsto (fun n => covariance (U n) (V n) P) atTop (𝓝 (covariance U₀ V₀ P)) := by
  simp_rw [covariance_L2_eq]
  exact (hU.inner hV).sub
    ((tendsto_integral_of_tendsto_L2 hU).mul (tendsto_integral_of_tendsto_L2 hV))

/-- Variances converge under L² convergence. -/
theorem tendsto_variance_of_tendsto_L2 {U : ℕ → Lp ℝ 2 P} {V : Lp ℝ 2 P}
    (h : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => variance (U n) P) atTop (𝓝 (variance V P)) := by
  simp_rw [← covariance_self (Lp.aestronglyMeasurable _).aemeasurable]
  exact tendsto_covariance_of_tendsto_L2 h h

/-- A scalar L² limit of Gaussian variables is Gaussian, allowing degenerate limits. -/
theorem hasGaussianLaw_of_tendsto_L2 {U : ℕ → Lp ℝ 2 P} {V : Lp ℝ 2 P}
    (hG : ∀ n, HasGaussianLaw (U n) P) (h : Tendsto U atTop (𝓝 V)) :
    HasGaussianLaw V P := by
  have hdist : TendstoInDistribution (fun n => ⇑(U n)) atTop (⇑V) (fun _ => P) P :=
    (tendstoInMeasure_of_tendsto_Lp h).tendstoInDistribution
      (fun n => (Lp.aestronglyMeasurable (U n)).aemeasurable)
  apply (hasGaussianLaw_iff_charFun_map_eq (Lp.aestronglyMeasurable V).aemeasurable).2
  intro t
  have hmean := tendsto_integral_of_tendsto_L2 h
  have hvar := tendsto_variance_of_tendsto_L2 h
  have hmeanC := Complex.continuous_ofReal.tendsto _ |>.comp hmean
  have hvarC := Complex.continuous_ofReal.tendsto _ |>.comp hvar
  have hexp : Tendsto
      (fun n => Complex.exp ((t : ℂ) * (∫ ω, U n ω ∂P) * Complex.I -
        (variance (U n) P : ℂ) * (t : ℂ) ^ 2 / 2)) atTop
      (𝓝 (Complex.exp ((t : ℂ) * (∫ ω, V ω ∂P) * Complex.I -
        (variance V P : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    exact Complex.continuous_exp.tendsto _ |>.comp
      ((tendsto_const_nhds.mul hmeanC).mul tendsto_const_nhds |>.sub
        ((hvarC.mul tendsto_const_nhds).div tendsto_const_nhds (by norm_num : (2 : ℂ) ≠ 0)))
  have hchar := hdist.tendsto_charFun t
  simp_rw [(hG _).map_eq_gaussianReal, charFun_gaussianReal,
    Real.coe_toNNReal _ (variance_nonneg _ _)] at hchar
  have heq := tendsto_nhds_unique hchar hexp
  rw [heq]
  change Complex.exp ((t : ℂ) * (∫ ω, V ω ∂P) * Complex.I -
    (variance V P : ℂ) * (t : ℂ) ^ 2 / 2) =
    Complex.exp (((∫ ω, V ω * t ∂P) : ℝ) * Complex.I -
      (variance (fun ω => V ω * t) P : ℂ) / 2)
  rw [integral_mul_const, variance_mul_const]
  congr 1
  push_cast
  ring

omit [IsProbabilityMeasure P] in
/-- Gaussianity of all real linear combinations identifies a finite-dimensional law. -/
theorem hasGaussianLaw_pi_of_linearCombinations {ι : Type*} [Fintype ι]
    (Z : ι → Ω → ℝ) (hmeas : ∀ i, AEMeasurable (Z i) P)
    (hlin : ∀ a : ι → ℝ, HasGaussianLaw (fun ω => ∑ i, a i * Z i ω) P) :
    HasGaussianLaw (fun ω i => Z i ω) P := by
  classical
  have hm : AEMeasurable (fun ω i => Z i ω) P := AEMeasurable.of_eval hmeas
  refine ⟨hm, isGaussian_of_isGaussian_map fun L => ?_⟩
  have hform (ω : Ω) : L (fun i => Z i ω) =
      ∑ i, L (Pi.single i 1) * Z i ω := by
    rw [pi_eq_sum_univ' (fun i => Z i ω), map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  have hg : HasGaussianLaw (L ∘ fun ω i => Z i ω) P := by
    simpa only [Function.comp_def, hform] using hlin (fun i => L (Pi.single i 1))
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm]
  exact hg.isGaussian_map

omit [IsProbabilityMeasure P] in
/-- Scalar linear combinations of a finite restriction of a Gaussian process are Gaussian. -/
theorem gaussianProcess_linearCombination {T : Type*}
    {Z : T → Ω → ℝ} (hZ : IsGaussianProcess Z P) (I : Finset T) (a : I → ℝ) :
    HasGaussianLaw (fun ω => ∑ i : I, a i * Z i ω) P := by
  let L : (I → ℝ) →L[ℝ] ℝ := ∑ i : I, a i • ContinuousLinearMap.proj i
  have hL (x : I → ℝ) : L x = ∑ i, a i * x i := by
    simp only [L, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hg := (hZ.hasGaussianLaw I).map L
  convert hg using 1
  funext ω
  exact (hL (I.restrict (Z · ω))).symm

omit [IsProbabilityMeasure P] in
/-- L² representatives of finite scalar combinations agree with the pointwise sums. -/
theorem coeFn_L2_linearCombination {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (Z : ι → Lp ℝ 2 P) :
    (⇑(∑ i, a i • Z i)) =ᵐ[P] fun ω => ∑ i, a i * Z i ω := by
  classical
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i => a i • Z i)
  have ht : ∀ᵐ ω ∂P, ∀ i, (a i • Z i) ω = a i * Z i ω :=
    ae_all_iff.2 fun i => Lp.coeFn_smul (a i) (Z i)
  filter_upwards [hs, ht] with ω hω hω'
  rw [hω]
  rw [Finset.sum_apply]
  change ∑ i, (a i • Z i) ω = ∑ i, a i * Z i ω
  exact Finset.sum_congr rfl (fun i _ => hω' i)

/-- Joint Gaussianity is preserved by coordinatewise L² limits, with no countability condition
on the process index. Every finite restriction is handled on its own finite null-set union. -/
theorem isGaussianProcess_of_tendsto_L2 {T : Type*}
    (Z : ℕ → T → Lp ℝ 2 P) (W : T → Lp ℝ 2 P)
    (hZ : ∀ n, IsGaussianProcess (fun t => ⇑(Z n t)) P)
    (hlim : ∀ t, Tendsto (fun n => Z n t) atTop (𝓝 (W t))) :
    IsGaussianProcess (fun t => ⇑(W t)) P := by
  classical
  constructor
  intro I
  apply hasGaussianLaw_pi_of_linearCombinations
    (fun i : I => ⇑(W i)) (fun i => (Lp.aestronglyMeasurable (W i)).aemeasurable)
  intro a
  have hg : ∀ n, HasGaussianLaw (⇑(∑ i : I, a i • Z n i)) P := by
    intro n
    exact (gaussianProcess_linearCombination (hZ n) I a).congr
      (coeFn_L2_linearCombination a (fun i : I => Z n i)).symm
  have hl : Tendsto (fun n => ∑ i : I, a i • Z n i) atTop
      (𝓝 (∑ i : I, a i • W i)) :=
    tendsto_finsetSum _ fun i _ => (hlim i).const_smul (a i)
  exact (hasGaussianLaw_of_tendsto_L2 hg hl).congr (coeFn_L2_linearCombination a _)

omit [IsProbabilityMeasure P] in
/-- Conversion of a raw L² error limit to convergence in the quotient L² space. -/
theorem tendsto_toLp_of_eLpNorm_sub {Z : ℕ → Ω → ℝ} {W : Ω → ℝ}
    (hZ : ∀ n, MemLp (Z n) 2 P) (hW : MemLp W 2 P)
    (h : Tendsto (fun n => eLpNorm (fun ω => Z n ω - W ω) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => (hZ n).toLp (Z n)) atTop (𝓝 (hW.toLp W)) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Z hZ W hW).2 h

/-- Gaussian laws are closed under the raw L²-error convergence used by the witnesses of
`DOZZ.IsCircleAverage`. -/
theorem hasGaussianLaw_of_eLpNorm_sub {Z : ℕ → Ω → ℝ} {W : Ω → ℝ}
    (hZ : ∀ n, HasGaussianLaw (Z n) P) (hW : MemLp W 2 P)
    (h : Tendsto (fun n => eLpNorm (fun ω => Z n ω - W ω) 2 P) atTop (𝓝 0)) :
    HasGaussianLaw W P := by
  have hm n := (hZ n).memLp_two
  have hg n := (hZ n).congr (hm n).coeFn_toLp.symm
  exact (hasGaussianLaw_of_tendsto_L2 hg
    (tendsto_toLp_of_eLpNorm_sub hm hW h)).congr hW.coeFn_toLp

/-- Joint Gaussian closure for raw random variables, preserving their given representatives. -/
theorem isGaussianProcess_of_eLpNorm_sub {T : Type*}
    (Z : ℕ → T → Ω → ℝ) (W : T → Ω → ℝ)
    (hZ : ∀ n, IsGaussianProcess (Z n) P) (hW : ∀ t, MemLp (W t) 2 P)
    (h : ∀ t, Tendsto (fun n => eLpNorm (fun ω => Z n t ω - W t ω) 2 P)
      atTop (𝓝 0)) : IsGaussianProcess W P := by
  let U (n : ℕ) (t : T) : Lp ℝ 2 P := (hZ n |>.hasGaussianLaw_eval t).memLp_two.toLp (Z n t)
  let V (t : T) : Lp ℝ 2 P := (hW t).toLp (W t)
  have hg n : IsGaussianProcess (fun t => ⇑(U n t)) P :=
    (hZ n).congr fun t => (hZ n |>.hasGaussianLaw_eval t).memLp_two.coeFn_toLp.symm
  have hl t : Tendsto (fun n => U n t) atTop (𝓝 (V t)) :=
    tendsto_toLp_of_eLpNorm_sub (fun n => (hZ n |>.hasGaussianLaw_eval t).memLp_two)
      (hW t) (h t)
  exact (isGaussianProcess_of_tendsto_L2 U V hg hl).congr fun t => (hW t).coeFn_toLp

/-- Means converge in the exact raw-L² form used by `IsCircleAverage`. -/
theorem tendsto_integral_of_eLpNorm_sub {Z : ℕ → Ω → ℝ} {W : Ω → ℝ}
    (hZ : ∀ n, MemLp (Z n) 2 P) (hW : MemLp W 2 P)
    (h : Tendsto (fun n => eLpNorm (fun ω => Z n ω - W ω) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 (∫ ω, W ω ∂P)) := by
  have hl := tendsto_integral_of_tendsto_L2 (tendsto_toLp_of_eLpNorm_sub hZ hW h)
  simpa only [integral_congr_ae (MemLp.coeFn_toLp _)] using hl

omit [IsProbabilityMeasure P] in
/-- Covariance is unchanged by null-set changes to either representative. -/
theorem covariance_congr_ae {U V U' V' : Ω → ℝ}
    (hU : U =ᵐ[P] U') (hV : V =ᵐ[P] V') :
    covariance U V P = covariance U' V' P := by
  unfold covariance
  rw [integral_congr_ae hU, integral_congr_ae hV]
  apply integral_congr_ae
  filter_upwards [hU, hV] with ω hω hω'
  rw [hω, hω']

/-- Mixed covariances converge for two raw-L² limits. -/
theorem tendsto_covariance_of_eLpNorm_sub {U V : ℕ → Ω → ℝ} {U₀ V₀ : Ω → ℝ}
    (hU : ∀ n, MemLp (U n) 2 P) (hV : ∀ n, MemLp (V n) 2 P)
    (hU₀ : MemLp U₀ 2 P) (hV₀ : MemLp V₀ 2 P)
    (hUl : Tendsto (fun n => eLpNorm (fun ω => U n ω - U₀ ω) 2 P) atTop (𝓝 0))
    (hVl : Tendsto (fun n => eLpNorm (fun ω => V n ω - V₀ ω) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => covariance (U n) (V n) P) atTop (𝓝 (covariance U₀ V₀ P)) := by
  have hl := tendsto_covariance_of_tendsto_L2
    (tendsto_toLp_of_eLpNorm_sub hU hU₀ hUl) (tendsto_toLp_of_eLpNorm_sub hV hV₀ hVl)
  simpa only [covariance_congr_ae (MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _)] using hl

omit [IsProbabilityMeasure P] in
/-- Each test evaluation of an equator GFF has its prescribed centered Gaussian law. -/
theorem equatorGFF_test_hasLaw (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : TestFn) :
    ∃ v : ℝ≥0, (v : ℝ) = gffCov f f ∧ HasLaw (fun ω => X ω f) (gaussianReal 0 v) P := by
  obtain ⟨hm, v, hv, hl⟩ := hX.2 f
  exact ⟨v, hv, hm.aemeasurable, hl⟩

omit [IsProbabilityMeasure P] in
/-- The scalar law in `DOZZ.IsEquatorGFF` provides Gaussianity, without choosing a new random
realization. -/
theorem equatorGFF_test_hasGaussianLaw (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (f : TestFn) : HasGaussianLaw (fun ω => X ω f) P := by
  obtain ⟨v, _, hl⟩ := equatorGFF_test_hasLaw X hX f
  exact hl.hasGaussianLaw

omit [IsProbabilityMeasure P] in
/-- Test evaluations are in L². -/
theorem equatorGFF_test_memLp (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : TestFn) :
    MemLp (fun ω => X ω f) 2 P := (equatorGFF_test_hasGaussianLaw X hX f).memLp_two

omit [IsProbabilityMeasure P] in
/-- All test evaluations are centered. -/
theorem equatorGFF_test_integral (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : TestFn) :
    (∫ ω, X ω f ∂P) = 0 := by
  obtain ⟨v, _, hl⟩ := equatorGFF_test_hasLaw X hX f
  rw [hl.integral_eq, integral_id_gaussianReal]

omit [IsProbabilityMeasure P] in
/-- Their variances are the diagonal of the covariance `DOZZ.gffCov`. -/
theorem equatorGFF_test_variance (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : TestFn) :
    variance (fun ω => X ω f) P = gffCov f f := by
  obtain ⟨v, hv, hl⟩ := equatorGFF_test_hasLaw X hX f
  rw [hl.variance_eq, variance_id_gaussianReal, hv]

omit [IsProbabilityMeasure P] [MeasurableSpace Ω] in
/-- Samplewise linearity turns a finite linear combination into a single test evaluation. -/
theorem equatorGFF_test_linearCombination {ι : Type*} [Fintype ι]
    (X : Ω → Distr) (f : ι → TestFn) (a : ι → ℝ) (ω : Ω) :
    X ω (∑ i, a i • f i) = ∑ i, a i * X ω (f i) := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

omit [IsProbabilityMeasure P] in
/-- Every finite real linear combination of tests is Gaussian. -/
theorem equatorGFF_tests_isGaussianProcess (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    IsGaussianProcess (fun f : TestFn => fun ω => X ω f) P := by
  classical
  constructor
  intro I
  apply hasGaussianLaw_pi_of_linearCombinations (fun f : I => fun ω => X ω f.val)
    (fun f => (hX.2 f.val).1.aemeasurable)
  intro a
  simpa only [equatorGFF_test_linearCombination] using
    equatorGFF_test_hasGaussianLaw X hX (∑ i : I, a i • i.val)

omit [IsProbabilityMeasure P] in
/-- Test approximants indexed by an arbitrary family remain jointly Gaussian. -/
theorem equatorGFF_test_family_isGaussianProcess {T : Type*}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : T → TestFn) :
    IsGaussianProcess (fun t => fun ω => X ω (f t)) P :=
  (equatorGFF_tests_isGaussianProcess X hX).comp_right f

/-- A centered sequence has a centered L² limit. -/
theorem integral_eq_zero_of_eLpNorm_sub {Z : ℕ → Ω → ℝ} {W : Ω → ℝ}
    (hZ : ∀ n, MemLp (Z n) 2 P) (hW : MemLp W 2 P)
    (hmean : ∀ n, (∫ ω, Z n ω ∂P) = 0)
    (h : Tendsto (fun n => eLpNorm (fun ω => Z n ω - W ω) 2 P) atTop (𝓝 0)) :
    (∫ ω, W ω ∂P) = 0 := by
  have hl := tendsto_integral_of_eLpNorm_sub hZ hW h
  simp_rw [hmean] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

omit [IsProbabilityMeasure P] in
/-- Circle witnesses are measurable at each fixed center and logarithmic radius. -/
theorem circleAverage_measurable_eval (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) :
    Measurable (fun ω => Xc ω x r) :=
  (hc.1 r).comp (measurable_id.prodMk measurable_const)

omit [IsProbabilityMeasure P] in
/-- The Gaussian closure step for any family of energy-approximated circles. The approximating tests
are explicit inputs to this helper, not additional premises of
`DOZZ.circleAverage_isGaussianProcess`. -/
theorem circleAverage_gaussian_of_energy_approx {T : Type*}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (p : T → ℂ × ℝ) (f : ℕ → T → TestFn)
    (hf : ∀ t, Tendsto (fun n => circleEnergyGap (p t).1 (p t).2 (f n t))
      atTop (𝓝 0)) : IsGaussianProcess (fun t => fun ω => Xc ω (p t).1 (p t).2) P := by
  let _ := hX.1
  apply isGaussianProcess_of_eLpNorm_sub (fun n t ω => X ω (f n t))
    (fun t ω => Xc ω (p t).1 (p t).2)
  · intro n
    exact equatorGFF_test_family_isGaussianProcess X hX (f n)
  · intro t
    exact hc.2.1 (p t).1 (p t).2
  · intro t
    exact hc.2.2 (p t).1 (p t).2 (fun n => f n t) (hf t)

omit [IsProbabilityMeasure P] in
/-- Circle centering follows from one energy-approximating sequence. -/
theorem circleAverage_integral_of_energy_approx
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x : ℂ) (r : ℝ) (f : ℕ → TestFn)
    (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) :
    (∫ ω, Xc ω x r ∂P) = 0 := by
  let _ := hX.1
  exact integral_eq_zero_of_eLpNorm_sub (fun n => equatorGFF_test_memLp X hX (f n))
    (hc.2.1 x r) (fun n => equatorGFF_test_integral X hX (f n)) (hc.2.2 x r f hf)

omit [IsProbabilityMeasure P] in
/-- At the equator, the zero test is already an exact energy approximant. -/
theorem circleAverage_equator_ae_eq_zero
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) : (fun ω => Xc ω 0 0) =ᵐ[P] 0 := by
  have hgap : circleEnergyGap 0 0 (0 : TestFn) = 0 := by
    rw [DOZZ.circleEnergyGap_zero]
    change (∫ x : ℂ, ∫ y : ℂ, (0 : ℝ) * gffKernel x y * 0) = 0
    simp only [zero_mul, integral_zero]
  have hl := hc.2.2 0 0 (fun _ => (0 : TestFn)) (by
    simpa only [hgap] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  have hn : eLpNorm (fun ω => X ω (0 : TestFn) - Xc ω 0 0) 2 P = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hl
  have hz := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 hn
  filter_upwards [hz] with ω hω
  simpa only [map_zero, zero_sub, Pi.zero_apply, neg_eq_zero] using hω

omit [IsProbabilityMeasure P] in
/-- A common energy approximant identifies two circle witnesses up to a null set. -/
theorem circleAverage_ae_eq_of_energy_approx
    (X : Ω → Distr) (Xc Yc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (hy : IsCircleAverage P X Yc)
    (x : ℂ) (r : ℝ) (f : ℕ → TestFn)
    (hm : ∀ n, MemLp (fun ω => X ω (f n)) 2 P)
    (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) :
    (fun ω => Xc ω x r) =ᵐ[P] (fun ω => Yc ω x r) := by
  have hcL := tendsto_toLp_of_eLpNorm_sub hm (hc.2.1 x r) (hc.2.2 x r f hf)
  have hyL := tendsto_toLp_of_eLpNorm_sub hm (hy.2.1 x r) (hy.2.2 x r f hf)
  exact (MemLp.toLp_eq_toLp_iff (hc.2.1 x r) (hy.2.1 x r)).1
    (tendsto_nhds_unique hcL hyL)

omit [IsProbabilityMeasure P] in
/-- A circle witness has the centered Gaussian law whenever its energy approximation has been
proved. This helper discharges the probabilistic step but does not assert existence of the tests. -/
theorem circleAverage_hasGaussianLaw_of_energy_approx
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x : ℂ) (r : ℝ) (f : ℕ → TestFn)
    (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) :
    HasGaussianLaw (fun ω => Xc ω x r) P := by
  let _ := hX.1
  exact hasGaussianLaw_of_eLpNorm_sub (fun n => equatorGFF_test_hasGaussianLaw X hX (f n))
    (hc.2.1 x r) (hc.2.2 x r f hf)

/-- Polarization of the covariance `DOZZ.gffCov`, using the Hilbert realization
`DOZZ.equatorKernelLimitMap`. -/
theorem gffCov_add_self (f g : TestFn) :
    gffCov (f + g) (f + g) = gffCov f f + 2 * gffCov f g + gffCov g g := by
  simp_rw [← DOZZ.inner_equatorKernelLimitMap_eq_gffCov]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  rw [real_inner_comm (DOZZ.equatorKernelLimitMap g) (DOZZ.equatorKernelLimitMap f)]
  ring

omit [IsProbabilityMeasure P] in
/-- The scalar law in `DOZZ.IsEquatorGFF` and samplewise linearity determine the full test
covariance. -/
theorem equatorGFF_test_covariance (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (f g : TestFn) : covariance (fun ω => X ω f) (fun ω => X ω g) P = gffCov f g := by
  let _ := hX.1
  have hvar := equatorGFF_test_variance X hX (f + g)
  have hsum : (fun ω => X ω (f + g)) = (fun ω => X ω f + X ω g) :=
    funext fun ω => map_add (X ω) f g
  rw [hsum, variance_fun_add (equatorGFF_test_memLp X hX f) (equatorGFF_test_memLp X hX g),
    equatorGFF_test_variance X hX f, equatorGFF_test_variance X hX g, gffCov_add_self] at hvar
  linarith only [hvar]

omit [IsProbabilityMeasure P] in
/-- The covariance of any two energy-approximated circles is the limit of test covariances.
This is the probabilistic covariance transfer; the deterministic limit remains a separate lemma. -/
theorem circleAverage_covariance_limit_of_energy_approx
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (r s : ℝ) (f g : ℕ → TestFn)
    (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0))
    (hg : Tendsto (fun n => circleEnergyGap y s (g n)) atTop (𝓝 0)) :
    Tendsto (fun n => gffCov (f n) (g n)) atTop
      (𝓝 (covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P)) := by
  let _ := hX.1
  have hl := tendsto_covariance_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX (f n)) (fun n => equatorGFF_test_memLp X hX (g n))
    (hc.2.1 x r) (hc.2.1 y s) (hc.2.2 x r f hf) (hc.2.2 y s g hg)
  simpa only [equatorGFF_test_covariance X hX] using hl

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in
/-- Brownian finite-dimensional laws are determined by Gaussianity, centering and the minimum
covariance. This helper deliberately exposes each probabilistic prerequisite. -/
theorem preBrownian_of_gaussian_min_covariance (U : ℝ≥0 → Ω → ℝ)
    (hG : IsGaussianProcess U P) (hmean : ∀ t, (∫ ω, U t ω ∂P) = 0)
    (hcov : ∀ s t, covariance (U s) (U t) P = min (s : ℝ) t) :
    IsPreBrownianReal U P := by
  apply hG.isPreBrownianReal_of_covariance hmean
  intro s t hst
  rw [hcov s t, min_eq_left (NNReal.coe_le_coe.mpr hst)]

omit [IsProbabilityMeasure P] in
/-- Restricting an almost surely continuous space-radius witness to a continuous time curve
provides the path-continuity premise of Brownian motion. -/
theorem brownian_of_preBrownian_circle_path
    (Xc : Ω → ℂ → ℝ → ℝ) (p : ℝ≥0 → ℂ × ℝ) (hp : Continuous p)
    (hB : IsPreBrownianReal (fun t ω => Xc ω (p t).1 (p t).2) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun q : ℂ × ℝ => Xc ω q.1 q.2)) :
    IsBrownianReal (fun t ω => Xc ω (p t).1 (p t).2) P := by
  refine ⟨hB, ?_⟩
  filter_upwards [hcont] with ω hω
  exact hω.comp hp

omit [IsProbabilityMeasure P] in
/-- Subtracting a samplewise constant preserves continuity along a circle-average path. -/
theorem brownian_of_preBrownian_circle_increment_path
    (Xc : Ω → ℂ → ℝ → ℝ) (p : ℝ≥0 → ℂ × ℝ) (q : ℂ × ℝ) (hp : Continuous p)
    (hB : IsPreBrownianReal (fun t ω => Xc ω (p t).1 (p t).2 - Xc ω q.1 q.2) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun v : ℂ × ℝ => Xc ω v.1 v.2)) :
    IsBrownianReal (fun t ω => Xc ω (p t).1 (p t).2 - Xc ω q.1 q.2) P := by
  refine ⟨hB, ?_⟩
  filter_upwards [hcont] with ω hω
  exact (hω.comp hp).sub continuous_const

omit [IsProbabilityMeasure P] in
/-- Exterior-pinned evaluations are measurable without requiring a jointly continuous witness. -/
theorem exteriorPinnedEvaluation_measurable
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 0 < R) (f : TestFn) :
    Measurable (fun ω => exteriorPinnedEvaluation X Xc R hR ω f) := by
  exact (hX.2 f).1.sub
    ((circleAverage_measurable_eval X Xc hc 0 (-Real.log R)).mul_const _)

omit [IsProbabilityMeasure P] in
/-- The L² conjunct of `DOZZ.exteriorPinnedEvaluation_covariance` follows directly from the field
and witness predicates. Its explicit covariance is a separate analytic step. -/
theorem exteriorPinnedEvaluation_memLp
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 0 < R) (f : TestFn) :
    MemLp (fun ω => exteriorPinnedEvaluation X Xc R hR ω f) 2 P := by
  exact (equatorGFF_test_memLp X hX f).sub ((hc.2.1 0 (-Real.log R)).mul_const _)

omit [IsProbabilityMeasure P] in
/-- The restoration scalar is measurable. -/
theorem equatorRestorationScalar_measurable
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 0 < R) : Measurable (equatorRestorationScalar Xc R hR) :=
  (circleAverage_measurable_eval X Xc hc 0 0).sub
    (circleAverage_measurable_eval X Xc hc 0 (-Real.log R))

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in
/-- The equator-restoration scalar is the negative exterior circle value, up to a null set. -/
theorem equatorRestorationScalar_ae_eq_neg_circle
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 0 < R) :
    equatorRestorationScalar Xc R hR =ᵐ[P] fun ω => -Xc ω 0 (-Real.log R) := by
  filter_upwards [circleAverage_equator_ae_eq_zero X Xc hc] with ω hω
  change Xc ω 0 0 - Xc ω 0 (-Real.log R) = -Xc ω 0 (-Real.log R)
  rw [hω, Pi.zero_apply, zero_sub]

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in
/-- Algebraic expansion of the pinning covariance in the given realization. The mixed
circle/test covariances remain visible until their analytic identification is proved. -/
theorem exteriorPinnedEvaluation_covariance_expansion
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 0 < R) (f g : TestFn) :
    covariance (fun ω => exteriorPinnedEvaluation X Xc R hR ω f)
      (fun ω => exteriorPinnedEvaluation X Xc R hR ω g) P =
      gffCov f g - (∫ z : ℂ, g z) * covariance (fun ω => X ω f)
        (fun ω => Xc ω 0 (-Real.log R)) P -
      (∫ z : ℂ, f z) * covariance (fun ω => Xc ω 0 (-Real.log R)) (fun ω => X ω g) P +
      (∫ z : ℂ, f z) * (∫ z : ℂ, g z) * variance (fun ω => Xc ω 0 (-Real.log R)) P := by
  let _ := hX.1
  change covariance (fun ω => X ω f - Xc ω 0 (-Real.log R) * (∫ z : ℂ, f z))
    (fun ω => X ω g - Xc ω 0 (-Real.log R) * (∫ z : ℂ, g z)) P = _
  rw [covariance_fun_sub_fun_sub (equatorGFF_test_memLp X hX f)
    ((hc.2.1 0 (-Real.log R)).mul_const _) (equatorGFF_test_memLp X hX g)
    ((hc.2.1 0 (-Real.log R)).mul_const _), covariance_mul_const_left,
    covariance_mul_const_right, covariance_mul_const_right, covariance_mul_const_left,
    covariance_self (hc.2.1 0 (-Real.log R)).aemeasurable, equatorGFF_test_covariance X hX]
  ring

omit [IsProbabilityMeasure P] in
/-- Joint Gaussianity and centering of every witness, see [KRV, (hatGformula)] and
[KRV, (circleav)]. -/
theorem circleAverage_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsGaussianProcess (fun p : ℂ × ℝ => fun ω => Xc ω p.1 p.2) P ∧
      ∀ x r, (∫ ω, Xc ω x r ∂P) = 0 := by
  have hex (p : ℂ × ℝ) := exists_testFn_circleEnergyGap_tendsto_zero p.1 p.2
  choose f hf using hex
  refine ⟨?_, ?_⟩
  · exact circleAverage_gaussian_of_energy_approx X Xc hX hc id
      (fun n p => f p n) (fun p => (hf p).2.2)
  · intro x r
    exact circleAverage_integral_of_energy_approx X Xc hX hc x r (f (x, r))
      (hf (x, r)).2.2

omit [IsProbabilityMeasure P] in
/-- Actual energy approximants identify every pair of circle-average witnesses at each
fixed parameter. This is coordinatewise equality and does not require joint continuity. -/
theorem circleAverage_ae_eq (X : Ω → Distr) (Xc Yc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hy : IsCircleAverage P X Yc) (x : ℂ) (r : ℝ) :
    (fun ω => Xc ω x r) =ᵐ[P] fun ω => Yc ω x r := by
  obtain ⟨f, _, _, hf⟩ := exists_testFn_circleEnergyGap_tendsto_zero x r
  exact circleAverage_ae_eq_of_energy_approx X Xc Yc hc hy x r f
    (fun n => equatorGFF_test_memLp X hX (f n)) hf

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in
/-- Circles and arbitrary original test evaluations form a single jointly Gaussian family.
This is the jointly Gaussian family used to prove the independence of the radial field. -/
theorem circleAverage_tests_isGaussianProcess
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsGaussianProcess (fun t : (ℂ × ℝ) ⊕ TestFn =>
      Sum.elim (fun p => fun ω => Xc ω p.1 p.2) (fun f => fun ω => X ω f) t) P := by
  let _ := hX.1
  have hex (p : ℂ × ℝ) := exists_testFn_circleEnergyGap_tendsto_zero p.1 p.2
  choose f hf using hex
  let F : ℕ → (ℂ × ℝ) ⊕ TestFn → TestFn :=
    fun n => Sum.elim (fun p => f p n) id
  apply isGaussianProcess_of_eLpNorm_sub (fun n t ω => X ω (F n t))
    (fun t => Sum.elim (fun p => fun ω => Xc ω p.1 p.2) (fun f => fun ω => X ω f) t)
  · intro n
    exact equatorGFF_test_family_isGaussianProcess X hX (F n)
  · intro t
    cases t with
    | inl p => exact hc.2.1 p.1 p.2
    | inr g => exact equatorGFF_test_memLp X hX g
  · intro t
    cases t with
    | inl p => exact hc.2.2 p.1 p.2 (f p) (hf p).2.2
    | inr g =>
      simpa only [F, Sum.elim_inr, id_eq, sub_self, ← Pi.zero_def, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

omit [IsProbabilityMeasure P] in
/-- Two almost surely continuous circle witnesses agree simultaneously at every parameter
on one full-measure event, by coordinatewise uniqueness on a countable dense set. -/
theorem circleAverage_continuous_ae_eq
    (X : Ω → Distr) (Xc Yc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hy : IsCircleAverage P X Yc)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (hYc : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Yc ω p.1 p.2)) :
    ∀ᵐ ω ∂P, ∀ x r, Xc ω x r = Yc ω x r := by
  let p : ℕ → ℂ × ℝ := TopologicalSpace.denseSeq (ℂ × ℝ)
  have heq : ∀ᵐ ω ∂P, ∀ n, Xc ω (p n).1 (p n).2 = Yc ω (p n).1 (p n).2 :=
    ae_all_iff.mpr (fun n => circleAverage_ae_eq X Xc Yc hX hc hy (p n).1 (p n).2)
  filter_upwards [heq, hXc, hYc] with ω hω hcontX hcontY
  have hfun := (TopologicalSpace.denseRange_denseSeq (ℂ × ℝ)).equalizer hcontX hcontY (funext hω)
  intro x r
  exact congrFun hfun (x, r)

omit [IsProbabilityMeasure P] in
/-- Every witness has the exact deterministic circle self-energy as its variance. The mixed-circle
approximation identifies the cross term; the gap then identifies the planar self-energy, so no
variance premise is added to `DOZZ.circleAverage_isGaussianProcess`. -/
theorem circleAverage_covariance_self (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω x r) P = circleSelfEnergy x r := by
  obtain ⟨f, hg, hcross⟩ := exists_testFn_circleEnergyGap_and_cross_tendsto x r
  have hcross' : Tendsto (fun n => circleCross x r (f n)) atTop (𝓝 (circleSelfEnergy x r)) :=
    hcross x r
  have hlim : Tendsto (fun n => gffCov (f n) (f n)) atTop (𝓝 (circleSelfEnergy x r)) := by
    convert (hg.add (hcross'.const_mul 2)).sub_const (circleSelfEnergy x r) using 1
    · funext n
      unfold circleEnergyGap
      ring
    · congr 1
      ring
  exact tendsto_nhds_unique
    (circleAverage_covariance_limit_of_energy_approx X Xc hX hc x x r r f f hg hg) hlim

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in
/-- Subtracting one fixed coordinate preserves joint Gaussianity at arbitrary indices. -/
theorem isGaussianProcess_sub_fixed {T : Type*} {Z : T → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (q : T) :
    IsGaussianProcess (fun t ω => Z t ω - Z q ω) P := by
  classical
  apply hZ.of_isGaussianProcess
  intro t
  let I : Finset T := {t, q}
  let a : I := ⟨t, by simp [I]⟩
  let b : I := ⟨q, by simp [I]⟩
  let L : (I → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a : (I → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj b
  refine ⟨I, L, fun ω => ?_⟩
  simp only [L, sub_apply, ContinuousLinearMap.proj_apply, Finset.restrict_def, a, b]

omit [IsProbabilityMeasure P] in
/-- Differences of two reindexed coordinates form a jointly Gaussian family. -/
theorem isGaussianProcess_sub_reindexed {T S : Type*} {Z : T → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (p q : S → T) :
    IsGaussianProcess (fun s ω => Z (p s) ω - Z (q s) ω) P := by
  classical
  apply hZ.of_isGaussianProcess
  intro s
  let I : Finset T := {p s, q s}
  let a : I := ⟨p s, by simp [I]⟩
  let b : I := ⟨q s, by simp [I]⟩
  let L : (I → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a : (I → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj b
  refine ⟨I, L, fun ω => ?_⟩
  simp only [L, sub_apply, ContinuousLinearMap.proj_apply, Finset.restrict_def, a, b]

omit [IsProbabilityMeasure P] in
/-- Arbitrary circle-coordinate differences and original tests form one Gaussian family. -/
theorem circleAverage_increment_tests_isGaussianProcess {T S : Type*}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (p q : T → ℂ × ℝ) (g : S → TestFn) :
    IsGaussianProcess (Sum.elim
      (fun t ω => Xc ω (p t).1 (p t).2 - Xc ω (q t).1 (q t).2)
      (fun s ω => X ω (g s))) P := by
  classical
  have hG := circleAverage_tests_isGaussianProcess X Xc hX hc
  apply hG.of_isGaussianProcess
  intro t
  cases t with
  | inl u =>
    let I : Finset ((ℂ × ℝ) ⊕ TestFn) := {Sum.inl (p u), Sum.inl (q u)}
    let a : I := ⟨Sum.inl (p u), by simp [I]⟩
    let b : I := ⟨Sum.inl (q u), by simp [I]⟩
    let L : (I → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj a : (I → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj b
    refine ⟨I, L, fun ω => ?_⟩
    simp only [L, sub_apply, ContinuousLinearMap.proj_apply, Finset.restrict_def, a, b,
      Sum.elim_inl]
  | inr s =>
    let I : Finset ((ℂ × ℝ) ⊕ TestFn) := {Sum.inr (g s)}
    let a : I := ⟨Sum.inr (g s), by simp [I]⟩
    refine ⟨I, ContinuousLinearMap.proj a, fun ω => ?_⟩
    simp only [ContinuousLinearMap.proj_apply, Finset.restrict_def, a, Sum.elim_inr]

end DOZZ.Proofs
