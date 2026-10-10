/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.FiniteGaussian
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
/-!
# Uniform harmonic exponential moments

Inner-circle Poisson averaging and Jensen's inequality bound compact harmonic
exponentials by boundary moments. A quadratic inequality handles correlated
restoration and harmonic variables using only their centered Gaussian marginal
laws. The explicit constant depends on the fixed radii and moment order, before
any realization or center choice, and applies to the actual Poisson family.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
/-- The two signed exponentials dominate the exponential of an absolute value. -/
theorem exp_mul_abs_le_exp_add (l x : ℝ) :
    Real.exp (l*|x|) ≤ Real.exp (l*x)+Real.exp (-l*x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have he : l*(-x) = -l*x := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- Centered scalar Gaussian exponential moments with their actual variance. -/
theorem gaussian_centered_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Ω → ℝ) (hU : HasGaussianLaw U P) (hmean : (∫ ω, U ω ∂P) = 0) (l : ℝ) :
    (∫ ω, Real.exp (l*U ω) ∂P) = Real.exp (variance U P*l^2/2) := by
  have hl : HasLaw U (gaussianReal (∫ ω, U ω ∂P) (variance U P).toNNReal) P :=
    ⟨hU.aemeasurable,hU.map_eq_gaussianReal⟩
  have hm := mgf_gaussianReal hl l
  rw [hmean,zero_mul,zero_add,Real.coe_toNNReal _ (variance_nonneg U P)] at hm
  exact hm

/-- Both signed scalar Gaussian exponential moments are integrable. -/
theorem gaussian_integrable_exp_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Ω → ℝ) (hU : HasGaussianLaw U P) (l : ℝ) :
    Integrable (fun ω => Real.exp (l*U ω)) P := by
  let _ := hU.isProbabilityMeasure
  apply mgf_pos_iff.mp
  rw [mgf_gaussianReal (⟨hU.aemeasurable,hU.map_eq_gaussianReal⟩ :
    HasLaw U (gaussianReal (∫ ω, U ω ∂P) (variance U P).toNNReal) P)]
  exact Real.exp_pos _

/-- Exponential absolute Gaussian moments have an explicit finite bound. -/
theorem gaussian_lintegral_exp_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Ω → ℝ) (hU : HasGaussianLaw U P) (hmean : (∫ ω, U ω ∂P) = 0) (l : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|U ω|)) ∂P) ≤
      ENNReal.ofReal (2*Real.exp (variance U P*l^2/2)) := by
  have hi := (gaussian_integrable_exp_mul P U hU l).add (gaussian_integrable_exp_mul P U hU (-l))
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (l*U ω)+Real.exp (-l*U ω)) ∂P :=
      lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (exp_mul_abs_le_exp_add l (U ω)))
    _ = ENNReal.ofReal (∫ ω, Real.exp (l*U ω)+Real.exp (-l*U ω) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))).symm
    _ = _ := by
      rw [integral_add (gaussian_integrable_exp_mul P U hU l) (gaussian_integrable_exp_mul P U hU (-l)),
        gaussian_centered_mgf P U hU hmean l,gaussian_centered_mgf P U hU hmean (-l),neg_sq]
      congr 1
      ring

/-- Continuous functions on an almost surely compact support are integrable under finite laws. -/
theorem integrable_of_continuousOn_ae_compact {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] (K : Set E)
    (hK : IsCompact K) (f : E → ℝ) (hf : Measurable f) (hcont : ContinuousOn f K)
    (hmem : ∀ᵐ x ∂μ, x ∈ K) : Integrable f μ := by
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_norm_le
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hmem] with x hx
  exact hC _ (mem_image_of_mem f hx)
/-- Pullback of an interior continuous function to a smaller circle is continuous. -/
theorem continuousOn_innerCircle_pullback (c : ℂ) (ρ b : ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (f : ℂ → ℝ) (hf : ContinuousOn f (ball c ρ)) :
    ContinuousOn (fun u : ℂ => f (c+b • u)) (sphere (0 : ℂ) 1) := by
  apply hf.comp (by fun_prop)
  intro u hu
  rw [mem_ball_iff_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hb]
  have hn : ‖u‖ = 1 := by simpa only [mem_sphere_iff_norm,sub_zero] using hu
  rw [hn,mul_one]
  exact hbρ

/-- Every measurable observable continuous near the smaller circle is integrable for its Poisson law. -/
theorem integrable_innerCircle_unitPoissonMeasure (c z : ℂ) (ρ b : ℝ)
    (hb : 0 < b) (hbρ : b < ρ) (hz : z ∈ ball c b)
    (f : ℂ → ℝ) (hfm : Measurable f) (hfc : ContinuousOn f (ball c ρ)) :
    Integrable (fun u => f (c+b • u)) (unitPoissonMeasure c b z) := by
  let _ := unitPoissonMeasure_isProbability c z b hb hz
  apply integrable_of_continuousOn_ae_compact (unitPoissonMeasure c b z) (sphere (0 : ℂ) 1)
    (isCompact_sphere 0 1) _ (hfm.comp (by fun_prop))
    (continuousOn_innerCircle_pullback c ρ b hb hbρ f hfc)
  filter_upwards [ae_norm_unitPoissonMeasure c z b] with u hu
  simpa only [mem_sphere_iff_norm,sub_zero] using hu

/-- Jensen's inequality for a literal inner-circle Poisson law. -/
theorem exp_mul_poisson_average_le (c z : ℂ) (ρ b : ℝ)
    (hb : 0 < b) (hbρ : b < ρ) (hz : z ∈ ball c b)
    (f : ℂ → ℝ) (hfm : Measurable f) (hfc : ContinuousOn f (ball c ρ)) (l : ℝ) :
    Real.exp (l*(∫ u, f (c+b • u) ∂unitPoissonMeasure c b z)) ≤
      ∫ u, Real.exp (l*f (c+b • u)) ∂unitPoissonMeasure c b z := by
  let _ := unitPoissonMeasure_isProbability c z b hb hz
  have hconv : ConvexOn ℝ (univ : Set ℝ) (fun x => Real.exp (l*x)) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ α β hα hβ hsum
    change Real.exp (l*(α*x+β*y)) ≤ α*Real.exp (l*x)+β*Real.exp (l*y)
    rw [show l*(α*x+β*y) = α*(l*x)+β*(l*y) by ring]
    exact convexOn_exp.2 (mem_univ (l*x)) (mem_univ (l*y)) hα hβ hsum
  exact hconv.map_integral_le (by fun_prop) isClosed_univ (ae_of_all _ (fun _ => mem_univ _))
    (integrable_innerCircle_unitPoissonMeasure c z ρ b hb hbρ hz f hfm hfc)
    (integrable_innerCircle_unitPoissonMeasure c z ρ b hb hbρ hz
      (fun v => Real.exp (l*f v)) (by fun_prop) (by fun_prop))

/-- Literal harmonic functions are reproduced by the inner-circle Poisson probability. -/
theorem integral_innerCircle_harmonic_eq (c z : ℂ) (ρ b : ℝ)
    (hb : 0 < b) (hbρ : b < ρ) (hz : z ∈ ball c b)
    (f : ℂ → ℝ) (hfm : Measurable f)
    (hfh : InnerProductSpace.HarmonicOnNhd f (ball c ρ)) :
    (∫ u, f (c+b • u) ∂unitPoissonMeasure c b z) = f z := by
  rw [integral_unitPoissonMeasure c z b hb hz,
    integral_unitPoissonWeight_mul_eq_circleAverage c z b hb f hfm]
  exact (hfh.mono (closedBall_subset_ball hbρ)).circleAverage_poissonKernel_smul hz

/-- Continuous inner-circle observables are integrable under unweighted angular probability. -/
theorem integrable_innerCircle_circleMeasure (c : ℂ) (ρ b : ℝ) (hb : 0 < b) (hbρ : b < ρ)
    (f : ℂ → ℝ) (hfm : Measurable f) (hfc : ContinuousOn f (ball c ρ)) :
    Integrable (fun u => f (c+b • u)) (circleMeasure 0 0) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  apply integrable_of_continuousOn_ae_compact (circleMeasure 0 0) (sphere (0 : ℂ) 1)
    (isCompact_sphere 0 1) _ (hfm.comp (by fun_prop))
    (continuousOn_innerCircle_pullback c ρ b hb hbρ f hfc)
  filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
  simpa only [mem_sphere_iff_norm,sub_zero,neg_zero,Real.exp_zero] using hu

/-- A signed exponential on the boundary is bounded by the absolute exponential times the uniform weight. -/
theorem integral_unitPoisson_exp_le_uniform (c z : ℂ) (ρ b a : ℝ)
    (hb : 0 < b) (hbρ : b < ρ) (hab : a < b) (hz : z ∈ closedBall c a)
    (f : ℂ → ℝ) (hfm : Measurable f) (hfc : ContinuousOn f (ball c ρ))
    (l t : ℝ) (ht : |t| ≤ l) :
    (∫ u, Real.exp (t*f (c+b • u)) ∂unitPoissonMeasure c b z) ≤
      b^2/(b-a)^2*(∫ u, Real.exp (l*|f (c+b • u)|) ∂circleMeasure 0 0) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  have hz' : z ∈ ball c b := closedBall_subset_ball hab hz
  rw [integral_unitPoissonMeasure c z b hb hz',← integral_const_mul]
  apply integral_mono_ae
  · have hi := integrable_innerCircle_unitPoissonMeasure c z ρ b hb hbρ hz'
      (fun v => Real.exp (t*f v)) (by fun_prop) (by fun_prop)
    rw [unitPoissonMeasure,integrable_withDensity_iff_integrable_smul'
      (measurable_unitPoissonWeight c z b).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at hi
    simpa only [ENNReal.toReal_ofReal (unitPoissonWeight_nonneg c z _ b hb hz'),smul_eq_mul] using hi
  · exact (integrable_innerCircle_circleMeasure c ρ b hb hbρ
      (fun v => Real.exp (l*|f v|)) (by fun_prop) (by fun_prop)).const_mul _
  · filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
    have hu' : ‖u‖ = 1 := by simpa only [sub_zero,neg_zero,Real.exp_zero] using hu
    have he : t*f (c+b • u) ≤ l*|f (c+b • u)| := calc
      _ ≤ |t*f (c+b • u)| := le_abs_self _
      _ = |t| * |f (c+b • u)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    exact mul_le_mul (unitPoissonWeight_le c z u b a hb hab (mem_closedBall_iff_norm.mp hz) hu')
      (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- An inner-circle boundary exponential controls the harmonic exponential uniformly on compact disks. -/
theorem exp_abs_harmonic_le_innerCircle (c z : ℂ) (ρ b a : ℝ)
    (hb : 0 < b) (hbρ : b < ρ) (hab : a < b) (hz : z ∈ closedBall c a)
    (f : ℂ → ℝ) (hfm : Measurable f)
    (hfh : InnerProductSpace.HarmonicOnNhd f (ball c ρ)) (hfc : ContinuousOn f (ball c ρ))
    (l : ℝ) (hl : 0 ≤ l) :
    Real.exp (l*|f z|) ≤ 2*(b^2/(b-a)^2)*
      (∫ u, Real.exp (l*|f (c+b • u)|) ∂circleMeasure 0 0) := by
  have hz' : z ∈ ball c b := closedBall_subset_ball hab hz
  have hj t := exp_mul_poisson_average_le c z ρ b hb hbρ hz' f hfm hfc t
  rw [integral_innerCircle_harmonic_eq c z ρ b hb hbρ hz' f hfm hfh] at hj
  have hp := integral_unitPoisson_exp_le_uniform c z ρ b a hb hbρ hab hz f hfm hfc l l (by rw [abs_of_nonneg hl])
  have hn := integral_unitPoisson_exp_le_uniform c z ρ b a hb hbρ hab hz f hfm hfc l (-l) (by rw [abs_neg,abs_of_nonneg hl])
  have ht := (exp_mul_abs_le_exp_add l (f z)).trans (add_le_add ((hj l).trans hp) ((hj (-l)).trans hn))
  calc
    _ ≤ _ := ht
    _ = _ := by ring

/-- A deterministic variance upper bound gives a realization-independent absolute moment bound. -/
theorem gaussian_lintegral_exp_abs_le_of_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → ℝ) (hU : HasGaussianLaw U P)
    (hmean : (∫ ω, U ω ∂P) = 0) (v : ℝ) (hv : variance U P ≤ v) (l : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|U ω|)) ∂P) ≤ ENNReal.ofReal (2*Real.exp (v*l^2/2)) := by
  apply (gaussian_lintegral_exp_abs_le P U hU hmean l).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (sq_nonneg l)) (by norm_num)

/-- A quadratic estimate controls correlated positive exponential factors. -/
theorem exp_mul_exp_le_doubled_add (x y : ℝ) :
    Real.exp x*Real.exp y ≤ Real.exp (2*x)+Real.exp (2*y) := by
  have h := sq_nonneg (Real.exp x-Real.exp y)
  have he (t : ℝ) : Real.exp (2*t) = (Real.exp t)^2 := by
    rw [two_mul,Real.exp_add,pow_two]
  rw [he,he]
  nlinarith only [h,sq_nonneg (Real.exp x),sq_nonneg (Real.exp y)]

/-- Two centered Gaussian marginal laws suffice to bound their correlated absolute exponential product. -/
theorem gaussian_product_lintegral_exp_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U V : Ω → ℝ) (hU : HasGaussianLaw U P) (hV : HasGaussianLaw V P)
    (hmeanU : (∫ ω, U ω ∂P) = 0) (hmeanV : (∫ ω, V ω ∂P) = 0)
    (u v : ℝ) (hu : variance U P ≤ u) (hv : variance V P ≤ v) (l : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|U ω|))*ENNReal.ofReal (Real.exp (l*|V ω|)) ∂P) ≤
      ENNReal.ofReal (2*(Real.exp (u*(2*l)^2/2)+Real.exp (v*(2*l)^2/2))) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ((2*l)*|U ω|))+ENNReal.ofReal (Real.exp ((2*l)*|V ω|)) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using exp_mul_exp_le_doubled_add (l*|U ω|) (l*|V ω|)
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp ((2*l)*|U ω|)) ∂P)+
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((2*l)*|V ω|)) ∂P) :=
      lintegral_add_left' ((continuous_abs.measurable.comp_aemeasurable hU.aemeasurable).const_mul (2*l) |>.exp.ennreal_ofReal) _
    _ ≤ ENNReal.ofReal (2*Real.exp (u*(2*l)^2/2))+ENNReal.ofReal (2*Real.exp (v*(2*l)^2/2)) :=
      add_le_add (gaussian_lintegral_exp_abs_le_of_variance_le P U hU hmeanU u hu (2*l))
        (gaussian_lintegral_exp_abs_le_of_variance_le P V hV hmeanV v hv (2*l))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The absolute exponential of a measurable real observable is measurable. -/
theorem measurable_ofReal_exp_mul_abs {E : Type*} [MeasurableSpace E]
    (U : E → ℝ) (hU : Measurable U) (l : ℝ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (l*|U x|))) := by
  have ha : Measurable (fun x => |U x|) := continuous_abs.measurable.comp hU
  have hm : Measurable (fun x => l*|U x|) := measurable_const.mul ha
  have he : Measurable (fun x => Real.exp (l*|U x|)) := Real.continuous_exp.measurable.comp hm
  exact he.ennreal_ofReal

/-- Restriction of a jointly measurable field to translated circle parameters is jointly measurable. -/
theorem measurable_innerCircle_field {Ω : Type*} [MeasurableSpace Ω]
    (c : ℂ) (b : ℝ) (V : Ω → ℂ → ℝ)
    (hV : Measurable (fun p : Ω × ℂ => V p.1 p.2)) :
    Measurable (fun p : Ω × ℂ => V p.1 (c+b • p.2)) := by
  have hm : Measurable (fun p : Ω × ℂ => c+b • p.2) := by fun_prop
  exact hV.comp (measurable_fst.prodMk hm)

/-- Explicit compact harmonic moment constant from two marginal variances. -/
noncomputable def harmonicMomentBound (b a u v l : ℝ) : ℝ :=
  4*(b^2/(b-a)^2)*(Real.exp (u*(2*l)^2/2)+Real.exp (v*(2*l)^2/2))

/-- The deterministic harmonic moment constant is strictly positive. -/
theorem harmonicMomentBound_pos (b a u v l : ℝ) (hb : 0 < b) (hab : a < b) :
    0 < harmonicMomentBound b a u v l := by
  unfold harmonicMomentBound
  exact mul_pos (mul_pos (by norm_num) (div_pos (sq_pos_of_pos hb) (sq_pos_of_pos (sub_pos.mpr hab))))
    (add_pos (Real.exp_pos _) (Real.exp_pos _))

/-- Uniform exponential compact supremum moments need only centered Gaussian marginal boundary laws. -/
theorem harmonic_lintegral_exp_sup_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (ρ b a : ℝ)
    (hb : 0 < b) (hbρ : b < ρ) (hab : a < b)
    (U : Ω → ℝ) (hUm : Measurable U) (hUg : HasGaussianLaw U P)
    (hUmean : (∫ ω, U ω ∂P) = 0) (u : ℝ) (hUvar : variance U P ≤ u)
    (V : Ω → ℂ → ℝ) (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧ ContinuousOn (V ω) (ball c ρ))
    (v : ℝ) (hVboundary : ∀ w : ℂ, ‖w‖ = 1 →
      HasGaussianLaw (fun ω => V ω (c+b • w)) P ∧
      (∫ ω, V ω (c+b • w) ∂P) = 0 ∧ variance (fun ω => V ω (c+b • w)) P ≤ v)
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|U ω|))*
      ⨆ z ∈ closedBall c a, ENNReal.ofReal (Real.exp (l*|V ω z|)) ∂P) ≤
      ENNReal.ofReal (harmonicMomentBound b a u v l) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  let K := 2*(b^2/(b-a)^2)
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (sq_nonneg _))
  let F : Ω → ℂ → ℝ≥0∞ := fun ω w =>
    ENNReal.ofReal (Real.exp (l*|U ω|))*ENNReal.ofReal (Real.exp (l*|V ω (c+b • w)|))
  have hFm : Measurable (Function.uncurry F) := by
    have hleft := measurable_ofReal_exp_mul_abs (fun p : Ω × ℂ => U p.1)
      (hUm.comp measurable_fst) l
    have hright := measurable_ofReal_exp_mul_abs (fun p : Ω × ℂ => V p.1 (c+b • p.2))
      (measurable_innerCircle_field c b V hVm) l
    exact hleft.mul hright
  have hsup : ∀ᵐ ω ∂P, (⨆ z ∈ closedBall c a, ENNReal.ofReal (Real.exp (l*|V ω z|))) ≤
      ENNReal.ofReal K*(∫⁻ w, ENNReal.ofReal (Real.exp (l*|V ω (c+b • w)|)) ∂circleMeasure 0 0) := by
    filter_upwards [hVh] with ω hω
    have hm : Measurable (V ω) := hVm.comp (measurable_const.prodMk measurable_id)
    have hi := integrable_innerCircle_circleMeasure c ρ b hb hbρ
      (fun z => Real.exp (l*|V ω z|)) (by fun_prop) (Real.continuous_exp.comp_continuousOn (hω.2.abs.const_mul l))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
      ← ENNReal.ofReal_mul hK]
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    exact ENNReal.ofReal_le_ofReal
      (exp_abs_harmonic_le_innerCircle c z ρ b a hb hbρ hab hz (V ω) hm hω.1 hω.2 l hl.le)
  have hboundary : (∫⁻ w, ∫⁻ ω, F ω w ∂P ∂circleMeasure 0 0) ≤
      ENNReal.ofReal (2*(Real.exp (u*(2*l)^2/2)+Real.exp (v*(2*l)^2/2))) := by
    calc
      _ ≤ ∫⁻ _w, ENNReal.ofReal (2*(Real.exp (u*(2*l)^2/2)+Real.exp (v*(2*l)^2/2))) ∂circleMeasure 0 0 := by
        apply lintegral_mono_ae
        filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with w hw
        have hw' : ‖w‖ = 1 := by simpa only [sub_zero,neg_zero,Real.exp_zero] using hw
        obtain ⟨hg,hm,hvar⟩ := hVboundary w hw'
        exact gaussian_product_lintegral_exp_abs_le P U (fun ω => V ω (c+b • w))
          hUg hg hUmean hm u v hUvar hvar l
      _ = _ := by rw [lintegral_const,measure_univ,mul_one]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal K*(∫⁻ w, F ω w ∂circleMeasure 0 0) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hsup] with ω hω
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact (mul_le_mul_right hω (ENNReal.ofReal (Real.exp (l*|U ω|)))).trans_eq (by ac_rfl)
    _ = ENNReal.ofReal K*(∫⁻ w, ∫⁻ ω, F ω w ∂P ∂circleMeasure 0 0) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_lintegral_swap hFm.aemeasurable]
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal (2*(Real.exp (u*(2*l)^2/2)+Real.exp (v*(2*l)^2/2))) :=
      mul_le_mul_right hboundary _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      unfold K harmonicMomentBound
      ring

/-- The actual restoration scalar is centered Gaussian with exterior pin variance. -/
theorem equatorRestorationScalar_gaussian_mean_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 1 < R) :
    HasGaussianLaw (equatorRestorationScalar Xc R (by linarith)) P ∧
    (∫ ω, equatorRestorationScalar Xc R (by linarith) ω ∂P) = 0 ∧
    variance (equatorRestorationScalar Xc R (by linarith)) P = Real.log R := by
  let _ := hX.1
  obtain ⟨hg,hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hae := equatorRestorationScalar_ae_eq_neg_circle X Xc hc R (by linarith)
  refine ⟨(hg.hasGaussianLaw_eval (0,-Real.log R)).fun_neg.congr hae.symm,?_,?_⟩
  · rw [integral_congr_ae hae,integral_neg,hm,neg_zero]
  · rw [variance_congr hae,variance_fun_neg,← covariance_self (hc.2.1 0 (-Real.log R)).aemeasurable,
      circleAverage_covariance_self X Xc hX hc,circleSelfEnergy_exterior_origin R hR]

/-- The exact closed harmonic covariance gives one variance on every concentric boundary circle. -/
theorem poisson_harmonic_boundary_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (R ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b < ρ)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (w : ℂ) (hw : ‖w‖ = 1) :
    variance (fun ω => V ω (c+b • w)) P = Real.log R+Real.log ρ-Real.log (ρ^2-b^2) := by
  have hn : ‖c+b • w-c‖ = b := by
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hb,hw,mul_one]
  have hz : c+b • w ∈ ball c ρ := mem_ball_iff_norm.mpr (hn.trans_lt hbρ)
  rw [← covariance_self (hV _ hz).aemeasurable,hcov _ _ hz hz,
    norm_diskGreen_numerator_self c _ ρ hρ hz,hn]

/-- A deterministic inner radius accommodates every compact target radius, including negative targets. -/
noncomputable def harmonicMomentRadius (ρ a : ℝ) : ℝ := (max a 0+ρ)/2

/-- The chosen inner radius is positive and lies strictly between the target and the disk boundary. -/
theorem harmonicMomentRadius_bounds (ρ a : ℝ) (hρ : 0 < ρ) (haρ : a < ρ) :
    0 < harmonicMomentRadius ρ a ∧ a < harmonicMomentRadius ρ a ∧ harmonicMomentRadius ρ a < ρ := by
  have hm : max a 0 < ρ := max_lt haρ hρ
  have hma : a ≤ max a 0 := le_max_left _ _
  have hm0 : 0 ≤ max a 0 := le_max_right _ _
  unfold harmonicMomentRadius
  constructor
  · linarith only [hρ,hm0]
  constructor <;> linarith only [hm,hma]

/-- A moment bound preceding all realizations and disk-center choices. -/
noncomputable def exteriorPinnedHarmonicMomentBound (R ρ a l : ℝ) : ℝ :=
  harmonicMomentBound (harmonicMomentRadius ρ a) a (Real.log R)
    (Real.log R+Real.log ρ-Real.log (ρ^2-(harmonicMomentRadius ρ a)^2)) l

/-- The realization-independent exterior-pinned harmonic bound is positive. -/
theorem exteriorPinnedHarmonicMomentBound_pos (R ρ a l : ℝ) (hρ : 0 < ρ) (haρ : a < ρ) :
    0 < exteriorPinnedHarmonicMomentBound R ρ a l :=
  harmonicMomentBound_pos _ _ _ _ _ (harmonicMomentRadius_bounds ρ a hρ haρ).1
    (harmonicMomentRadius_bounds ρ a hρ haρ).2.1

/-- The actual harmonic Poisson family has the all-order uniform moment bound required by
`DOZZ.exists_exteriorPinned_markov_uniform`. -/
theorem exteriorPinned_harmonic_uniform_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ a : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (haρ : a < ρ)
    (V : Ω → ℂ → ℝ) (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (V ω) (ball c ρ))
    (hG : IsGaussianProcess (fun z : {z : ℂ // z ∈ ball c ρ} => fun ω => V ω z.1) P)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|equatorRestorationScalar Xc R (by linarith) ω|))*
      ⨆ z ∈ closedBall c a, ENNReal.ofReal (Real.exp (l*|V ω z|)) ∂P) ≤
      ENNReal.ofReal (exteriorPinnedHarmonicMomentBound R ρ a l) := by
  let _ := hX.1
  obtain ⟨hb,hab,hbρ⟩ := harmonicMomentRadius_bounds ρ a hρ haρ
  obtain ⟨hUg,hUm,hUv⟩ := equatorRestorationScalar_gaussian_mean_variance P X Xc hX hc R hR
  apply harmonic_lintegral_exp_sup_le P c ρ (harmonicMomentRadius ρ a) a hb hbρ hab
    (equatorRestorationScalar Xc R (by linarith))
    (equatorRestorationScalar_measurable X Xc hc R (by linarith)) hUg hUm (Real.log R) hUv.le
    V hVm _ _ _ l hl
  · filter_upwards [hVh] with ω hω
    exact ⟨hω.1,hω.2.continuousOn⟩
  · intro w hw
    have hn : ‖c+harmonicMomentRadius ρ a • w-c‖ = harmonicMomentRadius ρ a := by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hb,hw,mul_one]
    have hz : c+harmonicMomentRadius ρ a • w ∈ ball c ρ := mem_ball_iff_norm.mpr (hn.trans_lt hbρ)
    exact ⟨hG.hasGaussianLaw_eval ⟨_,hz⟩,hmean _ hz,
      (poisson_harmonic_boundary_variance P c R ρ _ hρ hb hbρ V hV hcov w hw).le⟩

end DOZZ.Proofs
