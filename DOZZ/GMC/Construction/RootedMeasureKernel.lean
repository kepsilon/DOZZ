/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCircleKernel
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! Joint measurability of inserted measures with a varying root. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Integrating a jointly measurable function against a measurable family of finite measures
is measurable; the masses of the family need not have a common bound. -/
theorem measurable_lintegral_finite_family
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u))
    (f : U × E → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun u => ∫⁻ x, f (u, x) ∂μ u) := by
  let κ : Kernel U E := ⟨μ, hμ⟩
  let F : ℕ → SimpleFunc (U × E) ℝ≥0∞ := SimpleFunc.eapprox f
  have heq : ∀ u x, (⨆ n, F n (u, x)) = f (u, x) :=
    fun u x => SimpleFunc.iSup_eapprox_apply hf (u, x)
  simp_rw [← heq]
  have hi : ∀ u, (∫⁻ x, ⨆ n, F n (u, x) ∂μ u) =
      ⨆ n, ∫⁻ x, F n (u, x) ∂μ u := by
    intro u
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij x => SimpleFunc.monotone_eapprox f hij (u, x)
  simp_rw [hi]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun g => Measurable (fun u => ∫⁻ x, g (u, x) ∂μ u)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    have hind : (fun u => ∫⁻ x, t.indicator (fun _ => c) (u, x) ∂μ u) =
        fun u => c * μ u (Prod.mk u ⁻¹' t) := by
      funext u
      exact lintegral_indicator_const_comp (f := Prod.mk u) measurable_prodMk_left ht c
    rw [← Function.const_def, hind]
    exact Measurable.const_mul
      (Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) ht hfinite) c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have hadd : (fun u => ∫⁻ x, g₁ (u, x) + g₂ (u, x) ∂μ u) =
        (fun u => ∫⁻ x, g₁ (u, x) ∂μ u) + fun u => ∫⁻ x, g₂ (u, x) ∂μ u := by
      funext u
      rw [Pi.add_apply]
      have hg : Measurable (fun x : E => g₁ (u, x)) :=
        g₁.measurable.comp measurable_prodMk_left
      exact lintegral_add_left hg _
    rw [hadd]
    exact hm₁.add hm₂

/-- A jointly measurable density preserves measurability of a finite random-measure family,
even when the inserted measures themselves have infinite mass. -/
theorem measurable_withDensity_finite_family
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u))
    (w : U × E → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun u => (μ u).withDensity (fun x => w (u, x))) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  exact measurable_lintegral_finite_family μ hμ hfinite
    (fun q => (A.indicator (fun x => w (q.1, x))) q.2)
    (hw.indicator (hA.preimage measurable_snd))

/-- The circle average of a measurable real function is measurable in its center. -/
theorem measurable_circleAverage_center
    (f : ℂ → ℝ) (hf : Measurable f) (R : ℝ) :
    Measurable (fun u : ℂ => Real.circleAverage f u R) := by
  have hg : Measurable (fun q : ℂ × ℝ => f (circleMap q.1 R q.2)) := by
    apply hf.comp
    exact (show Continuous (fun q : ℂ × ℝ => circleMap q.1 R q.2) by
      fun_prop [circleMap]).measurable
  have hint : Measurable (fun u : ℂ =>
      ∫ θ, f (circleMap u R θ) ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    hg.stronglyMeasurable.integral_prod_right.measurable
  simp only [Real.circleAverage_def, intervalIntegral.integral_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi), smul_eq_mul]
  exact measurable_const.mul hint

/-- The one-circle root potential is jointly measurable in root and spatial point. -/
theorem measurable_circleRootPotential (r : ℝ) :
    Measurable (fun q : ℂ × ℂ => ∫ v, gffKernel q.2 v ∂circleMeasure q.1 r) := by
  have hpin : Measurable (fun u : ℂ =>
      ∫ v, Real.log (normPlus v) ∂circleMeasure u r) := by
    have h := measurable_circleAverage_center (fun v => Real.log (normPlus v))
      continuous_log_normPlus.measurable (Real.exp (-r))
    simpa only [CirclePotential.integral_circleMeasure_eq_circleAverage
      continuous_log_normPlus.measurable] using h
  have hlog : Measurable (fun q : ℂ × ℂ =>
      Real.log (max (Real.exp (-r)) ‖q.1 - q.2‖)) :=
    Real.measurable_log.comp (measurable_const.max
      (measurable_fst.sub measurable_snd).norm)
  simp_rw [integral_gffKernel_circleMeasure]
  exact (hlog.neg.add (continuous_log_normPlus.measurable.comp measurable_snd)).add
    (hpin.comp measurable_fst)

/-- The point potential is jointly measurable, including its prescribed value on the diagonal. -/
theorem measurable_pointRootPotential :
    Measurable (fun q : ℂ × ℂ => gffKernel q.1 q.2) := by
  unfold gffKernel
  exact ((Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).neg.add
    (continuous_log_normPlus.measurable.comp measurable_fst)).add
      (continuous_log_normPlus.measurable.comp measurable_snd)

/-- The singular inserted measure is jointly measurable in root and sample. -/
theorem measurable_gmcRootedMeasure_family
    {Ω : Type*} [MeasurableSpace Ω]
    (M : Ω → Measure ℂ) (hM : Measurable M) (hfinite : ∀ ω, IsFiniteMeasure (M ω))
    (γ : ℝ) : Measurable (fun q : ℂ × Ω => gmcRootedMeasure γ q.1 (M q.2)) := by
  apply measurable_withDensity_finite_family (fun q : ℂ × Ω => M q.2)
    (hM.comp measurable_snd) (fun q => hfinite q.2)
    (fun q : (ℂ × Ω) × ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel q.1.1 q.2)))
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_pointRootPotential.comp
      (f := fun q : (ℂ × Ω) × ℂ => (q.1.1, q.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))

/-- The one-circle inserted measure is jointly measurable in root and sample. -/
theorem measurable_circleRootedMeasure_family
    {Ω : Type*} [MeasurableSpace Ω]
    (M : Ω → Measure ℂ) (hM : Measurable M) (hfinite : ∀ ω, IsFiniteMeasure (M ω))
    (γ r : ℝ) : Measurable (fun q : ℂ × Ω =>
      (M q.2).withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure q.1 r)))) := by
  apply measurable_withDensity_finite_family (fun q : ℂ × Ω => M q.2)
    (hM.comp measurable_snd) (fun q => hfinite q.2)
    (fun q : (ℂ × Ω) × ℂ => ENNReal.ofReal
      (Real.exp (γ ^ 2 * ∫ v, gffKernel q.2 v ∂circleMeasure q.1.1 r)))
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_circleRootPotential r).comp
      (f := fun q : (ℂ × Ω) × ℂ => (q.1.1, q.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))

/-- A circle-root covariance with a test is measurable in the root. -/
theorem measurable_circleCross_center (r : ℝ) (f : TestFn) :
    Measurable (fun u : ℂ => circleCross u r f) := by
  let k : ℂ → ℝ := fun u => gffRootCovariance u f
  have hk : Measurable k := (gffRootCovariance_continuous f).measurable
  have heq : (fun u : ℂ => circleCross u r f) =
      fun u => Real.circleAverage k u (Real.exp (-r)) := by
    funext u
    rw [circleCross_eq_integral_testKernel]
    exact CirclePotential.integral_circleMeasure_eq_circleAverage hk u r
  rw [heq]
  exact measurable_circleAverage_center k hk _

end DOZZ.Proofs
