/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionChaosMeasure
@[expose] public section
open MeasureTheory Filter
open scoped Distributions Topology ENNReal
namespace DOZZ.Proofs

/-- A constant shift cancels after integration against a bounded continuous weight. -/
theorem symmetry_integral_shift_cancel (μ : Measure ℂ) [IsFiniteMeasure μ]
    (g w : BoundedContinuousFunction ℂ ℝ) (c : ℝ) :
    (∫ x, (g x + c) * w x ∂μ) - (∫ x, c * w x ∂μ) = ∫ x, g x * w x ∂μ := by
  have hi : Integrable (fun x => g x * w x) μ := (g * w).integrable μ
  have hc : Integrable (fun x => c * w x) μ := (w.integrable μ).const_mul c
  have he : (fun x => (g x + c) * w x) = fun x => g x * w x + c * w x := by
    funext x
    ring
  rw [he, integral_add hi hc, add_sub_cancel_right]

/-- Reflection and correlated re-pinning identify the ordinary limiting chaos on the same
probability space, rather than just identifying its marginal law. -/
theorem isGMCOf_symmetryRepinnedChaos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    IsGMCOf P (symmetryRepinnedField X (fun ω => Xc ω 1 0)) γ
      (symmetryRepinnedChaos γ M (fun ω => Xc ω 1 0)) := by
  let : IsProbabilityMeasure P := hX.1
  refine ⟨symmetryRepinnedChaos_finite γ M _ hM.1,
    (fun ω x r => Xc ω (1 - x) r - Xc ω 1 0),
    isCircleAverage_symmetryRepinned P X hX Xc hXc, ?_⟩
  intro f
  let φ : ContinuousMap ℂ ℂ := ⟨fun x => 1 - x, continuous_const.sub continuous_id⟩
  let g := f.compContinuous φ
  let C : BoundedContinuousFunction ℂ ℝ := BoundedContinuousFunction.const ℂ ‖f‖
  let w : ℝ → BoundedContinuousFunction ℂ ℝ := fun r =>
    (symmetryReflectionCutoffWeight γ r).compContinuous φ
  let v := (symmetryReflectionLimitWeight γ).compContinuous φ
  have hw (r : ℝ) (x : ℂ) : 0 ≤ w r x := by
    change 0 ≤ symmetryReflectionCutoffWeight γ r (1 - x)
    rw [symmetryReflectionCutoffWeight_apply]
    exact (Real.exp_pos _).le
  have hv (x : ℂ) : 0 ≤ v x := by
    change 0 ≤ symmetryReflectionLimitWeight γ (1 - x)
    rw [symmetryReflectionLimitWeight_apply]
    exact (Real.exp_pos _).le
  have hg (x : ℂ) : 0 ≤ (g + C) x := by
    change 0 ≤ f (1 - x) + ‖f‖
    have h := f.norm_coe_le_norm (1 - x)
    rw [Real.norm_eq_abs] at h
    linarith only [neg_abs_le (f (1 - x)), h]
  have hwconv : Tendsto w atTop (𝓝 v) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
      ((symmetryReflectionCutoffWeight_uniform γ).comp (fun x : ℂ => 1 - x))
  have hA := regularizedGMC_varying_bcf_integral P X hX Xc hXc γ M hM
    (fun r => (g + C) * w r) (fun r x => by
      change 0 ≤ (g + C) x * w r x
      exact mul_nonneg (hg x) (hw r x))
    ((g + C) * v) (fun x => by
      change 0 ≤ (g + C) x * v x
      exact mul_nonneg (hg x) (hv x))
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (tendsto_const_nhds.mul hwconv))
  have hB := regularizedGMC_varying_bcf_integral P X hX Xc hXc γ M hM
    (fun r => C * w r) (fun r x => by
      change 0 ≤ ‖f‖ * w r x
      exact mul_nonneg (norm_nonneg _) (hw r x))
    (C * v) (fun x => by
      change 0 ≤ ‖f‖ * v x
      exact mul_nonneg (norm_nonneg _) (hv x))
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (tendsto_const_nhds.mul hwconv))
  have hsub := tendstoInMeasure_sub_same_space _ _ _ _ hA hB
  have hsigned : TendstoInMeasure P
      (fun r ω => ∫ x, f (1 - x) * symmetryReflectionCutoffWeight γ r (1 - x)
        ∂regularizedGMC P Xc γ r ω) atTop
      (fun ω => ∫ x, f (1 - x) * symmetryReflectionLimitWeight γ (1 - x) ∂M ω) := by
    apply TendstoInMeasure.congr _ _ hsub
    · intro r
      filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
      let := hω
      exact symmetry_integral_shift_cancel _ g (w r) ‖f‖
    · exact ae_of_all _ (fun ω => by
        let := hM.1 ω
        exact symmetry_integral_shift_cancel _ g v ‖f‖)
  have hLmeas : Measurable (fun ω => Real.exp (-γ * Xc ω 1 0)) :=
    Real.measurable_exp.comp (((hXc.1 0).comp
      (measurable_id.prodMk measurable_const)).const_mul (-γ))
  have hscaled := tendstoInMeasure_mul_same_space _ _ _ hLmeas hsigned
  simpa only [regularizedGMC_symmetryRepinned_integral P X hX Xc hXc,
    symmetryRepinnedChaos_integral] using hscaled
end DOZZ.Proofs
