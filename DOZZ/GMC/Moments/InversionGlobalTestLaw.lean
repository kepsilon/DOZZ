/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionExhaustion
public import DOZZ.GMC.Moments.InversionAtomless
public import Mathlib.MeasureTheory.Measure.GiryMonad
@[expose] public section
open Filter MeasureTheory Set Metric
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- Bounded continuous integrals are measurable for measurable finite random measures. -/
theorem finiteMeasure_bcf_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω] (M : Ω → Measure ℂ) (hM : Measurable M)
    (hfin : ∀ ω, IsFiniteMeasure (M ω)) (f : BoundedContinuousFunction ℂ ℝ) :
    Measurable (fun ω => ∫ x, f x ∂M ω) := by
  let : ∀ ω, IsFiniteMeasure (M ω) := hfin
  have hp := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp f.nnrealPart)).comp hM
  have hn := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp (-f).nnrealPart)).comp hM
  have h : Measurable (fun ω =>
      (∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂M ω).toReal -
      (∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂M ω).toReal) := by
    exact hp.ennreal_toReal.sub hn.ennreal_toReal
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral, Function.comp_def, Pi.sub_apply] using h

/-- Inversion preserves every bounded continuous test vector of a measurable GMC version. -/
theorem gmc_inversion_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hmeas : Measurable M)
    (f : Fin k → BoundedContinuousFunction ℂ ℝ) :
    P.map (fun ω j => ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹)) =
      P.map (fun ω j => ∫ x, f j x ∂M ω) := by
  let : IsProbabilityMeasure P := hX.1
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hNmeas : Measurable N := (Measure.measurable_map _ measurable_inv).comp hmeas
  have hNfin : ∀ ω, IsFiniteMeasure (N ω) := by
    intro ω
    let := hM.1 ω
    infer_instance
  let q := fun n j => f j * gmcInversionCutoff n
  have hqm n j := finiteMeasure_bcf_integral_measurable M hmeas hM.1 (q n j)
  have hqn n j := finiteMeasure_bcf_integral_measurable N hNmeas hNfin (q n j)
  have hzero := gmc_atomless_at_zero_of_isGMCOf P X hX γ hγ hγ2 M hM
  have hNzero : ∀ᵐ ω ∂P, N ω {0} = 0 := by
    filter_upwards [hzero] with ω hω
    change (M ω).map (fun z : ℂ => z⁻¹) {0} = 0
    rw [Measure.map_apply measurable_inv (measurableSet_singleton 0)]
    simpa only [preimage, mem_singleton_iff, inv_eq_zero, ofPred_eq_eq_singleton] using hω
  apply gmc_limit_test_vector_law
    (fun n ω j => ∫ x, q n j x ∂N ω) (fun n ω j => ∫ x, q n j x ∂M ω)
    (fun ω j => ∫ x, f j x ∂N ω) (fun ω j => ∫ x, f j x ∂M ω)
  · intro n; exact (measurable_pi_iff.mpr (hqn n)).aemeasurable
  · intro n; exact (measurable_pi_iff.mpr (hqm n)).aemeasurable
  · exact (measurable_pi_iff.mpr (fun j =>
      finiteMeasure_bcf_integral_measurable N hNmeas hNfin (f j))).aemeasurable
  · exact (measurable_pi_iff.mpr (fun j =>
      finiteMeasure_bcf_integral_measurable M hmeas hM.1 (f j))).aemeasurable
  · intro n
    let U := {x : ℂ | 1 / (2 * ((n : ℝ) + 2)) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 3}
    apply gmc_inversion_annular_test_vector_law P X hX γ hγ hγ2 M hM U
      (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const))
      (m := 1 / (4 * ((n : ℝ) + 2))) (R := (n : ℝ) + 3)
      (by positivity) (by positivity)
    · intro x hx
      constructor
      · have he : 2 * (1 / (4 * ((n : ℝ) + 2))) = 1 / (2 * ((n : ℝ) + 2)) := by
          field_simp
          norm_num
        rw [he]; exact hx.1.le
      · exact hx.2.le
    · exact fun j => (gmcInversionCutoff_test_annular n (f j)).1
    · exact fun j => (gmcInversionCutoff_test_annular n (f j)).2
  · intro j
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hqn n j).aestronglyMeasurable)
    filter_upwards [hNzero] with ω hω
    let := hNfin ω
    exact inversion_cutoff_integral_tendsto (N ω) hω (f j)
  · intro j
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hqm n j).aestronglyMeasurable)
    filter_upwards [hzero] with ω hω
    let := hM.1 ω
    exact inversion_cutoff_integral_tendsto (M ω) hω (f j)
end DOZZ.Proofs
