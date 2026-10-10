/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedTransfer
public import DOZZ.GMC.SharpMoments.ExteriorMoment
public import DOZZ.GMC.SharpMoments.SeibergMoment

/-! # Convergence of bounded cutoff integrals and far exterior cutoff moments

Cutoff integrals of a bounded Borel function supported in a disk converge in probability along
the integer cutoffs, by the uniform `L¹` convergence. Exact exterior scaling moves the base
annulus of the exterior dyadic bound out to any radius, so the cutoff moments of a power weight
outside a large disk decay like a negative power of the radius. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Cutoff integrals of a bounded Borel function with bounded support converge in probability
along the integer cutoffs. -/
theorem regularizedGMC_lintegral_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (f : ℂ → ℝ≥0) (hf : Measurable f) (b : ℝ≥0) (hfb : ∀ x, f x ≤ b) (R : ℝ)
    (hfR : ∀ x ∉ closedBall (0 : ℂ) R, f x = 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => (∫⁻ x, (f x : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω).toReal)
      atTop (fun ω => (∫⁻ x, (f x : ℝ≥0∞) ∂M ω).toReal) := by
  have hfr : Measurable fun x => (f x : ℝ) := measurable_coe_nnreal_real.comp hf
  have hfm : Measurable fun x => (f x : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hf
  have hid : ∀ μ : Measure ℂ, (∫⁻ x, (f x : ℝ≥0∞) ∂μ).toReal = ∫ x, (f x : ℝ) ∂μ := by
    intro μ
    have h := integral_toReal (μ := μ) hfm.aemeasurable
      (Eventually.of_forall fun x => ENNReal.coe_lt_top)
    rw [← h]
    simp only [ENNReal.coe_toReal]
  have hL1 := regularizedGMC_integral_l1_tendsto P X hX γ hγ hγ2 M hM Xc hXc (fun x => (f x : ℝ))
    hfr b (fun x => by rw [NNReal.abs_eq]; exact_mod_cast hfb x) R
    (fun x hx => by simp [hfR x hx])
  have hF : ∀ n : ℕ, AEStronglyMeasurable (fun ω => (∫⁻ x, (f x : ℝ≥0∞)
      ∂regularizedGMC P Xc γ n ω).toReal) P := fun n =>
    (ENNReal.measurable_toReal.comp ((Measure.measurable_lintegral hfm).comp
      (regularizedGMC_measurable P X hX Xc hXc γ n))).aestronglyMeasurable
  have hG : AEStronglyMeasurable (fun ω => (∫⁻ x, (f x : ℝ≥0∞) ∂M ω).toReal) P :=
    (ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _ hfm)).aestronglyMeasurable
  refine DOZZ.Assembly.tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P _ _ hF hG ?_
  refine (hL1.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, hid]

/-- The base annulus of the exterior dyadic bound can be moved out to any radius by exact
exterior scaling. -/
theorem exteriorAnnulus_moment_le_far
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) {R0 R : ℝ} (hR0 : 2 ≤ R0)
    (hR : R0 ≤ R) {t : ℝ} {K0 : ℝ≥0∞}
    (hK0 : ∀ r' : ℝ, 0 ≤ r' →
      ∫⁻ ω, regularizedGMC P Xc γ r' ω (exteriorAnnulus R0 0) ^ t ∂P ≤ K0)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, regularizedGMC P Xc γ r ω (exteriorAnnulus R 0) ^ t ∂P ≤
      ENNReal.ofReal ((R / R0) ^ (-(2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2))) * K0 := by
  have hR0pos : 0 < R0 := by linarith
  set c : ℝ := R / R0 with hcdef
  have hc : 1 ≤ c := (one_le_div hR0pos).mpr hR
  have hc0 : 0 < c := by linarith
  have hA2 : ∀ x ∈ exteriorAnnulus R0 0, 2 ≤ ‖x‖ := fun x hx => by
    have := hx.1
    simp only [pow_zero, one_mul] at this
    linarith
  have hscale := cutoff_exterior_scale_moment_eq P X hX Xc hXc γ hr hc (exteriorAnnulus R0 0)
    (measurableSet_exteriorAnnulus R0 0) hA2 (fun _ => 1) measurable_const ⟨1, fun _ => le_rfl⟩ t
  have hone : ∀ (μ : Measure ℂ) (S : Set ℂ),
      (∫⁻ y in S, ((fun _ : ℂ => (1 : ℝ≥0)) y : ℝ≥0∞) ∂μ) = μ S := fun μ S => by simp
  simp only [hone] at hscale
  have hset : {y : ℂ | (c : ℂ)⁻¹ * y ∈ exteriorAnnulus R0 0} = exteriorAnnulus R 0 := by
    ext y
    have hnorm : ‖(c : ℂ)⁻¹ * y‖ = ‖y‖ / c := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, inv_mul_eq_div]
    change (2 ^ 0 * R0 ≤ ‖(c : ℂ)⁻¹ * y‖ ∧ ‖(c : ℂ)⁻¹ * y‖ < 2 ^ (0 + 1) * R0) ↔
      (2 ^ 0 * R ≤ ‖y‖ ∧ ‖y‖ < 2 ^ (0 + 1) * R)
    rw [hnorm, pow_zero, one_mul, one_mul, zero_add, pow_one, le_div_iff₀ hc0, div_lt_iff₀ hc0]
    have h1 : R0 * c = R := by rw [hcdef]; field_simp
    have h2 : 2 * R0 * c = 2 * R := by rw [mul_assoc, h1]
    rw [h1, h2]
  rw [hset] at hscale
  rw [hscale]
  have hcoef : c ^ (-2 * t) * Real.exp (γ ^ 2 * Real.log c / 2 * (t ^ 2 - t)) =
      c ^ (-(2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2)) := by
    rw [show Real.exp (γ ^ 2 * Real.log c / 2 * (t ^ 2 - t)) = c ^ (γ ^ 2 * (t ^ 2 - t) / 2) by
      rw [Real.rpow_def_of_pos hc0]; congr 1; ring, ← Real.rpow_add hc0]
    congr 1
    ring
  rw [hcoef]
  gcongr
  exact hK0 _ (by have := Real.log_nonneg hc; linarith)

end DOZZ.Proofs
