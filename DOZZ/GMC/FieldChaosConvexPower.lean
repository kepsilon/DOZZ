/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosAffineMax
public import DOZZ.GMC.KahaneConvexOrderClosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Continuum Kahane comparison for all convex real powers. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem kahane_field_power_ge_one_nonzero
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 1 ≤ p)
    (hcov : ∀ᵐ q ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω q.1) (fun ω => Φ ω q.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω q.1) (fun ω => Ψ ω q.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω ^ p ∂PX ≤
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω ^ p ∂PY := by
  classical
  let : IsProbabilityMeasure PX := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let : IsProbabilityMeasure PY := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  by_cases hw0 : ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) = 0
  · simp_rw [centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PX Φ ν h hh hhb γ hw0,
      centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral PY Ψ ν h hh hhb γ hw0]
    simp
  have hwpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) :=
    lt_of_le_of_ne (integral_nonneg fun _ => NNReal.coe_nonneg _) (Ne.symm hw0)
  let c : ℝ := ν.mass
  let mX : ΩX → ℝ := fun ω => c * ∫ x, fieldWickDensity PX Φ h γ ω x
    ∂(ν.normalize : Measure S)
  let mY : ΩY → ℝ := fun ω => c * ∫ x, fieldWickDensity PY Ψ h γ ω x
    ∂(ν.normalize : Measure S)
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have hmX := ((fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).1.integral_prod_left).const_mul c
  have hmY := ((fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).1.integral_prod_left).const_mul c
  have hmX0 (ω : ΩX) : 0 ≤ mX ω :=
    mul_nonneg hc (integral_nonneg fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
  have hmY0 (ω : ΩY) : 0 ≤ mY ω :=
    mul_nonneg hc (integral_nonneg fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
  have hrepX : ∀ᵐ ω ∂PX, DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω = ENNReal.ofReal (mX ω) := by
    filter_upwards [centeredGaussianField_ae_integrable_weighted_wick PX Φ hΦ ν h hh hhb γ] with ω hω
    exact fieldChaosMass_eq_ofReal_normalized_integral PX Φ ν h γ ω hω
  have hrepY : ∀ᵐ ω ∂PY, DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω = ENNReal.ofReal (mY ω) := by
    filter_upwards [centeredGaussianField_ae_integrable_weighted_wick PY Ψ hΨ ν h hh hhb γ] with ω hω
    exact fieldChaosMass_eq_ofReal_normalized_integral PY Ψ ν h γ ω hω
  have hposX : ∀ᵐ ω ∂PX, 0 < mX ω := by
    filter_upwards [hrepX, centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
      PX Φ hΦ ν hν h hh hhb γ hwpos] with ω hω hpω
    rw [hω] at hpω
    exact ENNReal.ofReal_pos.mp hpω
  have hposY : ∀ᵐ ω ∂PY, 0 < mY ω := by
    filter_upwards [hrepY, centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
      PY Ψ hΨ ν hν h hh hhb γ hwpos] with ω hω hpω
    rw [hω] at hpω
    exact ENNReal.ofReal_pos.mp hpω
  have hmean : (∫ ω, mX ω ∂PX) = ∫ ω, mY ω ∂PY := by
    dsimp [mX, mY]
    rw [integral_const_mul, integral_const_mul,
      ← integral_prod _ (fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).1,
      ← integral_prod _ (fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).1,
      (fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).2,
      (fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).2]
  have horder (n : ℕ) (a b : Fin (n + 1) → ℝ) :
      (∫ ω, affineMax a b (mX ω) ∂PX) ≤ ∫ ω, affineMax a b (mY ω) ∂PY := by
    have hscale (x : ℝ) : affineMax (fun i => a i * c) b x = affineMax a b (c * x) := by
      unfold affineMax
      congr 1
      funext i
      ring
    have hcmp := kahane_field_normalized_affine_max PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ
      (fun i => a i * c) b hcov hdiag
    simpa only [hscale] using hcmp
  have hpowX : ∀ᵐ ω ∂PX, DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω ^ p =
      ENNReal.ofReal (mX ω ^ p) := by
    filter_upwards [hrepX] with ω hω
    rw [hω, ENNReal.ofReal_rpow_of_nonneg (hmX0 ω) (by linarith)]
  have hpowY : ∀ᵐ ω ∂PY, DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω ^ p =
      ENNReal.ofReal (mY ω ^ p) := by
    filter_upwards [hrepY] with ω hω
    rw [hω, ENNReal.ofReal_rpow_of_nonneg (hmY0 ω) (by linarith)]
  rw [lintegral_congr_ae hpowX, lintegral_congr_ae hpowY]
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (mY ω ^ p) ∂PY) = ∞
  · rw [htop]
    exact le_top
  have hF : Measurable (fun x : ℝ => x ^ p) := by fun_prop
  have hIY : Integrable (fun ω => mY ω ^ p) PY := by
    refine ⟨(hF.comp_aemeasurable hmY.aemeasurable).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => Real.rpow_nonneg (hmY0 ω) p)).2
      (lt_top_iff_ne_top.mpr htop)
  have hcmp := convex_comparison_of_affine_max_order PX PY mX mY hmX hmY hposX hposY
    hmean horder (fun x => x ^ p) hF (convexOn_rpow hp) hIY
  rw [← ofReal_integral_eq_lintegral_ofReal hcmp.1
      (ae_of_all _ fun ω => Real.rpow_nonneg (hmX0 ω) p),
    ← ofReal_integral_eq_lintegral_ofReal hIY
      (ae_of_all _ fun ω => Real.rpow_nonneg (hmY0 ω) p)]
  exact ENNReal.ofReal_le_ofReal hcmp.2

/-- Continuum Kahane comparison for convex powers, with the diagonal covariance condition
separate from the almost-everywhere off-diagonal condition. -/
theorem kahane_field_power_convex
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p ≤ 0 ∨ 1 ≤ p)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX ≤ ∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≤
      ∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  rcases hp with hp | hp
  · exact kahane_field_power_nonpos PX PY Φ Ψ hΦ hΨ ν h hh hhb γ p hp hcov hdiag
  classical
  by_cases hν0 : ν = 0
  · simp [DOZZ.fieldChaosMass, hν0, ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hp)]
  have : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)
    exact ⟨x⟩
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    exact hν0 (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero)
  apply kahane_field_power_ge_one_nonzero PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ p hp
  · simpa [νf, DOZZ.gaussianCovariance] using hcov
  · simpa [νf, DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hdiag



end DOZZ.Proofs
