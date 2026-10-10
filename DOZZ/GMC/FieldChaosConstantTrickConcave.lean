/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldGaussianCommonScalar
public import DOZZ.GMC.FieldChaosConcavePower

/-! The common Gaussian scalar constant trick for concave continuum moments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Continuum constant trick for concave powers `0 < p < 1`. -/
theorem kahane_field_constant_trick_concave
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ C p : ℝ) (hC : 0 ≤ C)
    (hp : 0 < p ∧ p < 1)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      |(∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX) -
        (∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)| ≤ C)
    (hdiag : ∀ᵐ x ∂ν,
      |(∫ ω, Φ ω x ^ 2 ∂PX) - (∫ ω, Ψ ω x ^ 2 ∂PY)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p - p ^ 2)))) *
        (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) ≤
          ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ∧
      (∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX) ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p - p ^ 2))) *
          (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) := by
  classical
  let c := Real.sqrt C
  let A := γ ^ 2 * C / 2 * (p - p ^ 2)
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp A)
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A))
  let Φc : ΩX × ℝ → S → ℝ := fun ω x => Φ ω.1 x + c * ω.2
  let Ψc : ΩY × ℝ → S → ℝ := fun ω x => Ψ ω.1 x + c * ω.2
  have hc : c ^ 2 = C := Real.sq_sqrt hC
  have hΦc := independent_common_scalar_add_isCenteredGaussianField PX Φ hΦ c
  have hΨc := independent_common_scalar_add_isCenteredGaussianField PY Ψ hΨ c
  have hcovΦc (x y : S) :
      (∫ ω : ΩX × ℝ, Φc ω x * Φc ω y ∂PX.prod (gaussianReal 0 1)) =
        (∫ ω, Φ ω x * Φ ω y ∂PX) + C := by
    simpa [DOZZ.gaussianCovariance, Φc, hc] using
      gaussianCovariance_field_independent_common_scalar_add PX Φ hΦ c x y
  have hcovΨc (x y : S) :
      (∫ ω : ΩY × ℝ, Ψc ω x * Ψc ω y ∂PY.prod (gaussianReal 0 1)) =
        (∫ ω, Ψ ω x * Ψ ω y ∂PY) + C := by
    simpa [DOZZ.gaussianCovariance, Ψc, hc] using
      gaussianCovariance_field_independent_common_scalar_add PY Ψ hΨ c x y
  have hcovXYc : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX) ≤
        ∫ ω, Ψc ω xy.1 * Ψc ω xy.2 ∂PY.prod (gaussianReal 0 1) := by
    filter_upwards [hcov] with xy hxy
    rw [hcovΨc]
    linarith [(abs_le.mp hxy).2]
  have hcovYXc : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY) ≤
        ∫ ω, Φc ω xy.1 * Φc ω xy.2 ∂PX.prod (gaussianReal 0 1) := by
    filter_upwards [hcov] with xy hxy
    rw [hcovΦc]
    linarith [(abs_le.mp hxy).1]
  have hdiagXYc : ∀ᵐ x ∂ν,
      (∫ ω, Φ ω x ^ 2 ∂PX) ≤
        ∫ ω, Ψc ω x ^ 2 ∂PY.prod (gaussianReal 0 1) := by
    filter_upwards [hdiag] with x hx
    simp only [pow_two] at hx ⊢
    rw [hcovΨc]
    linarith [(abs_le.mp hx).2]
  have hdiagYXc : ∀ᵐ x ∂ν,
      (∫ ω, Ψ ω x ^ 2 ∂PY) ≤
        ∫ ω, Φc ω x ^ 2 ∂PX.prod (gaussianReal 0 1) := by
    filter_upwards [hdiag] with x hx
    simp only [pow_two] at hx ⊢
    rw [hcovΦc]
    linarith [(abs_le.mp hx).1]
  have hXfactor : (∫⁻ ω, fieldChaosMass (PX.prod (gaussianReal 0 1)) Φc ν h γ ω ^ p
      ∂PX.prod (gaussianReal 0 1)) = L * ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX := by
    have h := fieldChaosMoment_independent_common_scalar_factor PX Φ hΦ ν h hh hhb γ c p
    have hA : γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p) = -A := by dsimp [A]; rw [hc]; ring
    simpa only [hA] using h
  have hYfactor : (∫⁻ ω, fieldChaosMass (PY.prod (gaussianReal 0 1)) Ψc ν h γ ω ^ p
      ∂PY.prod (gaussianReal 0 1)) = L * ∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
    have h := fieldChaosMoment_independent_common_scalar_factor PY Ψ hΨ ν h hh hhb γ c p
    have hA : γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p) = -A := by dsimp [A]; rw [hc]; ring
    simpa only [hA] using h
  have hXY := kahane_field_power_concave PX (PY.prod (gaussianReal 0 1)) Φ Ψc hΦ hΨc
    ν h hh hhb γ p hp hcovXYc hdiagXYc
  have hYX := kahane_field_power_concave PY (PX.prod (gaussianReal 0 1)) Ψ Φc hΨ hΦc
    ν h hh hhb γ p hp hcovYXc hdiagYXc
  rw [hYfactor] at hXY
  rw [hXfactor] at hYX
  have hKL : K * L = 1 := by
    dsimp [K, L]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  constructor
  · exact hXY
  · calc
      _ = (K * L) * ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX := by rw [hKL]; simp
      _ = K * (L * ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX) := mul_assoc _ _ _
      _ ≤ K * ∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY :=
        mul_le_mul_of_nonneg_left hYX (by positivity)


end DOZZ.Proofs
