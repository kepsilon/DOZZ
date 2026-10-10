/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliScalar

/-! Multivariate Gaussian comparison with an explicit common-scalar factor. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The finite-measure zero case does not require a nonempty spatial carrier. -/
theorem fieldChaosMass_finite_ae
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, fieldChaosMass P Φ ν h γ ω ≠ ⊤ := by
  by_cases hν : ν = 0
  · filter_upwards [] with ω
    rw [hν, fieldChaosMass, lintegral_zero_measure]
    exact ENNReal.zero_ne_top
  · have : Nonempty S := by
      obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν)
      exact ⟨x⟩
    exact centeredGaussianField_fieldChaosMass_ne_top_ae P Φ hΦ ⟨ν, inferInstance⟩ h hh hhb γ

/-- One common Gaussian constant compares products of negative moments. Its factor involves
the square of the sum of all orders, rather than separate squares for independent blocks. -/
theorem retained_fields_multi_negative_compare
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν]
    (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ C : ℝ) (hC : 0 ≤ C) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤
        (∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY) + C)
    (hdiag : ∀ᵐ x ∂ν, ∫ ω, Φ ω x ^ 2 ∂PX ≤ (∫ ω, Ψ ω x ^ 2 ∂PY) + C) :
    (∫⁻ ω, ∏ k, (fieldChaosMass PX Φ ν (h k) γ ω) ^ (-q k) ∂PX) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * ((∑ k, q k) ^ 2 + ∑ k, q k))) *
        ∫⁻ ω, ∏ k, (fieldChaosMass PY Ψ ν (h k) γ ω) ^ (-q k) ∂PY := by
  classical
  let c := Real.sqrt C
  let Ψc : ΩY × ℝ → S → ℝ := fun w x => Ψ w.1 x + c * w.2
  have hc : c ^ 2 = C := Real.sq_sqrt hC
  have hΨc := independent_common_scalar_add_isCenteredGaussianField PY Ψ hΨ c
  have hcovc (x y : S) :
      (∫ w, Ψc w x * Ψc w y ∂PY.prod (gaussianReal 0 1)) =
        (∫ ω, Ψ ω x * Ψ ω y ∂PY) + C := by
    simpa only [gaussianCovariance, Ψc, hc] using
      gaussianCovariance_field_independent_common_scalar_add PY Ψ hΨ c x y
  have hcov' : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤
        ∫ w, Ψc w xy.1 * Ψc w xy.2 ∂PY.prod (gaussianReal 0 1) := by
    filter_upwards [hcov] with xy hxy
    rw [hcovc]
    exact hxy
  have hdiag' : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ w, Ψc w x ^ 2 ∂PY.prod (gaussianReal 0 1) := by
    filter_upwards [hdiag] with x hx
    simp only [pow_two] at hx ⊢
    rw [hcovc]
    exact hx
  have hk := kahane_field_multi_negative_power PX (PY.prod (gaussianReal 0 1)) Φ Ψc
    hΦ hΨc ν h hh hhb γ q hq hcov' hdiag'
  change (∫⁻ ω, ∏ k, (fieldChaosMass PX Φ ν (h k) γ ω) ^ (-q k) ∂PX) ≤
    ∫⁻ w, ∏ k, (fieldChaosMass (PY.prod (gaussianReal 0 1)) Ψc ν (h k) γ w) ^ (-q k)
      ∂PY.prod (gaussianReal 0 1) at hk
  have : IsProbabilityMeasure PY := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let F : κ → ΩY → ℝ≥0∞ := fun k ω => fieldChaosMass PY Ψ ν (h k) γ ω
  have hF : ∀ k, AEMeasurable (F k) PY := fun k =>
    (centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ ν (h k) (hh k) γ).aemeasurable
  have hFfin : ∀ k, ∀ᵐ ω ∂PY, F k ω ≠ ⊤ := fun k =>
    fieldChaosMass_finite_ae PY Ψ hΨ ν (h k) (hh k) (hhb k) γ
  have hfactor := retained_masses_common_scalar_factor PY F hF hFfin γ
    (fun _ => c) (fun k => -q k)
  have hident (w : ΩY × ℝ) :
      (∏ k, (fieldChaosMass (PY.prod (gaussianReal 0 1)) Ψc ν (h k) γ w) ^ (-q k)) =
        ∏ k, (ENNReal.ofReal (Real.exp (γ * c * w.2 - γ ^ 2 * c ^ 2 / 2)) * F k w.1) ^ (-q k) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [fieldChaosMass_independent_common_scalar_factor PY Ψ hΨ ν (h k) γ c w.1 w.2]
    rw [show γ ^ 2 / 2 * c ^ 2 = γ ^ 2 * c ^ 2 / 2 by ring]
  rw [lintegral_congr (hident), hfactor] at hk
  have hsum : (∑ k, -q k * c) = -(∑ k, q k) * c := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  have hsum2 : (∑ k, -q k * c ^ 2) = -(∑ k, q k) * C := by
    rw [hc, ← Finset.sum_mul, Finset.sum_neg_distrib]
  rw [hsum, hsum2] at hk
  have he : γ ^ 2 / 2 * ((-(∑ k, q k) * c) ^ 2 - (-(∑ k, q k) * C)) =
      γ ^ 2 * C / 2 * ((∑ k, q k) ^ 2 + ∑ k, q k) := by
    rw [mul_pow, neg_sq, hc]
    ring
  rw [he] at hk
  exact hk

end DOZZ.Proofs
