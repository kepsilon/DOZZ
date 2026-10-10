/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Lower measurable envelopes for potentially nonmeasurable masses. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- A measurable minorant attaining a finite lower integral dominates every measurable minorant
almost everywhere. No measurability or sigma-finiteness assumption on the original mass is used. -/
theorem lower_integral_envelope_dominates
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g v : Ω → ℝ≥0∞)
    (hg : Measurable g) (hv : Measurable v) (hgf : g ≤ f) (hvf : v ≤ f)
    (heq : (∫⁻ ω, f ω ∂P) = ∫⁻ ω, g ω ∂P)
    (hfinite : (∫⁻ ω, f ω ∂P) ≠ ∞) : v ≤ᵐ[P] g := by
  have hmax : (∫⁻ ω, max (g ω) (v ω) ∂P) ≤ ∫⁻ ω, g ω ∂P := by
    rw [← heq]
    exact lintegral_mono fun ω => max_le (hgf ω) (hvf ω)
  have hae := ae_eq_of_ae_le_of_lintegral_le
    (ae_of_all P fun ω => le_max_left (g ω) (v ω))
    (heq ▸ hfinite) (hg.max hv).aemeasurable hmax
  filter_upwards [hae] with ω hω
  exact (le_max_right (g ω) (v ω)).trans hω.ge

/-- Monotone transforms with a measurable inverse preserve a finite attaining lower envelope. -/
theorem lintegral_transform_eq_of_lower_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ≥0∞)
    (hg : Measurable g) (hgf : g ≤ f)
    (heq : (∫⁻ ω, f ω ∂P) = ∫⁻ ω, g ω ∂P)
    (hfinite : (∫⁻ ω, f ω ∂P) ≠ ∞)
    (φ ψ : ℝ≥0∞ → ℝ≥0∞) (hmono : Monotone φ) (hψ : Measurable ψ)
    (hinverse : ∀ ω z, z ≤ φ (f ω) → ψ z ≤ f ω ∧ z ≤ φ (ψ z)) :
    (∫⁻ ω, φ (f ω) ∂P) = ∫⁻ ω, φ (g ω) ∂P := by
  apply le_antisymm
  · obtain ⟨v, hv, hvle, hveq⟩ := exists_measurable_le_lintegral_eq P (fun ω => φ (f ω))
    have hψle : (fun ω => ψ (v ω)) ≤ f := fun ω => (hinverse ω (v ω) (hvle ω)).1
    have hdom := lower_integral_envelope_dominates P f g (fun ω => ψ (v ω))
      hg (hψ.comp hv) hgf hψle heq hfinite
    rw [hveq]
    apply lintegral_mono_ae
    filter_upwards [hdom] with ω hω
    exact (hinverse ω (v ω) (hvle ω)).2.trans (hmono hω)
  · exact lintegral_mono fun ω => hmono (hgf ω)

/-- Positive powers preserve an attaining finite lower measurable envelope. -/
theorem lintegral_rpow_eq_of_lower_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ≥0∞)
    (hg : Measurable g) (hgf : g ≤ f)
    (heq : (∫⁻ ω, f ω ∂P) = ∫⁻ ω, g ω ∂P)
    (hfinite : (∫⁻ ω, f ω ∂P) ≠ ∞) (t : ℝ) (ht : 0 < t) :
    (∫⁻ ω, f ω ^ t ∂P) = ∫⁻ ω, g ω ^ t ∂P := by
  apply lintegral_transform_eq_of_lower_envelope P f g hg hgf heq hfinite
    (fun r => r ^ t) (fun r => r ^ t⁻¹)
    (fun _ _ h => ENNReal.rpow_le_rpow h ht.le)
    (ENNReal.continuous_rpow_const.measurable)
  intro ω z hz
  have hleft : (f ω ^ t) ^ t⁻¹ = f ω := by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
  have hright : (z ^ t⁻¹) ^ t = z := by
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ ht.ne', ENNReal.rpow_one]
  constructor
  · exact hleft ▸ ENNReal.rpow_le_rpow hz (inv_nonneg.mpr ht.le)
  · exact hright.ge

end DOZZ.Proofs
