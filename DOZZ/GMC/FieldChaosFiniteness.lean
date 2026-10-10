/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower

/-! Finiteness of continuum chaos masses with bounded measurable weights. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A field-chaos mass is finite almost surely under a bounded spatial weight. -/
theorem centeredGaussianField_fieldChaosMass_ne_top_ae
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ≠ ∞ := by
  filter_upwards [centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ] with ω hω
  rw [fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω hω]
  exact ENNReal.ofReal_ne_top


end DOZZ.Proofs
