/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.FirstShiftContinuation

/-! # The first structure shift on its physical strip

The unreflected formula and diagonal classification supply the seed; the holomorphic physical germ
and translated-rectangle gluing supply its continuation.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- Proof of `DOZZ.structureConstant_first_shift_strip`. -/
theorem structureConstant_first_shift_strip
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ) :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
      MeromorphicOn C {z | |z.im| < h} ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ →
        C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ,
        C (z + γ / 2) =
          -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
            C (z - γ / 2) := by
  simpa only [horizontalStrip] using firstStrip_continuation
    P X M γ μ η α₂ α₃ hγ hγ2 hμ hη hX hM hα₂ hα₃

end DOZZ.Proofs
