/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.FirstStrip.Strip
public import DOZZ.FourPoint.BPZ.GammaHalfFullUnreflectedFormula

/-!
# The first structure shift on a strip from the unreflected formula

`structureConstant_first_shift_strip_of_unreflected` with the proof of
`DOZZ.gammaHalf_full_unreflected_formula`: the conclusion of
`DOZZ.structureConstant_first_shift_strip`, with no remaining input. This is a helper with the exact
statement of `DOZZ.structureConstant_first_shift_strip`, not its proof.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The first structure shift on a strip with no remaining input** (the exact statement of
`DOZZ.structureConstant_first_shift_strip`). -/
theorem structureConstant_first_shift_strip_unconditional
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
            C (z - γ / 2) :=
  structureConstant_first_shift_strip_of_unreflected P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃
    (fun hH α₁ a₂ a₃ h1 h2 h3 h4 hs =>
      gammaHalf_full_unreflected_formula hH P X M γ μ α₁ a₂ a₃ hγ hγ2 hμ h1 h2 h3 h4 hs hX hM)

end DOZZ.Proofs

end
