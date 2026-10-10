/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Inversion.Reduction
public import DOZZ.ShiftEquations.Assembly.ReflectedShiftAndGluing

/-! # The unconditional reflection inversion -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The charge-zero residue and dual crossing/gluing give inversion on the continued domain
([KRV, §10.4]), as a meromorphic identity rather than pointwise values at poles. -/
theorem reflectionR_inversion_meromorphic
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ, R z * R (2 * Q γ - z) = 1 := by
  exact reflectionR_inversion_meromorphic_of_reflected_shift_and_gluing P X M γ μ hγ hγ2 hμ hX hM
    (fun η hη α₂ α₃ hα₂ hα₃ =>
      structureConstant_reflected_shift_and_gluing P X M γ μ η hγ hγ2 hμ hη
        hX hM α₂ α₃ hα₂ hα₃)

end DOZZ.Proofs
