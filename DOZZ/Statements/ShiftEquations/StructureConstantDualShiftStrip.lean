/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Shifts.Assembly.DualShiftStrip

/-! The statement `DOZZ.structureConstant_dual_shift_strip`,
proved by `DOZZ.Proofs.structureConstant_dual_shift_strip`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The corrected dual fusion relation, reflection gluing and the identification `R = R^DOZZ`
([KRV, Theorem 3.5]) identify the centered dual `2/γ` shift on the same meromorphic continuation
([KRV, §11]). -/
theorem structureConstant_dual_shift_strip
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, R z = reflectionDOZZ γ μ z) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              ∀ᶠ z in codiscrete ℂ,
                C (z + 2 / γ) =
                  -(1 / (Real.pi * dualMu γ μ)) *
                    shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
                      C (z - 2 / γ) := by exact DOZZ.Proofs.structureConstant_dual_shift_strip P X M γ μ η hγ hγ2 hγirr hμ hη hX hM α₂ α₃ hα₂ hα₃

end DOZZ
