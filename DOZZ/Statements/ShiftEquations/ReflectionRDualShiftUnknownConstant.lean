/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Assembly.DualShiftUnknownConstant

/-! The statement `DOZZ.reflectionR_dual_shift_unknown_constant`,
proved by `DOZZ.Proofs.reflectionR_dual_shift_unknown_constant`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The nonempty limiting region `0 < η'' < -2η'` (with `α' = 2/γ - η' = Q - ε`), as corrected in
erratum K6 (see docs/ERRATA-AND-DEVIATIONS.md), yields the dual shift [KRV, §10.5] with its
initially unknown constant `cγ = γ² μπ R(γ)/4`. The standing premise `γ² ∉ ℚ` of [KRV, §10] keeps
`R(γ)` finite, so `cγ ≠ 0` is meaningful. -/
theorem reflectionR_dual_shift_unknown_constant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
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
              ∃ cγ : ℂ, cγ ≠ 0 ∧
                cγ = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧
                ∀ᶠ z in codiscrete ℂ,
                  R z = -cγ * R (z + 2 / γ) /
                    (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
                      lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)) := by exact DOZZ.Proofs.reflectionR_dual_shift_unknown_constant P X M γ μ hγ hγ2 hγirr hμ hX hM

end DOZZ
