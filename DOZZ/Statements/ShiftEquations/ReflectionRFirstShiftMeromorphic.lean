/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Assembly.FirstShiftMeromorphic

/-! The statement `DOZZ.reflectionR_first_shift_meromorphic`,
proved by `DOZZ.Proofs.reflectionR_first_shift_meromorphic`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The first shift, corrected as in erratum K11 (see docs/ERRATA-AND-DEVIATIONS.md), gives a
meromorphic continuation of the probabilistic `R` from `(γ/2, Q)` and its exact shift equation, off
its discrete pole set ([KRV, §10.2]). The third denominator factor is the corrected
`l(2+γ²/2−γz/2)`, as in `reflectionDOZZ_shift_b`. -/
theorem reflectionR_first_shift_meromorphic
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
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) := by exact DOZZ.Proofs.reflectionR_first_shift_meromorphic P X M γ μ hγ hγ2 hμ hX hM

end DOZZ
