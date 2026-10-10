/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Quotient.RemovablePeriodic

/-! The statement `DOZZ.structureConstant_DOZZ_quotient_removable_periodic`,
proved by `DOZZ.Proofs.structureConstant_DOZZ_quotient_removable_periodic`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- On the regime of the final quotient argument [KRV, §11] (`γ² ∉ ℚ` and fixed real charges `α₂`,
`α₃` on the near-`Q` slice), the quotient extends holomorphically through all divisor points and has
periods `γ` and `4/γ`. -/
theorem structureConstant_DOZZ_quotient_removable_periodic
    (γ μ η : ℝ) (U : ℂ → ℂ) (α₂ α₃ : ℝ) (h : ℝ) (hh : 0 < h)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ) (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hU : IsUpsilon γ U)
    (C : ℂ → ℂ) (hC : MeromorphicOn C (horizontalStrip h))
    (hfirst : ∀ᶠ z in codiscrete ℂ,
      C (z + γ / 2) =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2))
    (hdual : ∀ᶠ z in codiscrete ℂ,
      C (z + 2 / γ) =
        -(1 / (Real.pi * dualMu γ μ)) *
          shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) * C (z - 2 / γ)) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (horizontalStrip h) ∧
      (∀ᶠ z in codiscrete ℂ, Ψ z * dozzFormula γ μ U z (α₂ : ℂ) (α₃ : ℂ) = C z) ∧
      ∀ z ∈ horizontalStrip h, Ψ (z + γ) = Ψ z ∧ Ψ (z + 4 / γ) = Ψ z := by exact DOZZ.Proofs.structureConstant_DOZZ_quotient_removable_periodic γ μ η U α₂ α₃ h hh hγ hγ2 hγirr hμ hη hα₂ hα₃ hU C hC hfirst hdual

end DOZZ
