/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf

/-! The definition `DOZZ.rho`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `ρ(α₁,α₂,α₃) = ∫ |x|_+^{γᾱ} |x|^{-γα₁} |x-1|^{-γα₂} M_γ(d²x)` ([KRV, §2.3]). -/
noncomputable def rho (γ : ℝ) (M : Measure ℂ) (α₁ α₂ α₃ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (normPlus x ^ (γ * (α₁ + α₂ + α₃))
    / (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂))) ∂M

end DOZZ
