/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.WeightedGmcBallMoment

/-! The definition `DOZZ.coulombMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Coulomb weighted mass with `N` distinct finite roots and one optional root at infinity.
At a finite root, the displayed `ENNReal.ofReal` convention gives value `0` for a positive
charge exponent and `⊤` for a negative one, opposite the extended singular weight; these values
are harmless when the random measure has no atoms at the roots. The definition `rho` is the
`N = 2` case at `0,1` with the third charge at infinity. See [KRV, (coulomb)]. -/
noncomputable def coulombMass {N : ℕ} (γ : ℝ) (M : Measure ℂ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z k‖)) (γ * α k)) *
    ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) ∂M

end DOZZ
