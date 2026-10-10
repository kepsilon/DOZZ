/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.ReflectionShifts

/-! The statement `DOZZ.reflectionDOZZ_shift_b`, proved by `DOZZ.Proofs.reflectionDOZZ_shift_b`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- First reflection shift [KRV, (shift1DOZZ)] (correct as printed). -/
theorem reflectionDOZZ_shift_b {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ (α - γ / 2) =
        -(μ * Real.pi) * reflectionDOZZ γ μ α /
          (lFun (-(γ ^ 2 / 4)) * lFun (γ * α / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * α / 2)) := by exact DOZZ.Proofs.reflectionDOZZ_shift_b hγ hγ2 hμ

end DOZZ
