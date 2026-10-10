/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.ReflectionShifts

/-! The statement `DOZZ.reflectionDOZZ_shift_binv`,
proved by `DOZZ.Proofs.reflectionDOZZ_shift_binv`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Dual reflection shift [KRV, (shift3DOZZ)], for `4/γ² ∉ ℕ`. -/
theorem reflectionDOZZ_shift_binv {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ α =
        -(((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)) *
          reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * α / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * α / γ)) := by exact DOZZ.Proofs.reflectionDOZZ_shift_binv hγ hγ2 hγk hμ

end DOZZ
