/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.ReflectionLimit

/-! The statement `DOZZ.reflectionDOZZ_tendsto_Q`,
proved by `DOZZ.Proofs.reflectionDOZZ_tendsto_Q`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `R^{DOZZ}(Q) = -1` ([KRV, §10.6]), as a punctured limit; the literal Lean value at `Q` is
junk. -/
theorem reflectionDOZZ_tendsto_Q {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (reflectionDOZZ γ μ) (𝓝[≠] (Q γ : ℂ)) (𝓝 (-1)) := by exact DOZZ.Proofs.reflectionDOZZ_tendsto_Q hγ hγ2 hμ

end DOZZ
