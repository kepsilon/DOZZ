/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.FormulaBridge

/-! The statement `DOZZ.dozzFormula_bridge`, proved by `DOZZ.Proofs.dozzFormula_bridge`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Three-to-two bridge for `C^{DOZZ}` ([KRV, (defRDOZZlim)] and [KRV, §12.6]; erratum K12, see
docs/ERRATA-AND-DEVIATIONS.md): `ε C^{DOZZ}(α, ε, α) → 4 R^{DOZZ}(α)` as `ε → 0`, for generic
`α`. -/
theorem dozzFormula_bridge {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) :
    ∀ᶠ α in codiscrete ℂ,
      Tendsto (fun ε : ℂ => ε * dozzFormula γ μ U α ε α) (𝓝[≠] 0)
        (𝓝 (4 * reflectionDOZZ γ μ α)) := by exact DOZZ.Proofs.dozzFormula_bridge hγ hγ2 hμ hU

end DOZZ
