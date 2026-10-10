/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.KahaneLimitLipschitz

/-! The statement `DOZZ.kahane_limit_lipschitz`, proved by `DOZZ.Proofs.kahane_limit_lipschitz`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Passage of a finite-cutoff Kahane comparison through `L¹` convergence for Lipschitz tests.
Applying this to the convex truncations `F_R` and then increasing `R` gives the positive power
part of `thm:limit-kahane`. -/
theorem kahane_limit_lipschitz
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Xr : ℕ → ΩX → ℝ) (Yr : ℕ → ΩY → ℝ) (X : ΩX → ℝ) (Y : ΩY → ℝ)
    (hX : Tendsto (fun n => eLpNorm (fun ω => Xr n ω - X ω) 1 PX) atTop (𝓝 0))
    (hY : Tendsto (fun n => eLpNorm (fun ω => Yr n ω - Y ω) 1 PY) atTop (𝓝 0))
    (F : ℝ → ℝ) (hF : Measurable F)
    (hLip : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |F x - F y| ≤ C * |x - y|)
    (hIX : ∀ n, Integrable (fun ω => F (Xr n ω)) PX)
    (hIY : ∀ n, Integrable (fun ω => F (Yr n ω)) PY)
    (hI : Integrable (fun ω => F (X ω)) PX ∧ Integrable (fun ω => F (Y ω)) PY)
    (hcmp : ∀ n, ∫ ω, F (Xr n ω) ∂PX ≤ ∫ ω, F (Yr n ω) ∂PY) :
    ∫ ω, F (X ω) ∂PX ≤ ∫ ω, F (Y ω) ∂PY := by exact DOZZ.Proofs.kahane_limit_lipschitz PX PY Xr Yr X Y hX hY F hF hLip hIX hIY hI hcmp

end DOZZ
