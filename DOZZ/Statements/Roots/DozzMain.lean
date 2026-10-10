/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Roots.Assembly

/-! The statement `DOZZ.dozz_main`, proved by `DOZZ.Proofs.dozz_main`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- **DOZZ formula** ([KRV, Theorem 2.4]). -/
theorem dozz_main (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃ := by exact DOZZ.Proofs.dozz_main γ μ hγ hγ2 hμ α₁ α₂ α₃ hα hs U hU P X M hX hM

end DOZZ
