/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Roots.Existence

/-! The statement `DOZZ.dozz_existence`, proved by `DOZZ.Proofs.dozz_existence`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- **Existence**: for every `0 < γ < 2` there are a probability space, an equator GFF and its
GMC (whose circle averages exist by `IsGMCOf`), and a function `Υ_{γ/2}`. -/
theorem dozz_existence (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    (∃ U : ℂ → ℂ, IsUpsilon γ U) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ),
        IsEquatorGFF P X ∧ IsGMCOf P X γ M := by exact DOZZ.Proofs.dozz_existence γ hγ hγ2

end DOZZ
