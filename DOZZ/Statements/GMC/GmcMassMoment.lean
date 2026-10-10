/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass

/-! The definition `DOZZ.gmcMassMoment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Extended expectation of the `p`th power of the GMC mass on a set. Using `ENNReal.rpow`
retains infinite negative moments at zero. See [KRV, (condmom)]. -/
noncomputable def gmcMassMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (A : Set ℂ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.rpow (M ω A) p ∂P

end DOZZ
