/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.Assembly.AdmissibleGMC

/-! The statement `DOZZ.admissibleLogRegularization_GMC_exists`,
proved by `DOZZ.Proofs.admissibleLogRegularization_GMC_exists`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The GMC construction from an admissible regularization gives a measurable admissible version
carried by the chart for every `0 < γ < 2`. -/
theorem admissibleLogRegularization_GMC_exists
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ M : Ω → Measure ℂ, IsAdmissibleGMCVersion P U dens Y γ M := by exact DOZZ.Proofs.admissibleLogRegularization_GMC_exists P U dens ε₀ Y hY γ hγ hγ2

end DOZZ
