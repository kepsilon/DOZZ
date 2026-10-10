/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.AdmissibleGMCCoordinateChange

/-! The statement `DOZZ.admissibleLogRegularization_GMC_coordinate_change`,
proved by `DOZZ.Proofs.admissibleLogRegularization_GMC_coordinate_change`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Chart transport of admissible GMC along an open partial homeomorphism. -/
theorem admissibleLogRegularization_GMC_coordinate_change
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U V : Set ℂ) (densU densV : ℂ → ℝ)
    (εU εV : ℝ) (YU YV : Ω → ℝ → ℂ → ℝ)
    (hYU : IsAdmissibleLogRegularization P U densU εU YU)
    (hYV : IsAdmissibleLogRegularization P V densV εV YV)
    (φ : OpenPartialHomeomorph ℂ ℂ) (hφU : φ.source = U) (hφV : φ.target = V)
    (hReference : logRegularizationReference V densV =
      (logRegularizationReference U densU).map φ)
    (hField : ∀ ω ε, ∀ y ∈ V, YV ω ε y = YU ω ε (φ.symm y))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M N : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U densU YU γ M)
    (hN : IsAdmissibleGMCVersion P V densV YV γ N) :
    ∀ᵐ ω ∂P, (M ω).map φ = N ω := by exact DOZZ.Proofs.admissibleLogRegularization_GMC_coordinate_change P U V densU densV εU εV YU YV hYU hYV φ hφU hφV hReference hField γ hγ hγ2 M N hM hN

end DOZZ
