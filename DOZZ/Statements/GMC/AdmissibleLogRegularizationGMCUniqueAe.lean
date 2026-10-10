/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.Assembly.AdmissibleGMC

/-! The statement `DOZZ.admissibleLogRegularization_GMC_unique_ae`,
proved by `DOZZ.Proofs.admissibleLogRegularization_GMC_unique_ae`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Compatible admissible regularizations on one chart have the same GMC limit almost surely. -/
theorem admissibleLogRegularization_GMC_unique_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M N : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P U dens Z γ N) :
    ∀ᵐ ω ∂P, M ω = N ω := by exact DOZZ.Proofs.admissibleLogRegularization_GMC_unique_ae P U dens ε₀ ε₁ Y Z hY hZ hYZ γ hγ hγ2 M N hM hN

end DOZZ
