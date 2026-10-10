/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion

/-! Uniqueness of compact-test limits for one admissible logarithmic regularization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Two admissible GMC versions for the same regularization have almost surely equal integrals
against each compactly supported continuous test. This is uniqueness of each scalar limit in
measure; identifying the random measures requires a countable determining family. -/
theorem admissible_regularization_test_integral_unique_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (γ : ℝ) (M N : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P U dens Y γ N)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hfCompact : HasCompactSupport (f : ℂ → ℝ))
    (hfSupport : tsupport (f : ℂ → ℝ) ⊆ U) :
    (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] fun ω => ∫ x, f x ∂N ω := by
  rcases hM with ⟨_, _, _, hMlim⟩
  rcases hN with ⟨_, _, _, hNlim⟩
  exact tendstoInMeasure_ae_unique (hMlim f hfCompact hfSupport)
    (hNlim f hfCompact hfSupport)



end DOZZ.Proofs
