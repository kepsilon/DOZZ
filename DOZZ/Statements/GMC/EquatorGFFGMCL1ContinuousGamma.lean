/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Assembly.CircleUniformL1

/-! The statement `DOZZ.equatorGFF_GMC_L1_continuous_gamma`,
proved by `DOZZ.Proofs.equatorGFF_GMC_L1_continuous_gamma`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `L¹` continuity of the GMC mass against bounded continuous tests as the charge varies on
the same probability space. -/
theorem equatorGFF_GMC_L1_continuous_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (f : BoundedContinuousFunction ℂ ℝ) (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Set.Ioo (0 : ℝ) 2) :
    Tendsto (fun γ => ∫⁻ ω, ENNReal.ofReal
        |∫ x, f x ∂Mfam γ ω - ∫ x, f x ∂Mfam γ₀ ω| ∂P) (𝓝 γ₀) (𝓝 0) := by exact DOZZ.Proofs.equatorGFF_GMC_L1_continuous_gamma P X hX Mfam hMfam f γ₀ hγ₀

end DOZZ
