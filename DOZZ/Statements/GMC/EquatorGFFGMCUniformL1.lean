/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Assembly.UniformL1

/-! The statement `DOZZ.equatorGFF_GMC_uniform_L1`,
proved by `DOZZ.Proofs.equatorGFF_GMC_uniform_L1`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Uniform `L¹` convergence of regularized GMC masses on compact charge intervals, uniformly
over bounded Borel tests supported in a compact set. -/
theorem equatorGFF_GMC_uniform_L1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (I : Set ℝ) (hI : IsCompact I) (hI2 : I ⊆ Set.Ioo 0 2)
    (K : Set ℂ) (hK : IsCompact K) (Lb : ℝ) :
    Tendsto (fun r : ℝ => ⨆ γ ∈ I, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
        (_ : ∀ x, |f x| ≤ Lb) (_ : ∀ x ∉ K, f x = 0),
        ∫⁻ ω, ENNReal.ofReal
          |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P)
      atTop (𝓝 0) := by exact DOZZ.Proofs.equatorGFF_GMC_uniform_L1 P X hX Xc hXc Mfam hMfam I hI hI2 K hK Lb

end DOZZ
