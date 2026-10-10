/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.SharpMoments.InverseGamma

/-! The statement `DOZZ.equatorGFF_regularizedGMC_inverse_moment_uniform`,
proved by `DOZZ.Proofs.equatorGFF_regularizedGMC_inverse_moment_uniform`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Every inverse moment of the circle-average cutoff mass of a nonempty open set is bounded
uniformly in the cutoff and in `γ` on compact subsets of `(0,2)`. -/
theorem equatorGFF_regularizedGMC_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (O : Set ℂ) (hO : IsOpen O) (hOne : O.Nonempty) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, ∀ r : ℝ, 0 ≤ r →
      (∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω O) (-q) ∂P) ≤ ENNReal.ofReal C := by exact DOZZ.Proofs.equatorGFF_regularizedGMC_inverse_moment_uniform P X hX Xc hXc Γ hΓ hΓ2 O hO hOne q hq

end DOZZ
