/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.Moments.InversionLaw

/-! The statement `DOZZ.equatorGFF_GMC_inversion_law`,
proved by `DOZZ.Proofs.equatorGFF_GMC_inversion_law`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Inversion chart law of the equator chaos, by chart transport along `φ(x) = 1/x`. -/
theorem equatorGFF_GMC_inversion_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, H ((M ω).map (fun x => x⁻¹)) ∂P = ∫⁻ ω, H (M ω) ∂P := by exact DOZZ.Proofs.equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM H hH

end DOZZ
