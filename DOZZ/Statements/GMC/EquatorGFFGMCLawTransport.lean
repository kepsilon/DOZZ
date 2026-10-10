/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.EquatorGFFChaosTransportLaw

/-! The statement `DOZZ.equatorGFF_GMC_law_transport`,
proved by `DOZZ.Proofs.equatorGFF_GMC_law_transport`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Characterization transport: two equator GFF models with `IsGMCOf` chaoses at the same
`0 < γ < 2`, on arbitrary probability spaces, have the same joint law of test evaluations and
chaos. -/
theorem equatorGFF_GMC_law_transport
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P = ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by exact DOZZ.Proofs.equatorGFF_GMC_law_transport P X hX P' X' hX' γ hγ hγ2 M hM M' hM' H hH

end DOZZ
