/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedAllRootFinite
public import DOZZ.GMC.Construction.RootedGlobalIdentity

/-! The rooted identity for all nonnegative measurable observables. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- The exact rooted identity, using almost sure finiteness at every deterministic root. -/
theorem equatorGFF_rooted_GMC_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M)
    (H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) =>
      H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ∫⁻ u, H u (fun f => X ω f) (M ω) ∂M ω ∂P) =
      ∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f)
        (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure := by
  exact rooted_GMC_identity_of_ae_root_finite P X hX γ hγ hγ2 M hM
    (ae_of_all gmcReferenceMeasure fun u =>
      equatorGFF_rooted_measure_finite P X hX γ hγ hγ2 M hM u) H hH

end DOZZ.Proofs
