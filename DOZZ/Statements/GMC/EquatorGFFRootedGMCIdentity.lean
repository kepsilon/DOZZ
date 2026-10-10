/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Construction.RootedIdentity

/-! The statement `DOZZ.equatorGFF_rooted_GMC_identity`,
proved by `DOZZ.Proofs.equatorGFF_rooted_GMC_identity`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The rooted GMC identity for every nonnegative measurable functional of the root, all test
coordinates, and the chaos measure. The translated field contains `γ G(u,·)` and the rooted
measure contains `e^{γ²G(u,·)}`. See [KRV, Corollary 12.2] (corrected; erratum K3, see
docs/ERRATA-AND-DEVIATIONS.md). -/
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
        (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure := by exact DOZZ.Proofs.equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM H hH

end DOZZ
