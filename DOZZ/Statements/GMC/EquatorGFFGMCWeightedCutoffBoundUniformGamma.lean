/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.WeightedCutoff.UniformGamma

/-! The statement `DOZZ.equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma`,
proved by `DOZZ.Proofs.equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Compact-parameter version of the cutoff weighted bound, including charge uniformity. -/
theorem equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, t.1 < Q γ ∧ 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    (K : Set ℂ) (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ z ∈ K, ∀ δ R : ℝ,
      0 < δ → δ ≤ R → R ≤ r₀ →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω) t.2 ∂P) ≤
        ENNReal.ofReal (C * Real.rpow R
          (γ * (Q γ - t.1) * t.2 - γ ^ 2 * t.2 ^ 2 / 2)) := by exact DOZZ.Proofs.equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma P X hX Γ hΓ hΓ2 Xc hXc T hT hTadm K hK r₀ hr₀

end DOZZ
