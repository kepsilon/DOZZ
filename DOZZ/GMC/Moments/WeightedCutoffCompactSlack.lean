/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedExponent
import Mathlib.Topology.Order.Compact

/-! Uniform positivity of the weighted scaling exponent on compact parameter sets. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Pointwise strict weighted-moment slack on a compact parameter set has a uniform positive
margin in the annular scaling exponent. -/
theorem exists_uniform_weighted_cutoff_exponent_lower_bound
    {γ : ℝ} (hγ : 0 < γ) (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ t ∈ T, 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ T,
      ε ≤ γ * (Q γ - t.1) * t.2 - γ ^ 2 * t.2 ^ 2 / 2 := by
  let exponent : ℝ × ℝ → ℝ := fun t =>
    γ * (Q γ - t.1) * t.2 - γ ^ 2 * t.2 ^ 2 / 2
  have hexponent : Continuous exponent := by
    dsimp [exponent]
    fun_prop
  have hpositive : ∀ t ∈ T, 0 < exponent t := by
    intro t ht
    have h := hTadm t ht
    exact weightedGmcMomentExponent_pos_of_sharp_range hγ h.1 h.2
  obtain ⟨ε, hε, hεlower⟩ := hT.exists_forall_le'
    hexponent.continuousOn hpositive
  refine ⟨ε, hε, ?_⟩
  intro t ht
  simpa [exponent] using hεlower t ht

end DOZZ.Proofs
