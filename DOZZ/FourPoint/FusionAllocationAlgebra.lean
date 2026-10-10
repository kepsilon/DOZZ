/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionKernelBounds
public import DOZZ.FourPoint.RetainedAnnuliUniformOrders
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Exact fusion charge allocations and compact bounds. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The last insertion adds its charge to the triple drift. -/
theorem four_fusion_nu4 (γ : ℝ) (α : Fin 4 → ℝ) :
    fourFusionNu4 γ α = fourFusionNu3 γ α + α 3 := by
  unfold fourFusionNu4 fourFusionNu3
  rw [Fin.sum_univ_four]
  ring

/-- The third insertion adds its charge to the pair drift. -/
theorem four_fusion_nu3 (γ : ℝ) (α : Fin 4 → ℝ) :
    fourFusionNu3 γ α = fourFusionNu2 γ α + α 2 := by
  unfold fourFusionNu3 fourFusionNu2
  ring

/-- Completing the Gaussian square at the fused allocated order. -/
theorem fused_allocated_scale_exponent (γ T : ℝ) (hγ : γ ≠ 0) :
    γ * T * ((T - Q γ) / γ) +
      (γ * Q γ * (-((T - Q γ) / γ)) - γ ^ 2 * ((T - Q γ) / γ) ^ 2 / 2) =
      (T - Q γ) ^ 2 / 2 := by
  field_simp
  ring

/-- The possibly negative middle exponent in fusion case two is retained literally. -/
theorem fusion_middle_exponent (γ : ℝ) (α : Fin 4 → ℝ) :
    fourFusionNu2 γ α * fourFusionNu3 γ α - fourFusionNu2 γ α ^ 2 / 2 =
      (fourFusionNu3 γ α ^ 2 - (α 2) ^ 2) / 2 := by
  rw [four_fusion_nu3]
  ring

/-- Compact parameter sets supply one positive bound for every charge and moment order. -/
theorem fusion_compact_parameter_bound
    (A : Set (Fin 4 → ℝ)) (hA : IsCompact A) (S : Set ℝ) (hS : IsCompact S) :
    ∃ H : ℝ, 1 ≤ H ∧ (∀ α ∈ A, ∀ i : Fin 4, |α i| ≤ H) ∧ (∀ q ∈ S, |q| ≤ H) := by
  obtain ⟨CA, hCA⟩ := hA.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨CS, hCS⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨max 1 (max CA CS), le_max_left _ _, ?_, ?_⟩
  · intro α hα i
    exact (show |α i| ≤ ‖α‖ from by simpa only [Real.norm_eq_abs] using norm_le_pi_norm α i).trans
      ((hCA α hα).trans ((le_max_left CA CS).trans (le_max_right _ _)))
  · intro q hq
    exact (show |q| ≤ CS from by simpa only [Real.norm_eq_abs, id_eq] using hCS q hq).trans
      ((le_max_right CA CS).trans (le_max_right _ _))

end DOZZ.Proofs
