/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.TailMargins

/-! The literal ceiling `DOZZ.twoInsertionTailCeiling` of the two-insertion tail and its five
available remainder exponents. -/

@[expose] public section
open Set
namespace DOZZ.Proofs

theorem sumtail_one_error_continuousOn (γ : ℝ) (K : Set ℝ) (hγ : 0 < γ)
    (hK : ∀ α ∈ K, γ/2 < α ∧ α < Q γ) :
    ContinuousOn (oneInsertionErrorCeiling γ) K := by
  have hp : Continuous (reflectionExponent γ) := by unfold reflectionExponent; fun_prop
  have hm : Continuous (oneInsertionMomentCeiling γ) := by
    unfold oneInsertionMomentCeiling
    exact (hp.add continuous_const).min continuous_const
  unfold oneInsertionErrorCeiling
  apply (hm.sub hp).continuousOn.div (continuous_const.add hm).continuousOn
  intro α hα
  obtain ⟨hpa,hpb⟩ := residue_critical_order_bounds γ α hγ (hK α hα).1 (hK α hα).2
  have hmp : 0 < oneInsertionMomentCeiling γ α := by
    unfold oneInsertionMomentCeiling
    exact lt_min (by positivity) (by positivity)
  change 1+oneInsertionMomentCeiling γ α ≠ 0
  exact (by linarith only [hmp] : 0 < 1+oneInsertionMomentCeiling γ α).ne'

theorem sumtail_one_error_lt_one (γ α : ℝ) (hγ : 0 < γ)
    (hα : γ/2 < α) (hαQ : α < Q γ) : oneInsertionErrorCeiling γ α < 1 := by
  obtain ⟨hp,hpb⟩ := residue_critical_order_bounds γ α hγ hα hαQ
  have hm : 0 < oneInsertionMomentCeiling γ α := by
    unfold oneInsertionMomentCeiling
    exact lt_min (by positivity) (by positivity)
  unfold oneInsertionErrorCeiling
  apply (div_lt_one (by linarith only [hm])).mpr
  linarith only [hp]

/-- The ceiling is bounded by each one-point error, both shift errors and both joint errors. -/
theorem sumtail_ceiling_bounds (γ α2 α3 : ℝ) :
    twoInsertionTailCeiling γ α2 α3 ≤ reflectionExponent γ α2+oneInsertionErrorCeiling γ α2 ∧
    twoInsertionTailCeiling γ α2 α3 ≤ reflectionExponent γ α3+oneInsertionErrorCeiling γ α3 ∧
    twoInsertionTailCeiling γ α2 α3 ≤ reflectionExponent γ α2+1/2 ∧
    twoInsertionTailCeiling γ α2 α3 ≤ reflectionExponent γ α3+1/2 ∧
    twoInsertionTailCeiling γ α2 α3 ≤ reflectionExponent γ α2+reflectionExponent γ α3/2 ∧
    twoInsertionTailCeiling γ α2 α3 ≤ reflectionExponent γ α3+reflectionExponent γ α2/2 := by
  have he (α : ℝ) : (Q γ-α)/γ = reflectionExponent γ α/2 := by
    unfold reflectionExponent
    ring
  have hl := min_le_left (reflectionExponent γ α2+twoInsertionPointLoss γ α2 α3)
    (reflectionExponent γ α3+twoInsertionPointLoss γ α3 α2)
  have hr := min_le_right (reflectionExponent γ α2+twoInsertionPointLoss γ α2 α3)
    (reflectionExponent γ α3+twoInsertionPointLoss γ α3 α2)
  change twoInsertionTailCeiling γ α2 α3 ≤ _ at hl hr
  have loss (α αo : ℝ) : twoInsertionPointLoss γ α αo ≤ oneInsertionErrorCeiling γ α ∧
      twoInsertionPointLoss γ α αo ≤ 1/2 ∧
      twoInsertionPointLoss γ α αo ≤ reflectionExponent γ αo/2 := by
    unfold twoInsertionPointLoss
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (by rw [← he]; exact min_le_left _ _)⟩
  refine ⟨hl.trans (add_le_add le_rfl (loss α2 α3).1),
    hr.trans (add_le_add le_rfl (loss α3 α2).1),
    hl.trans (add_le_add le_rfl (loss α2 α3).2.1),
    hr.trans (add_le_add le_rfl (loss α3 α2).2.1),
    hl.trans (add_le_add le_rfl (loss α2 α3).2.2),
    hr.trans (add_le_add le_rfl (loss α3 α2).2.2)⟩

end DOZZ.Proofs
