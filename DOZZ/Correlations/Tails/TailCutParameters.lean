/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.TailMargins

/-! Strict moment and logarithmic-cut choices for the remainder of the one-insertion tail
estimate. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The printed error ceiling is exactly the condition allowing both the last-cut error
and the excluded higher-moment tail to decay faster than `x^(-p-η)`. -/
theorem tail_cut_parameters (p β η : ℝ) (hp : 0 < p) (hβ : p < β)
    (hη : 0 < η) (hceil : η < (β-p)/(1+β)) :
    ∃ a r : ℝ, η < a ∧ a < 1 ∧ 0 < r ∧ r < β ∧ p+η < (1-a)*r := by
  have hβ0 : 0 < β := hp.trans hβ
  have hden : 0 < 1+β := by linarith
  have hslack := (lt_div_iff₀ hden).mp hceil
  have hηtop : η < (β-p-η)/β := (lt_div_iff₀ hβ0).mpr (by nlinarith only [hslack])
  obtain ⟨a, hηa, hatop⟩ := exists_between hηtop
  have htop1 : (β-p-η)/β < 1 := (div_lt_one hβ0).mpr (by linarith)
  have ha1 : a < 1 := hatop.trans htop1
  have haden : 0 < 1-a := sub_pos.mpr ha1
  have har := (lt_div_iff₀ hβ0).mp hatop
  have hrlow : (p+η)/(1-a) < β := (div_lt_iff₀ haden).mpr (by nlinarith only [har])
  obtain ⟨r, hrr, hrβ⟩ := exists_between hrlow
  have hr : 0 < r := (div_pos (by linarith : 0 < p+η) haden).trans hrr
  refine ⟨a, r, hηa, ha1, hr, hrβ, ?_⟩
  have h := (div_lt_iff₀ haden).mp hrr
  nlinarith only [h]

/-- The same strict choices apply to the literal one-insertion ceiling
`DOZZ.oneInsertionErrorCeiling`. -/
theorem oneInsertion_cut_parameters (γ α η : ℝ) (hγ : 0 < γ)
    (hα : γ/2 < α) (hαQ : α < Q γ) (hη : 0 < η)
    (hceil : η < oneInsertionErrorCeiling γ α) :
    ∃ a r : ℝ, η < a ∧ a < 1 ∧ 0 < r ∧ r < oneInsertionMomentCeiling γ α ∧
      reflectionExponent γ α+η < (1-a)*r := by
  have hp := (residue_critical_order_bounds γ α hγ hα hαQ).1
  have hβ : reflectionExponent γ α < oneInsertionMomentCeiling γ α := by
    unfold oneInsertionMomentCeiling
    exact lt_min (lt_add_of_pos_right _ (by positivity))
      (residue_critical_order_bounds γ α hγ hα hαQ).2
  exact tail_cut_parameters _ _ η hp hβ hη hceil


end DOZZ.Proofs
