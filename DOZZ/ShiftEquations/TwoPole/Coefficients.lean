/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.LocalTail
public import DOZZ.ShiftEquations.PoleSubtracted.Window
public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
public import DOZZ.Statements.ShiftEquations.TwoPoleFirstResidue
public import DOZZ.Statements.ShiftEquations.TwoPoleSecondResidue

/-!
# The tail coefficients and the residues

At the pole `2` the one-insertion tail coefficient is `|2|^{-4α₂(Q-α₂)} F₂(2)^{p₂} R̄ = 2^{-4p₂} R̄`
with `p₂ = 1 - 2η/γ`, because `F₂(2) = 2^{2γη}`; at `-2` it is `2^{-4p₃} R̄` with `p₃ = 1 + 2η/γ`.
The frame factor `(2/γ) 2^{4(1-z/γ)}` cancels these position factors, leaving the residues
`2 p R̄ = (4/γ)(Q - α) R̄` (erratum K26, see docs/ERRATA-AND-DEVIATIONS.md).
-/

@[expose] public section

namespace DOZZ.Proofs

theorem reflectionExponent_pole_neg {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    reflectionExponent γ (2 / γ - η) = 1 + 2 * η / γ := by
  rw [reflectionExponent, Q]
  field_simp
  ring

/-- The tail coefficient at `2` is `2^{-4p₂} R̄`. -/
theorem tailCoefficient_two {γ : ℝ} (hγ : 0 < γ) (η R : ℝ) :
    oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R =
      2 ^ (-(4 * (1 - 2 * η / γ))) * R := by
  unfold oneInsertionTailCoefficient
  rw [poleFactorTwo_two hγ, reflectionExponent_pole hγ η]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  rw [Q]
  field_simp
  ring

/-- The tail coefficient at `-2` is `2^{-4p₃} R̄`. -/
theorem tailCoefficient_negTwo {γ : ℝ} (hγ : 0 < γ) (η R : ℝ) :
    oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2)) R =
      2 ^ (-(4 * (1 + 2 * η / γ))) * R := by
  unfold oneInsertionTailCoefficient
  rw [poleFactorNegTwo_negTwo hγ, reflectionExponent_pole_neg hγ η]
  have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [h2, Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  rw [Q]
  field_simp
  ring

/-- The first residue: `γ c₂ (2/γ) 2^{4p₂} p₂ = (4/γ)(Q - α₂) R̄`. -/
theorem firstResidue_eq {γ : ℝ} (hγ : 0 < γ) (η R : ℝ) :
    γ * (2 ^ (-(4 * (1 - 2 * η / γ))) * R) *
        (2 / γ * 2 ^ (4 * (1 - 2 * η / γ)) * (1 - 2 * η / γ)) =
      4 / γ * (Q γ - (2 / γ + η)) * R := by
  have h : (2 : ℝ) ^ (-(4 * (1 - 2 * η / γ))) * 2 ^ (4 * (1 - 2 * η / γ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hA0 : (2 : ℝ) ^ (-(4 * (1 - 2 * η / γ))) ≠ 0 := by positivity
  generalize (2 : ℝ) ^ (-(4 * (1 - 2 * η / γ))) = A at h hA0 ⊢
  generalize (2 : ℝ) ^ (4 * (1 - 2 * η / γ)) = B at h ⊢
  have hB : B = A⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hB
  rw [Q]
  field_simp
  ring

/-- The second residue: `γ c₃ (2/γ) 2^{4p₃} p₃ = (4/γ)(Q - (Q - η) + γ/2) R̄`. -/
theorem secondResidue_eq {γ : ℝ} (hγ : 0 < γ) (η R : ℝ) :
    γ * (2 ^ (-(4 * (1 + 2 * η / γ))) * R) *
        (2 / γ * 2 ^ (4 * (1 + 2 * η / γ)) * (1 + 2 * η / γ)) =
      4 / γ * (Q γ - (Q γ - η) + γ / 2) * R := by
  have h : (2 : ℝ) ^ (-(4 * (1 + 2 * η / γ))) * 2 ^ (4 * (1 + 2 * η / γ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hA0 : (2 : ℝ) ^ (-(4 * (1 + 2 * η / γ))) ≠ 0 := by positivity
  generalize (2 : ℝ) ^ (-(4 * (1 + 2 * η / γ))) = A at h hA0 ⊢
  generalize (2 : ℝ) ^ (4 * (1 + 2 * η / γ)) = B at h ⊢
  have hB : B = A⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hB
  field_simp
  ring

end DOZZ.Proofs

end
