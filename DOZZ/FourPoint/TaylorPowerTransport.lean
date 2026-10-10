/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorScales

/-! Transporting the three actual regional radius powers to one Taylor power. -/

@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs

/-- The annular, optimized intermediate and near-root physical powers share a strict gain. -/
theorem taylor_regional_powers (γ α δ ε η W q r : ℝ)
    (hγ : 0 < γ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hηd : η ≤ δ * (γ * (α - γ / 2)))
    (hηnear : η ≤ ε * γ ^ 2 / 2)
    (hmid : γ * (Q γ - α) - 2 + η ≤ -2 - 2 * ε + (1 - δ) * W / (2 * q)) :
    (r ^ (1 - δ)) ^ (γ * (Q γ - α) - 2) ≤ r ^ (γ * (Q γ - α) - 2 + η) ∧
    ((r ^ (1 + ε))⁻¹) ^ 2 * (r ^ (1 - δ)) ^ (W / (2 * q)) ≤
      r ^ (γ * (Q γ - α) - 2 + η) ∧
    r ^ (-γ * α) * (r ^ (1 + ε)) ^ (γ ^ 2 / 2) ≤
      r ^ (γ * (Q γ - α) - 2 + η) := by
  have hκ : γ * (Q γ - α) - 2 = γ ^ 2 / 2 - γ * α := by
    unfold Q
    field_simp [hγ.ne']
    ring
  have hmono (a b : ℝ) (hab : a ≤ b) : r ^ b ≤ r ^ a :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 hab
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_mul hr.le]
    apply hmono
    rw [hκ]
    nlinarith only [hηd]
  · have heq : ((r ^ (1 + ε))⁻¹) ^ 2 * (r ^ (1 - δ)) ^ (W / (2 * q)) =
        r ^ (-2 - 2 * ε + (1 - δ) * W / (2 * q)) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (Real.rpow_nonneg hr.le _),
        ← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
      congr 1
      ring
    rw [heq]
    exact hmono _ _ hmid
  · rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    apply hmono
    rw [hκ]
    nlinarith only [hηnear]

end DOZZ.Proofs
