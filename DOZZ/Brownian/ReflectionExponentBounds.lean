/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionExponent

/-!
# Parameter bounds for the Brownian reflection moment

The physical charge interval is exactly the positive subcritical moment range for the
reflection mass, with drift `ν = Q - α`.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- On the physical charge interval, the associated conditioned drift is positive and the
reflection exponent is a positive subcritical moment order. -/
theorem reflectionExponent_in_subcritical_range
    (γ α : ℝ) (hγ : 0 < γ) (hα : γ / 2 < α ∧ α < Q γ) :
    0 < Q γ - α ∧ 0 < reflectionExponent γ α ∧
      reflectionExponent γ α < 4 / γ ^ 2 := by
  have hν : 0 < Q γ - α := sub_pos.mpr hα.2
  have hsub : Q γ - α < 2 / γ := by
    dsimp [Q]
    nlinarith [hα.1]
  have hp : 0 < reflectionExponent γ α := by
    unfold reflectionExponent
    exact div_pos (mul_pos (by norm_num) hν) hγ
  have hpupper : reflectionExponent γ α < 4 / γ ^ 2 := by
    unfold reflectionExponent
    calc
      2 * (Q γ - α) / γ < 2 * (2 / γ) / γ := by
        apply (div_lt_div_iff₀ hγ hγ).2
        nlinarith
      _ = 4 / γ ^ 2 := by
        field_simp [hγ.ne']
        ring
  exact ⟨hν, hp, hpupper⟩

/-- The Brownian reflection moment order tends to zero as the charge tends to `Q`. -/
theorem tendsto_reflectionExponent_at_Q (γ : ℝ) :
    Tendsto (fun α : ℝ => reflectionExponent γ α) (𝓝 (Q γ)) (𝓝 0) := by
  have hcont : ContinuousAt (fun α : ℝ => reflectionExponent γ α) (Q γ) := by
    unfold reflectionExponent
    fun_prop
  simpa [reflectionExponent] using hcont.tendsto

end DOZZ.Proofs

end
