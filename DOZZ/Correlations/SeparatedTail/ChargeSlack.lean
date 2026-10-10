/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact

/-! One Hölder exponent works for every charge in the compact parameter sets of
`DOZZ.separatedSingularMass_joint_tail`. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

/-- The charge restriction in `DOZZ.separatedSingularMass_joint_tail` puts the reflection exponent
below the bulk GMC threshold. -/
theorem separatedTail_reflectionExponent_lt_bulk {γ α : ℝ} (hγ : 0 < γ) (hα : γ/2 < α) :
    reflectionExponent γ α < 4/γ^2 := by
  unfold reflectionExponent Q
  apply (div_lt_iff₀ hγ).mpr
  field_simp
  nlinarith

/-- A deterministic choice close to one keeps half of the supplied strict charge slack.
No charge-dependent choice of the Hölder exponent enters the uniform bound. -/
theorem separatedTail_exists_uniform_holder_slack {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∃ q : ℝ, 1 < q ∧ ∀ α : ℝ, γ/2 < α → ε < reflectionExponent γ α →
      0 < q*(reflectionExponent γ α-ε) ∧
      q*(reflectionExponent γ α-ε)+ε/2 ≤ reflectionExponent γ α ∧
      q*(reflectionExponent γ α-ε)+ε/2 < 4/γ^2 := by
  let B : ℝ := 4/γ^2
  have hB : 0 < B := by dsimp [B]; positivity
  let q := 1+ε/(2*(B+1))
  have hq : 1 < q := by
    have : 0 < ε/(2*(B+1)) := by positivity
    dsimp [q]
    linarith
  refine ⟨q, hq, fun α hα hεα => ?_⟩
  have hpB := separatedTail_reflectionExponent_lt_bulk hγ hα
  have hp0 : 0 < reflectionExponent γ α-ε := sub_pos.mpr hεα
  have hfrac : ε/(2*(B+1))*(B+1) = ε/2 := by field_simp
  have hmargin : q*(reflectionExponent γ α-ε)+ε/2 ≤ reflectionExponent γ α := by
    dsimp [q]
    have hmul := mul_le_mul_of_nonneg_left
      (show reflectionExponent γ α-ε ≤ B+1 by dsimp [B]; linarith) (by positivity :
        0 ≤ ε/(2*(B+1)))
    nlinarith
  exact ⟨mul_pos (by linarith) hp0, hmargin, hmargin.trans_lt hpB⟩

end DOZZ.Proofs
