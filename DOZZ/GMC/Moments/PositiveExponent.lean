/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q

/-! The unweighted annular exponent governing the positive-moment induction. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The exact-scale moment exponent `ξγ(p)`. -/
noncomputable def gmcScaleExponent (γ p : ℝ) : ℝ :=
  γ * Q γ * p - γ ^ 2 * p ^ 2 / 2

/-- Subtracting the covariance singularity at induction order `p-1` factors into the
dimension slack and the bulk-moment slack. -/
theorem gmcScaleAnnularExponent_eq (γ p : ℝ) (hγ : γ ≠ 0) :
    gmcScaleExponent γ (p - 1) - γ ^ 2 * (p - 1) =
      (p - 1) * (2 - γ ^ 2 * p / 2) := by
  unfold gmcScaleExponent Q
  field_simp [hγ]
  ring




end DOZZ.Proofs
