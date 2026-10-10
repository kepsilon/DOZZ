/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionKernel
public import DOZZ.Statements.Defs.Rho
public import DOZZ.Statements.Defs.SExp
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The canonical density picks up precisely the charge times the pinning change. -/
theorem rho_reflection_density (γ α₁ α₂ α₃ : ℝ) (x : ℂ) :
    normPlus (1 - x) ^ (γ * (α₁ + α₂ + α₃)) /
      (‖1 - x‖ ^ (γ * α₁) * ‖(1 - x) - 1‖ ^ (γ * α₂)) =
    Real.exp (γ * (α₁ + α₂ + α₃) * symmetryReflectionPotential x) *
      (normPlus x ^ (γ * (α₂ + α₁ + α₃)) /
        (‖x‖ ^ (γ * α₂) * ‖x - 1‖ ^ (γ * α₁))) := by
  have hn (y : ℂ) : 0 < normPlus y := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖y‖)
  have he (t : ℝ) : normPlus (1 - x) ^ t =
      Real.exp (t * symmetryReflectionPotential x) * normPlus x ^ t := by
    rw [Real.rpow_def_of_pos (hn (1 - x)), Real.rpow_def_of_pos (hn x), ← Real.exp_add]
    congr 1
    unfold symmetryReflectionPotential
    ring
  rw [norm_sub_rev (1 : ℂ) x, show (1 - x) - 1 = -x by ring, norm_neg, he]
  have hs : α₂ + α₁ + α₃ = α₁ + α₂ + α₃ := by ring
  rw [hs]
  ring

/-- The Wick and reference-density correction has exponent twice gamma Q. -/
theorem symmetry_reflection_wick_exponent (γ : ℝ) (hγ : γ ≠ 0) :
    γ ^ 2 + 4 = 2 * γ * Q γ := by
  unfold Q
  field_simp
  ring

/-- The remaining root weight is exactly the exponent canceled by the Gaussian tilt. -/
theorem symmetry_reflection_charge_exponent (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) :
    γ * (α₁ + α₂ + α₃) - 2 * γ * Q γ = γ ^ 2 * sExp γ α₁ α₂ α₃ := by
  unfold sExp
  field_simp

end DOZZ.Proofs
