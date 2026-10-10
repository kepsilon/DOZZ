/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedUniformNegative

/-! A charge-independent lower random mass for all retained Coulomb integrals. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- A bounded charge box admits one deterministic positive multiplier of a fixed disk mass as
a lower bound, uniformly over every retained set containing that disk. -/
theorem retained_uniform_disk_lower {N : ℕ} (μ : Measure ℂ)
    (γ : ℝ) (hγ : 0 < γ) (A : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ)
    (hα : ∀ i, |α i| ≤ A) (hinf : |αinf| ≤ A)
    (O : Set ℂ) (R : ℝ) (hR : 1 ≤ R) (hz : ∀ i, 2 * ‖z i‖ ≤ R)
    (hO : Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8) ⊆ O) :
    (ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
      ENNReal.ofReal ((R + 2) ^ (-(γ * A)))) *
        μ (Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8)) ≤
      ∫⁻ x in O, coulombWeight γ α z αinf x ∂μ := by
  have hsum : ∑ j, |γ * α j| ≤ N * (γ * A) := by
    calc
      _ ≤ ∑ _j : Fin N, γ * A := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul, abs_of_pos hγ]
        exact mul_le_mul_of_nonneg_left (hα j) hγ.le)
      _ = _ := by simp
  have hi : |γ * αinf| ≤ γ * A := by
    rw [abs_mul, abs_of_pos hγ]
    exact mul_le_mul_of_nonneg_left hinf hγ.le
  have hc : ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
      ENNReal.ofReal ((R + 2) ^ (-(γ * A))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((R + 2) ^ (-|γ * αinf|)) := by
    apply mul_le_mul'
    · exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    · exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  exact (mul_le_mul' hc le_rfl).trans
    (retained_coulomb_mass_ge_exterior_ball μ γ α z αinf O R hR hz hO)

end DOZZ.Proofs
