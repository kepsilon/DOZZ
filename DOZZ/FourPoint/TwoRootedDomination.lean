/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfTwoRootedTerm
public import DOZZ.FourPoint.RootedPairIdentity

/-! Absolute majorants for the actual two-rooted Taylor observables. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The nonnegative absolute first-root mass from source `idefin`, with its absolute denominator. -/
noncomputable def gammaHalfRootMajorant {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖) ∂M ω

/-- The positive square expectation controlling all three Taylor contributions. -/
noncomputable def gammaHalfTwoRootedMajorant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ ω, (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 2) *
    (gammaHalfRootMajorant M γ α₁ α₂ α₃ ω z) ^ 2 ∂P

/-- The literal real kernel is nonnegative even at the prescribed singular-point values. -/
theorem gammaHalfKernel_nonneg (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) :
    0 ≤ gammaHalfKernel γ α₁ α₂ α₃ z x := by
  unfold gammaHalfKernel
  apply div_nonneg
  · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by unfold normPlus; positivity) _)
  · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _)

/-- The absolute root mass dominates the actual complex first-root integral. -/
theorem rootKernelZ_enorm_le {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) :
    ‖gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω z‖ₑ ≤
      gammaHalfRootMajorant M γ α₁ α₂ α₃ ω z := by
  refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x)]

/-- The same absolute mass dominates the conjugate-root integral. -/
theorem rootKernelBar_enorm_le {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) :
    ‖gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω z‖ₑ ≤
      gammaHalfRootMajorant M γ α₁ α₂ α₃ ω z := by
  refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, norm_div, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x)]

/-- Taking `toReal` of a negative mass power cannot increase its extended absolute coefficient. -/
theorem mass_coefficient_enorm_le (a : ℝ≥0∞) :
    ‖(a.toReal : ℂ)‖ₑ ≤ a := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/-- The square inner expectation is bounded by the nonnegative source expectation. -/
theorem twoRooted_square_expectation_enorm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) :
    ‖∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^
      (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω z ^ 2 ∂P‖ₑ ≤
      gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p z := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro ω
  dsimp only
  rw [enorm_mul, enorm_pow]
  apply mul_le_mul'
  · exact mass_coefficient_enorm_le _
  · exact pow_le_pow_left' (rootKernelZ_enorm_le M γ α₁ α₂ α₃ ω z) 2

/-- The mixed inner expectation has the same majorant, with two absolute denominators. -/
theorem twoRooted_mixed_expectation_enorm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) :
    ‖∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^
      (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω z *
        gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω z ∂P‖ₑ ≤
      gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p z := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro ω
  dsimp only
  rw [enorm_mul, enorm_mul, pow_two, mul_assoc]
  exact mul_le_mul' (mass_coefficient_enorm_le _)
    (mul_le_mul' (rootKernelZ_enorm_le M γ α₁ α₂ α₃ ω z)
      (rootKernelBar_enorm_le M γ α₁ α₂ α₃ ω z))

end DOZZ.Proofs
