/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Infinity.WeightTransport
public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The conformal exponent cancels the Coulomb pairs and inverted-mass scale. -/
theorem infinity_exponent_cancel (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) :
    4 * (conformalWeight γ (α₃ : ℂ)).re - α₁ * α₃ - α₂ * α₃ +
      γ * α₃ * sExp γ α₁ α₂ α₃ = 0 := by
  have hre : (conformalWeight γ (α₃ : ℂ)).re = α₃ / 2 * (Q γ - α₃ / 2) := by
    have he : conformalWeight γ (α₃ : ℂ) = ((α₃ / 2 * (Q γ - α₃ / 2) : ℝ) : ℂ) := by
      unfold conformalWeight
      push_cast
      ring
    rw [he, Complex.ofReal_re]
  rw [hre, sExp]
  field_simp
  ring

/-- The full distance normalization is a single factor tending to one. -/
theorem infinity_prefactor_eq (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    ‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re) * ‖z‖ ^ (-(α₁ * α₃)) *
      ‖1 - z‖ ^ (-(α₂ * α₃)) * ‖z‖ ^ (γ * α₃ * sExp γ α₁ α₂ α₃) =
      ‖1 - z⁻¹‖ ^ (-(α₂ * α₃)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : ‖1 - z‖ = ‖z‖ * ‖1 - z⁻¹‖ := by
    rw [norm_sub_rev, show z - 1 = z * (1 - z⁻¹) by field_simp [hz], norm_mul]
  rw [hd, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  calc
    _ = ‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re - α₁ * α₃ - α₂ * α₃ +
        γ * α₃ * sExp γ α₁ α₂ α₃) * ‖1 - z⁻¹‖ ^ (-(α₂ * α₃)) := by
      have he : 4 * (conformalWeight γ (α₃ : ℂ)).re - α₁ * α₃ - α₂ * α₃ +
          γ * α₃ * sExp γ α₁ α₂ α₃ =
          ((4 * (conformalWeight γ (α₃ : ℂ)).re + -(α₁ * α₃)) + -(α₂ * α₃)) +
            γ * α₃ * sExp γ α₁ α₂ α₃ := by ring
      rw [he, Real.rpow_add hn, Real.rpow_add hn, Real.rpow_add hn]
      ring
    _ = _ := by rw [infinity_exponent_cancel γ α₁ α₂ α₃ hγ, Real.rpow_zero, one_mul]

/-- The ordinary finite correlation equals its normalized inverted-chart moment. -/
theorem infinity_normalized_correlation_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 ≤ μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (z : ℂ) (hz : z ≠ 0) :
    ‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re) *
        threePointFiniteCorrelation P M γ μ α₁ α₂ α₃ z =
      (2 / μ ^ (sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃)) *
        ‖1 - z⁻¹‖ ^ (-(α₂ * α₃)) *
          (∫⁻ ω, (coulombMass γ (M ω) ![α₃, α₂] ![z⁻¹, 1] α₁) ^
            (-sExp γ α₁ α₂ α₃) ∂P).toReal := by
  have ht := congrArg ENNReal.toReal (infinity_finite_moment_transport P X M γ α₁ α₂ α₃
    hγ hγ2 hX hM z hz (-sExp γ α₁ α₂ α₃))
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (norm_nonneg z)] at ht
  rw [show -(γ * α₃) * -sExp γ α₁ α₂ α₃ = γ * α₃ * sExp γ α₁ α₂ α₃ by ring] at ht
  unfold threePointFiniteCorrelation
  simp only [ENNReal.rpow_eq_pow, Real.rpow_eq_pow]
  rw [ht, Real.rpow_neg hμ]
  calc
    _ = (2 / μ ^ (sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃)) *
        (‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re) * ‖z‖ ^ (-(α₁ * α₃)) *
          ‖1 - z‖ ^ (-(α₂ * α₃)) * ‖z‖ ^ (γ * α₃ * sExp γ α₁ α₂ α₃)) *
            (∫⁻ ω, (coulombMass γ (M ω) ![α₃, α₂] ![z⁻¹, 1] α₁) ^
              (-sExp γ α₁ α₂ α₃) ∂P).toReal := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [infinity_prefactor_eq γ α₁ α₂ α₃ hγ.ne' z hz]

end DOZZ.Proofs
