/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorJensen
public import DOZZ.FourPoint.TaylorExterior

/-! Weighted Jensen reduces each annular positive Taylor square to a one-root expectation. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Nonnegative weighted Cauchy inequality with no normalization or mass finiteness assumption. -/
theorem weighted_jensen_square (μ : Measure ℂ) (k f : ℂ → ℝ≥0∞)
    (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ x, k x * f x ∂μ) ^ 2 ≤
      (∫⁻ x, k x * f x ^ 2 ∂μ) * ∫⁻ x, k x ∂μ := by
  have h := lintegral_square_le_mass (μ.withDensity k) f hf
  have hsq : Measurable (fun x : ℂ => f x ^ 2) := hf.pow_const 2
  rw [lintegral_withDensity_eq_lintegral_mul μ hk hf,
    lintegral_withDensity_eq_lintegral_mul μ hk hsq,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  exact h

/-- Measurability includes the prescribed values at all the finite roots. -/
theorem gammaHalfKernel_measurable (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    Measurable (gammaHalfKernel γ α₁ α₂ α₃ z) := by
  have hn : Measurable (normPlus : ℂ → ℝ) := measurable_const.max measurable_norm
  have hxz : Measurable (fun x : ℂ => ‖x - z‖) := (measurable_id.sub_const z).norm
  have hx1 : Measurable (fun x : ℂ => ‖x - 1‖) := (measurable_id.sub_const 1).norm
  exact ((hxz.pow_const _).mul (hn.pow_const _)).div
    ((measurable_norm.pow_const _).mul (hx1.pow_const _))

/-- The exact absolute numerator and its squared denominator satisfy weighted Jensen. -/
theorem gammaHalf_annular_jensen_bound (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (μ : Measure ℂ) (B : Set ℂ) :
    (∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖) ∂μ) ^ 2 ≤
      (∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ∂μ) *
        ∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
  let k : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)
  let f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖x - z‖⁻¹)
  have hk : Measurable k := ENNReal.measurable_ofReal.comp (gammaHalfKernel_measurable γ α₁ α₂ α₃ z)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp ((measurable_id.sub_const z).norm.inv)
  have hprod (x : ℂ) : k x * f x = ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖) := by
    rw [← ENNReal.ofReal_mul (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x)]
    congr 1
  have hprod₂ (x : ℂ) : k x * f x ^ 2 =
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) := by
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr (norm_nonneg _)),
      ← ENNReal.ofReal_mul (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x)]
    congr 1
    simp only [inv_pow, div_eq_mul_inv]
  have h := weighted_jensen_square (μ.restrict B) k f hk hf
  simp_rw [hprod, hprod₂] at h
  exact h

/-- Source Jensen reduction against the actual full Coulomb mass, for every spatial region. -/
theorem gammaHalf_region_jensen_reduction
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) (z : ℂ) (B : Set ℂ) :
    gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z B ≤
      ∫⁻ ω, (∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ∂M ω) *
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 1) ∂P := by
  apply lintegral_mono_ae
  filter_upwards [gammaHalfMass_eq_coulombMass_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ z]
    with ω hmass
  have hmassle : (∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω) ≤
      coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
    rw [← hmass]
    exact setLIntegral_le_lintegral _ _
  exact jensen_inverse_square_bound _ _ _ _ p hp
    (gammaHalf_annular_jensen_bound γ α₁ α₂ α₃ z (M ω) B) hmassle

end DOZZ.Proofs
