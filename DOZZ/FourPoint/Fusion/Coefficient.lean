/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootedCoefficient
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.FourPoint.Fusion.RootedMass
import DOZZ.GMC.Moments.RhoCoulomb
import DOZZ.GMC.Moments.RhoMoment
public import DOZZ.FourPoint.Fusion.Parameters

/-! # Normalization of the rooted fusion coefficient -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The coefficient in the one-rooted formula is the shifted rho moment. -/
theorem fusion_rootedCoefficient_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ p : ℝ) :
    gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p =
      (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
        (∫⁻ ω, rho γ (M ω) (α₁ + γ / 2) α₂ α₃ ^ (-p - 1) ∂P).toReal := by
  unfold gammaHalfRootedCoefficient
  congr 2
  apply lintegral_congr_ae
  filter_upwards [fusion_gammaHalfRootedMass_eq_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃,
    gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM (α₁ + γ / 2) α₂ α₃]
    with ω hroot hrho
  rw [hroot, hrho]
  rfl

/-- The shifted Seiberg exponent increases by one. -/
theorem fusion_shifted_seiberg_exponent (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) :
    sExp γ (α₁ + γ / 2) α₂ α₃ =
      (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1 := by
  unfold sExp
  field_simp
  ring

/-- Gamma recurrence converts the rooted Taylor coefficient to the KRV coefficient. -/
theorem fusion_shifted_normalization (γ μ p A E : ℝ) (hμ : 0 < μ) (hp : p ≠ 0) :
    (2 * μ ^ (-p) / γ * Real.Gamma p) * (-p * (A * E)) =
      (-μ * A) * (2 * μ ^ (-(p + 1)) / γ * Real.Gamma (p + 1) * E) := by
  rw [Real.Gamma_add_one hp]
  have hm : μ * μ ^ (-(p + 1)) = μ ^ (-p) := by
    conv_lhs => lhs; rw [← Real.rpow_one μ]
    rw [← Real.rpow_add hμ]
    congr 1
    ring
  calc
    _ = -A * (2 / γ * Real.Gamma p * p * E) * μ ^ (-p) := by ring
    _ = -A * (2 / γ * Real.Gamma p * p * E) * (μ * μ ^ (-(p + 1))) := by rw [hm]
    _ = _ := by ring


/-- The normalization in the four-point moment gives exactly the shifted structure constant. -/
theorem fusion_normalized_rootedCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (μ α₁ α₂ α₃ : ℝ) (hμ : 0 < μ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
    (2 * μ ^ (-p) / γ * Real.Gamma p) *
        (-p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p) =
      (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
        structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ := by
  dsimp only
  rw [fusion_rootedCoefficient_moment P X hX γ hγ hγ2 M hM]
  unfold structureConstant
  rw [fusion_shifted_seiberg_exponent γ α₁ α₂ α₃ hγ.ne']
  have hp : (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ ≠ 0 :=
    (div_pos (by linarith) hγ).ne'
  have he : -((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1) =
      -(α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ - 1 := by ring
  simpa only [he, neg_div] using
    fusion_shifted_normalization γ μ
      ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ)
      (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re
      (∫⁻ ω, rho γ (M ω) (α₁ + γ / 2) α₂ α₃ ^
        (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) - 1) ∂P).toReal hμ hp

end DOZZ.Proofs
