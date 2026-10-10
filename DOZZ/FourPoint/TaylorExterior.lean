/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorMassInterpolation
public import DOZZ.FourPoint.TaylorFixedDisk

/-! The exterior part of the positive two-root Taylor square is uniformly bounded. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Restrict the absolute first-root mass to one spatial region. -/
noncomputable def gammaHalfRootMajorantOn {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) (B : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖) ∂M ω

/-- The source `I(B,z)` for an arbitrary Borel region. -/
noncomputable def gammaHalfTwoRootedMajorantOn {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) (B : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ ω, (gammaHalfRootMajorantOn M γ α₁ α₂ α₃ ω z B) ^ 2 *
    (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 2) ∂P

/-- Outside the half-unit disk the absolute numerator is at most four times the full mass. -/
theorem twoRooted_exterior_numerator_bound {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) (hz : ‖z‖ ≤ 1 / 4) :
    gammaHalfRootMajorantOn M γ α₁ α₂ α₃ ω z (Metric.ball 0 (1 / 2))ᶜ ≤
      ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω := by
  calc
    _ ≤ ∫⁻ x in (Metric.ball 0 (1 / 2))ᶜ,
        ENNReal.ofReal 4 * ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω := by
      apply setLIntegral_mono' measurableSet_ball.compl
      intro x hx
      have hxnorm : 1 / 2 ≤ ‖x‖ := by
        simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
      have hdist : 1 / 4 ≤ ‖x - z‖ := by
        have hh := norm_sub_norm_le x z
        linarith only [hxnorm, hz, hh]
      have hdistpos : 0 < ‖x - z‖ := lt_of_lt_of_le (by norm_num) hdist
      have hk := gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ hdistpos).mpr
      have hh := mul_le_mul_of_nonneg_left (show 1 ≤ 4 * ‖x - z‖ by linarith only [hdist]) hk
      nlinarith only [hh]
    _ ≤ ∫⁻ x, ENNReal.ofReal 4 * ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω :=
      setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Source exterior contribution is O(1), with a constant before z and no hidden full-mass
finiteness assumption. Zero and infinite masses are handled by the scalar interpolation lemma. -/
theorem twoRooted_exterior_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 / 4 →
      gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z (Metric.ball 0 (1 / 2))ᶜ ≤
        ENNReal.ofReal C := by
  obtain ⟨Cb, hCb, hbound⟩ := coulomb_inverse_moment_uniform_roots P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ p hp
  refine ⟨16 * Cb, by positivity, ?_⟩
  intro z hz
  have hpoint : ∀ᵐ ω ∂P,
      (gammaHalfRootMajorantOn M γ α₁ α₂ α₃ ω z (Metric.ball 0 (1 / 2))ᶜ) ^ 2 *
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 2) ≤
      ENNReal.ofReal 16 * (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p) := by
    filter_upwards [gammaHalfMass_eq_coulombMass_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ z]
      with ω hmass
    have hnum := twoRooted_exterior_numerator_bound M γ α₁ α₂ α₃ ω z hz
    rw [hmass] at hnum
    simpa only [show (4 : ℝ) ^ (2 : ℕ) = 16 by norm_num] using
      square_inverse_mass_bound _ _ 4 p (by norm_num) hp hnum
  have hy : ∀ i : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) i‖ ≤ 1 := by
    intro i
    fin_cases i
    · change ‖z‖ ≤ 1
      linarith only [hz]
    · change ‖(0 : ℂ)‖ ≤ 1
      norm_num
    · change ‖(1 : ℂ)‖ ≤ 1
      norm_num
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal 16 *
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p) ∂P :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal 16 * ∫⁻ ω,
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p) ∂P :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 16 * ENNReal.ofReal Cb := mul_le_mul' le_rfl (hbound ![z, 0, 1] hy)
    _ = _ := (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)).symm

end DOZZ.Proofs
