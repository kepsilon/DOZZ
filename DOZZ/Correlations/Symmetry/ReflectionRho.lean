/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionChaosMeasure
public import DOZZ.Correlations.Symmetry.ReflectionTiltInputs
public import DOZZ.Correlations.Symmetry.ReflectionWeight
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The reflected canonical mass before correlated Gaussian tilt removes its pinning weight. -/
noncomputable def symmetryCorrectedRho (γ a b c : ℝ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (γ ^ 2 * sExp γ a b c * symmetryReflectionPotential x) *
    (normPlus x ^ (γ * (b + a + c)) / (‖x‖ ^ (γ * b) * ‖x - 1‖ ^ (γ * a)))) ∂μ

theorem symmetryCorrectedRho_density_measurable (γ a b c : ℝ) :
    Measurable (fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ ^ 2 * sExp γ a b c * symmetryReflectionPotential x) *
        (normPlus x ^ (γ * (b + a + c)) / (‖x‖ ^ (γ * b) * ‖x - 1‖ ^ (γ * a))))) := by
  unfold symmetryReflectionPotential normPlus
  fun_prop

theorem symmetryCorrectedRho_measurable (γ a b c : ℝ) :
    Measurable (symmetryCorrectedRho γ a b c) :=
  Measure.measurable_lintegral (symmetryCorrectedRho_density_measurable γ a b c)

theorem symmetry_reflection_total_exponent (γ a b c : ℝ) (hγ : γ ≠ 0) :
    γ ^ 2 * sExp γ a b c + (γ ^ 2 + 4) = γ * (a + b + c) := by
  have h1 := symmetry_reflection_charge_exponent γ a b c hγ
  have h2 := symmetry_reflection_wick_exponent γ hγ
  linarith only [h1, h2]

/-- Finite positive exponential factors commute with every extended real power. -/
theorem symmetry_exp_mul_rpow (t p : ℝ) (A : ℝ≥0∞) :
    (ENNReal.ofReal (Real.exp t) * A) ^ p = ENNReal.ofReal (Real.exp (t * p)) * A ^ p := by
  rw [ENNReal.mul_rpow_eq_ite]
  have h0 : ENNReal.ofReal (Real.exp t) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  simp only [h0, ENNReal.ofReal_ne_top, false_and, false_or, ite_false]
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]

/-- The coupled corrected mass is the original canonical mass times the correlated scalar. -/
theorem symmetryCorrectedRho_repinned {Ω : Type*} (γ a b c : ℝ) (hγ : γ ≠ 0)
    (M : Ω → Measure ℂ) (L : Ω → ℝ) (ω : Ω) :
    symmetryCorrectedRho γ a b c (symmetryRepinnedChaos γ M L ω) =
      ENNReal.ofReal (Real.exp (-γ * L ω)) * rho γ (M ω) a b c := by
  unfold symmetryCorrectedRho symmetryRepinnedChaos
  rw [lintegral_smul_measure, smul_eq_mul]
  congr 1
  have hW : Measurable (fun x => ENNReal.ofReal (symmetryReflectionLimitWeight γ x)) :=
    ENNReal.measurable_ofReal.comp (symmetryReflectionLimitWeight γ).continuous.measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hW
    (symmetryCorrectedRho_density_measurable γ a b c)]
  have hF : Measurable (fun x : ℂ => ENNReal.ofReal (symmetryReflectionLimitWeight γ x) *
      ENNReal.ofReal (Real.exp (γ ^ 2 * sExp γ a b c * symmetryReflectionPotential x) *
        (normPlus x ^ (γ * (b + a + c)) / (‖x‖ ^ (γ * b) * ‖x - 1‖ ^ (γ * a))))) :=
    hW.mul (symmetryCorrectedRho_density_measurable γ a b c)
  simp only [Pi.mul_def]
  have hφ : Measurable (fun x : ℂ => 1 - x) := measurable_const.sub measurable_id
  rw [lintegral_map hF hφ]
  unfold rho
  apply lintegral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [symmetryReflectionLimitWeight_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [← mul_assoc, ← Real.exp_add]
    have he : (γ ^ 2 + 4) * symmetryReflectionPotential (1 - x) +
        γ ^ 2 * sExp γ a b c * symmetryReflectionPotential (1 - x) =
        γ * (a + b + c) * symmetryReflectionPotential (1 - x) := by
      rw [← add_mul, add_comm (γ ^ 2 + 4), symmetry_reflection_total_exponent γ a b c hγ]
    rw [he, ← rho_reflection_density γ a b c (1 - x)]
    rw [show (1 : ℂ) - (1 - x) = x from symmetryReflection_involutive x])

/-- Spatial Cameron--Martin cancellation leaves only the scalar normalization. -/
theorem symmetryCorrectedRho_tilt (γ a b c : ℝ) (μ : Measure ℂ) :
    symmetryCorrectedRho γ a b c
      (μ.withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * symmetryTiltPotential (-γ * sExp γ a b c) x)))) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * sExp γ a b c * symmetryReflectionKappa)) *
        rho γ μ b a c := by
  have hW : Measurable (fun x => ENNReal.ofReal
      (Real.exp (γ * symmetryTiltPotential (-γ * sExp γ a b c) x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((symmetryTiltPotential _).continuous.measurable.const_mul γ))
  unfold symmetryCorrectedRho rho
  rw [lintegral_withDensity_eq_lintegral_mul _ hW
    (symmetryCorrectedRho_density_measurable γ a b c), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [Pi.mul_def]
  apply lintegral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, symmetryTiltPotential_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring)
end DOZZ.Proofs
