/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.AffineMoment

/-! Affine covariance with the nonzero charge at infinity used in the residue chart of the
three-to-two residue bridge. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Total zero-mode exponent, including the charge at infinity. -/
noncomputable def residueTotalSExp {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (αinf : ℝ) : ℝ :=
  ((∑ k, α k) + αinf - 2 * Q γ) / γ

/-- The charge at infinity contributes with the opposite sign to the affine scale factor. -/
theorem residue_coulombWeight_affine {N : ℕ} (γ : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (αinf : ℝ) (a b : ℂ) (ha : a ≠ 0) {y : ℂ}
    (hyz : ∀ k, y ≠ z k) :
    coulombWeight γ α (fun k => a * z k + b) αinf (a * y + b) =
      ENNReal.ofReal (Real.exp (γ * ((∑ k, α k) + αinf) * affineDefect a b y -
        γ * ((∑ k, α k) - αinf) * Real.log ‖a‖ / 2)) *
        coulombWeight γ α z αinf y := by
  have hy := normPlus_pos' y
  have hψ := normPlus_pos' (a * y + b)
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hinf : ENNReal.rpow (ENNReal.ofReal (normPlus (a * y + b))) (γ * αinf) =
      ENNReal.ofReal (Real.exp (γ * αinf * (affineDefect a b y + Real.log ‖a‖ / 2))) *
        ENNReal.rpow (ENNReal.ofReal (normPlus y)) (γ * αinf) := by
    rw [ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow,
      ENNReal.ofReal_rpow_of_pos hψ, ENNReal.ofReal_rpow_of_pos hy,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      Real.rpow_def_of_pos hψ, Real.rpow_def_of_pos hy, ← Real.exp_add]
    congr 2
    unfold affineDefect
    ring
  have hsplit (zs : Fin N → ℂ) (x : ℂ) : coulombWeight γ α zs αinf x =
      coulombWeight γ α zs 0 x * ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) := by
    unfold coulombWeight
    simp only [mul_zero, ENNReal.rpow_eq_pow, ENNReal.rpow_zero, mul_one]
  rw [hsplit, coulombWeight_affine γ α z a b ha hyz, hinf, hsplit]
  calc _ = (ENNReal.ofReal (Real.exp (γ * (∑ k, α k) *
          (affineDefect a b y - Real.log ‖a‖ / 2))) *
        ENNReal.ofReal (Real.exp (γ * αinf * (affineDefect a b y + Real.log ‖a‖ / 2)))) *
        (coulombWeight γ α z 0 y * ENNReal.rpow (ENNReal.ofReal (normPlus y)) (γ * αinf)) := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring

/-- Coulomb integration against the repinned chaos also allows a charge at infinity. -/
theorem residue_lintegral_coulombWeight_repinChaos {Ω : Type*} (M : Ω → Measure ℂ)
    (L : Ω → ℝ) (a b : ℂ) (ha : a ≠ 0) (γ V : ℝ) (ω : Ω)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    ∫⁻ x, coulombWeight γ α z αinf x ∂repinChaos M L a b γ V ω =
      ENNReal.ofReal (Real.exp (-γ * L ω - γ ^ 2 / 2 * V)) *
        ∫⁻ x, coulombWeight γ α z αinf (affineInv a b x) *
          ENNReal.ofReal (Real.exp (γ ^ 2 * repinPotential a b x) * repinWeight a b x) ∂M ω := by
  have hc := continuous_repinPotential a b ha
  have hw := continuous_repinWeight a b ha
  unfold repinChaos
  have hcw : Measurable fun x => coulombWeight γ α z αinf (affineInv a b x) :=
    (measurable_coulombWeight γ α z αinf).comp (continuous_affineInv a b).measurable
  have hD : Measurable fun x => ENNReal.ofReal (Real.exp (γ ^ 2 * repinPotential a b x) *
      repinWeight a b x) := ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_map (measurable_coulombWeight γ α z αinf) (continuous_affineInv a b).measurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hcw,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [Real.exp_add, mul_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- The Cameron--Martin reweighting constant includes the infinity charge. -/
theorem residue_coulombWeight_repin_identity {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) (a b : ℂ) (ha : a ≠ 0)
    {x : ℂ} (hx : ∀ k, x ≠ a * z k + b) :
    coulombWeight γ α z αinf (affineInv a b x) *
        ENNReal.ofReal (Real.exp (γ ^ 2 * (1 + residueTotalSExp γ α αinf) *
          repinPotential a b x) * repinWeight a b x) =
      ENNReal.ofReal (‖a‖ ^ (γ * ((∑ k, α k) - αinf) / 2) *
        Real.exp (γ ^ 2 * (1 + residueTotalSExp γ α αinf) * repinKappa a b)) *
        coulombWeight γ α (fun k => a * z k + b) αinf x := by
  set y := affineInv a b x with hydef
  have hxy : x = a * y + b := (affine_affineInv a b ha x).symm
  have hyz : ∀ k, y ≠ z k := fun k h => hx k (by rw [hxy, h])
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hexp : γ ^ 2 * (1 + residueTotalSExp γ α αinf) + 4 =
      γ * ((∑ k, α k) + αinf) := by
    unfold residueTotalSExp Q
    field_simp [hγ.ne']
    ring
  rw [hxy, residue_coulombWeight_affine γ α z αinf a b ha hyz,
    repinPotential_affine a b ha y, repinWeight_affine a b ha y,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_comm (ENNReal.ofReal _) (coulombWeight _ _ _ _ _)]
  congr 2
  rw [Real.rpow_def_of_pos hapos, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination (affineDefect a b y) * hexp

end DOZZ.Proofs
