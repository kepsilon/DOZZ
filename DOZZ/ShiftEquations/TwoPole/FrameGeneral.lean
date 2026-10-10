/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.Frame
public import DOZZ.Statements.Correlations.UnitVolumeNPointCorrelation
import DOZZ.GMC.Moments.RhoCoulomb

/-!
# The structure constant in a finite frame

For arbitrary charges the inversion–translation–inversion chain of `Frame` gives
`E[I_{(0,2,-2)}^{q}] = 2^{-γ(α₂+α₃) q} E[ρ(α₁, α₂, α₃)^{q}]` with `q = -s`, so the unit-volume
structure constant in the frame `(0, 1, ∞)` is an explicit positive multiple of the finite-position
unit-volume moment at `(0, 2, -2)`:
`C̄(α₁, α₂, α₃) = 2^{γ(α₂+α₃)(-s)} / C(α, z) · C̄_{(0,2,-2)}(α)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The general inversion constant `2^{-γ(α₂+α₃) q}`. -/
theorem frame_inversion_constant_gen (γ α₂ α₃ q : ℝ) :
    ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖(![2, -2] : Fin 2 → ℂ) k‖)
      (-(γ * (![α₂, α₃] : Fin 2 → ℝ) k))) q =
      ENNReal.ofReal (2 ^ (-(γ * (α₂ + α₃) * q))) := by
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_neg]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow,
    ← ENNReal.rpow_add _ _ (by simp) ENNReal.ofReal_ne_top, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_pos (by norm_num)]
  congr 2
  ring

theorem frame_infSExp_gen (γ α₁ α₂ α₃ : ℝ) :
    -infSExp γ (![α₂, α₃] : Fin 2 → ℝ) α₁ = -sExp γ α₁ α₂ α₃ := by
  unfold infSExp sExp
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The general frame identity** `E[I_{(0,2,-2)}^q] = 2^{-γ(α₂+α₃)q} E[ρ^q]`, `q = -s`. -/
theorem lintegral_coulombMass_frame_eq_rho {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α₁, α₂, α₃] ![0, 2, -2] 0)
        (-sExp γ α₁ α₂ α₃) ∂P =
      ENNReal.ofReal (2 ^ (-(γ * (α₂ + α₃) * (-sExp γ α₁ α₂ α₃)))) *
        ∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P := by
  have hz1 : ∀ k, (![2, -2] : Fin 2 → ℂ) k ≠ 0 := by
    intro k
    fin_cases k <;> norm_num
  have hz2 : ∀ k, (![1] : Fin 1 → ℂ) k ≠ 0 := by
    intro k
    fin_cases k
    norm_num
  -- step 1: inversion sends `α₁` to infinity; the zero-charge root drops
  have h1 := coulombMass_inv_moment_cons P X hX γ hγ hγ2 M hM α₁ 0 ![α₂, α₃] ![2, -2] hz1
    (-sExp γ α₁ α₂ α₃)
  rw [frame_inversion_constant_gen, frame_inverse_roots] at h1
  simp_rw [coulombMass_cons_zero] at h1
  -- step 2: translation by `1/2`
  have h2 := coulombMass_affine_moment_inf P X hX γ hγ hγ2 M hM ![α₂, α₃] ![1 / 2, -1 / 2] α₁ 1
    (1 / 2) one_ne_zero
  rw [frame_infSExp_gen, frame_translate_roots, norm_one, Real.one_rpow, ENNReal.ofReal_one,
    one_mul] at h2
  -- step 3: inversion sends `α₃` to infinity
  have h3 := coulombMass_inv_moment_cons P X hX γ hγ hγ2 M hM α₃ α₁ ![α₂] ![1] hz2
    (-sExp γ α₁ α₂ α₃)
  have hc3 : ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖(![1] : Fin 1 → ℂ) k‖)
      (-(γ * (![α₂] : Fin 1 → ℝ) k))) (-sExp γ α₁ α₂ α₃) = 1 := by
    simp
  have hinv3 : (fun k => ((![1] : Fin 1 → ℂ) k)⁻¹) = ![1] := by
    funext k
    fin_cases k
    norm_num
  rw [hc3, one_mul, hinv3] at h3
  have hswap : ∀ ω, coulombMass γ (M ω) ![α₂, α₃] ![1, 0] α₁ =
      coulombMass γ (M ω) (Fin.cons α₃ ![α₂] : Fin 2 → ℝ) (Fin.cons 0 ![1] : Fin 2 → ℂ) α₁ :=
    fun ω => coulombMass_swap γ (M ω) α₂ α₃ 1 0 α₁
  simp_rw [hswap] at h2
  -- step 4: the structure-constant mass
  have h4 : ∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P =
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons α₁ ![α₂] : Fin 2 → ℝ)
        (Fin.cons 0 ![1] : Fin 2 → ℂ) α₃) (-sExp γ α₁ α₂ α₃) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃] with ω hω
    rw [hω, ENNReal.rpow_eq_pow]
    rfl
  have h0 : (![α₁, α₂, α₃] : Fin 3 → ℝ) = Fin.cons α₁ ![α₂, α₃] := rfl
  have h0' : (![0, 2, -2] : Fin 3 → ℂ) = Fin.cons 0 ![2, -2] := rfl
  rw [h0, h0', h1, ← h2, h3, ← h4]

/-- **The structure constant through a finite frame.** -/
theorem unitVolumeStructureConstant_eq_nPoint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ =
      2 ^ (γ * (α₂ + α₃) * (-sExp γ α₁ α₂ α₃)) /
          nPointCoulombPrefactor ![α₁, α₂, α₃] ![0, 2, -2] *
        unitVolumeNPointCorrelation P M γ ![α₁, α₂, α₃] ![0, 2, -2] := by
  have hpref : 0 < nPointCoulombPrefactor ![α₁, α₂, α₃] ![0, 2, -2] := by
    unfold nPointCoulombPrefactor
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
    split_ifs with hij
    · refine Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) _
      fin_cases i <;> fin_cases j
      all_goals first | (simp_all; done) | (simp_all; norm_num)
    · exact one_pos
  have hs : nPointSExp γ ![α₁, α₂, α₃] = sExp γ α₁ α₂ α₃ := by
    unfold nPointSExp sExp
    rw [Fin.sum_univ_three]
    simp
  have hframe := lintegral_coulombMass_frame_eq_rho P X hX γ hγ hγ2 M hM α₁ α₂ α₃
  have hrho : ∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P =
      ENNReal.ofReal (2 ^ (γ * (α₂ + α₃) * (-sExp γ α₁ α₂ α₃))) *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α₁, α₂, α₃] ![0, 2, -2] 0)
          (-sExp γ α₁ α₂ α₃) ∂P := by
    rw [hframe, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos,
      add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  unfold unitVolumeStructureConstant unitVolumeNPointCorrelation
  rw [hs, hrho, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  field_simp

end DOZZ.Proofs

end
