/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.ShiftEquations.Mobius.AffineMomentInf
import Mathlib.Tactic

/-! # Interchanging the zero and one channels

The affine GMC moment identity `coulombMass_affine_moment_inf`, including the charge at infinity,
implements the map z ↦ 1-z. All moments retain their totalized convention.
-/

public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Swapping the last two finite roots also swaps their charges. -/
theorem crossing_mass_swap_last (γ a b c : ℝ) (ν : Measure ℂ) (w : ℂ) :
    coulombMass γ ν ![-γ / 2, a, b] ![w, 1, 0] c =
      coulombMass γ ν ![-γ / 2, b, a] ![w, 0, 1] c := by
  unfold coulombMass
  apply lintegral_congr
  intro x
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one]
  rw [mul_comm (ENNReal.rpow _ (γ * a)) (ENNReal.rpow _ (γ * b))]

/-- The half-charge reduced four-point function is symmetric under exchange
of zero and one, throughout its whole carrier. -/
theorem gammaHalf_fourPoint_reflection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ a b c : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (z : ℂ) :
    fourPointT P M γ μ (-γ / 2) a b c z =
      fourPointT P M γ μ (-γ / 2) b a c (1 - z) := by
  have he : infSExp γ ![-γ / 2, a, b] c = fourPointSExp γ (-γ / 2) a b c := by
    unfold infSExp fourPointSExp
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    congr 1
    ring
  have hm := coulombMass_affine_moment_inf P X hX γ hγ hγ2 M hM
    ![-γ / 2, a, b] ![z, 0, 1] c (-1) 1 (by norm_num)
  have hz : (fun k : Fin 3 => (-1 : ℂ) * (![z, 0, 1] : Fin 3 → ℂ) k + 1) =
      ![1 - z, 1, 0] := by
    funext k
    fin_cases k
    · change (-1 : ℂ) * z + 1 = 1 - z
      ring
    · simp
    · simp
  rw [hz, he] at hm
  simp only [norm_neg, norm_one, Real.one_rpow, ENNReal.ofReal_one, one_mul] at hm
  simp_rw [crossing_mass_swap_last] at hm
  have hs : fourPointSExp γ (-γ / 2) b a c = fourPointSExp γ (-γ / 2) a b c := by
    unfold fourPointSExp
    congr 1
    ring
  unfold fourPointT
  rw [hs]
  congr 2
  simpa only [ENNReal.rpow_eq_pow] using hm.symm

end DOZZ.Proofs
