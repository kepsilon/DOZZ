/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.DualFirstCase.Coefficients
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Brownian.Reflection.RtheorAnalytic
import Mathlib.Tactic
/-! # Cancellation of the two dual crossing coefficients -/
@[expose] public section
open Complex Filter Topology Set
namespace DOZZ.Proofs
/-- The algebraic cancellation retains the literal centered shift coefficient. -/
theorem dualFirstCase_coefficient_product (γ : ℝ) (a₂ a₃ z : ℂ) (hγ : γ ≠ 0)
    (hA : lFun (dualFirstCase_A γ a₂ a₃ z) ≠ 0)
    (hB : lFun (dualFirstCase_B γ a₂ a₃ z) ≠ 0)
    (hc : lFun (dualFirstCase_C γ z) ≠ 0)
    (hd : lFun (dualFirstCase_C γ a₂ - 1) ≠ 0)
    (hD : lFun ((2 / γ : ℂ) / 2 * (z - a₂ + a₃ - 2 / γ)) ≠ 0)
    (hE : lFun ((2 / γ : ℂ) / 2 * (-z + a₂ + a₃ - 2 / γ)) ≠ 0) :
    dualFirstCase_crossingProduct γ a₂ a₃ z * shiftCoeffA γ (2 / γ) z a₂ a₃ =
      lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * z / γ) *
        lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * z / γ) := by
  have hg : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  let χ : ℂ := 2 / γ
  let D := χ / 2 * (z - a₂ + a₃ - χ)
  let E := χ / 2 * (-z + a₂ + a₃ - χ)
  have hda : dualFirstCase_C γ a₂ - dualFirstCase_A γ a₂ a₃ z = 1 - D := by
    unfold dualFirstCase_C dualFirstCase_A D χ Q
    push_cast
    field_simp; ring
  have hdb : dualFirstCase_C γ a₂ - dualFirstCase_B γ a₂ a₃ z = E := by
    unfold dualFirstCase_C dualFirstCase_B E χ
    ring
  have hcoeff : shiftCoeffA γ χ z a₂ a₃ =
      lFun (-χ ^ 2) * lFun (χ * z) * lFun (dualFirstCase_C γ z) * lFun E /
        (lFun (dualFirstCase_A γ a₂ a₃ z) * lFun (dualFirstCase_B γ a₂ a₃ z) * lFun D) := by
    have hEarg : χ / 2 * ((z + a₂ + a₃) - 2 * z - χ) = E := by dsimp only [E]; ring
    have hBarg : χ / 2 * ((z + a₂ + a₃) - 2 * a₃ - χ) = dualFirstCase_B γ a₂ a₃ z := by
      dsimp only [dualFirstCase_B, χ]
      ring
    have hDarg : χ / 2 * ((z + a₂ + a₃) - 2 * a₂ - χ) = D := by dsimp only [D]; ring
    unfold shiftCoeffA
    rw [hEarg, hBarg, hDarg]
    rfl
  have hn : χ ^ 2 = ((4 / γ ^ 2 : ℝ) : ℂ) := by dsimp only [χ]; push_cast; field_simp; ring
  have hz : χ * z = 2 * z / γ := by dsimp only [χ]; ring
  have hC : 2 - dualFirstCase_C γ z = 2 + χ ^ 2 - χ * z := by unfold dualFirstCase_C χ; ring
  change dualFirstCase_crossingProduct γ a₂ a₃ z * shiftCoeffA γ χ z a₂ a₃ = _
  rw [hcoeff]
  unfold dualFirstCase_crossingProduct
  dsimp only
  rw [hda, hdb, dualFirstCase_lFun_one_sub, hC, ← hn, ← hz]
  change lFun D ≠ 0 at hD
  change lFun E ≠ 0 at hE
  field_simp [hA, hB, hc, hd, hD, hE]
/-- The dual seed and reflection/gluing equations give the centered shift without dividing
by the structure constant or by the reflection coefficient. -/
theorem dualFirstCase_scalar_shift (P A K D R B Cm Cp : ℂ) (hD : D ≠ 0) (hK : K ≠ 0)
    (hc : P * A = D) (hs : Cm = P * (-K * R / D) * B) (hg : Cp = R * B) :
    Cp = -(1 / K) * A * Cm := by
  have hm : D * Cm = -K * P * Cp := by
    rw [hg]
    field_simp [hD] at hs
    linear_combination hs
  apply mul_left_cancel₀ hD
  calc
    D * Cp = -(1 / K) * A * (-K * P * Cp) := by rw [← hc]; field_simp [hK]
    _ = -(1 / K) * A * (D * Cm) := by rw [hm]
    _ = D * (-(1 / K) * A * Cm) := by ring
/-- Every nonconstant affine l-factor is nonzero away from a locally finite set. -/
theorem dualFirstCase_affine_lFun (c d : ℂ) (hc : c ≠ 0) :
    ∀ᶠ z in codiscrete ℂ, lFun (c * z + d) ≠ 0 := eventually_affine_lFun_ne_zero hc
/-- The constant crossing factor is finite and nonzero for a near-Q charge. -/
theorem dualFirstCase_fixed_factor_ne_zero {γ a : ℝ} (hγ : 0 < γ)
    (hlo : Q γ - γ / 2 < a) (hhi : a < Q γ) :
    lFun (dualFirstCase_C γ (a : ℂ) - 1) ≠ 0 := by
  have hg : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have he : dualFirstCase_C γ (a : ℂ) - 1 = ((-(2 / γ) * (Q γ - a) : ℝ) : ℂ) := by
    unfold dualFirstCase_C Q
    push_cast
    field_simp; ring
  rw [he]
  apply lFun_ne_zero_of_forall_ne_int
  intro n hn
  have hn' : -(2 / γ) * (Q γ - a) = (n : ℝ) := Complex.ofReal_inj.mp (by simpa only [Complex.ofReal_intCast] using hn)
  have hlt : -(2 / γ) * (Q γ - a) < 0 := by
    have hpos := mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) hγ) (sub_pos.mpr hhi)
    linarith only [hpos]
  have hgt : -1 < -(2 / γ) * (Q γ - a) := by
    have ht : Q γ - a < γ / 2 := by linarith only [hlo]
    have hm := mul_lt_mul_of_pos_left ht (div_pos (by norm_num : (0 : ℝ) < 2) hγ)
    have hc : (2 / γ) * (γ / 2) = (1 : ℝ) := by field_simp
    rw [hc] at hm
    linarith only [hm]
  rw [hn'] at hlt hgt
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast hgt
  have hnhi : n < (0 : ℤ) := by exact_mod_cast hlt
  omega
/-- The coefficient cancellation is valid codiscretely on the whole plane. -/
theorem dualFirstCase_coefficient_product_codiscrete (γ : ℝ) (a₂ a₃ : ℂ) (hγ : γ ≠ 0)
    (hd : lFun (dualFirstCase_C γ a₂ - 1) ≠ 0) :
    ∀ᶠ z in codiscrete ℂ,
      dualFirstCase_crossingProduct γ a₂ a₃ z * shiftCoeffA γ (2 / γ) z a₂ a₃ =
        lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * z / γ) *
          lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * z / γ) := by
  have hg : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  let χ : ℂ := 2 / γ
  have hχ : χ ≠ 0 := div_ne_zero (by norm_num) hg
  have hχh : χ / 2 ≠ 0 := div_ne_zero hχ (by norm_num)
  have hA := dualFirstCase_affine_lFun (χ / 2) (χ / 2 * (a₂ + a₃ - χ - 2 * Q γ)) hχh
  have hB := dualFirstCase_affine_lFun (χ / 2) (χ / 2 * (a₂ - a₃ - χ)) hχh
  have hc := dualFirstCase_affine_lFun χ (-χ ^ 2) hχ
  have hD := dualFirstCase_affine_lFun (χ / 2) (χ / 2 * (-a₂ + a₃ - χ)) hχh
  have hE := dualFirstCase_affine_lFun (-(χ / 2)) (χ / 2 * (a₂ + a₃ - χ)) (neg_ne_zero.mpr hχh)
  filter_upwards [hA, hB, hc, hD, hE] with z hzA hzB hzc hzD hzE
  refine dualFirstCase_coefficient_product γ a₂ a₃ z hγ ?_ ?_ ?_ hd ?_ ?_
  · convert hzA using 1
    unfold dualFirstCase_A χ
    congr 1
    ring
  · convert hzB using 1
    unfold dualFirstCase_B χ
    congr 1
    ring
  · simpa only [dualFirstCase_C, χ, sub_eq_add_neg] using hzc
  · convert hzD using 1
    dsimp only [χ]
    congr 1
    ring
  · convert hzE using 1
    dsimp only [χ]
    congr 1
    ring
end DOZZ.Proofs
