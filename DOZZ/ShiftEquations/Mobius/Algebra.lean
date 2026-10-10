/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.MobiusMap
public import DOZZ.Statements.Correlations.NPointCoulombPrefactor
public import DOZZ.Statements.Correlations.NPointSExp
public import DOZZ.Statements.Defs.ConformalWeight
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Möbius chart algebra

Elementary algebra of the finite Möbius charts `z ↦ (a z + b) / (c z + d)` used to move the
Coulomb prefactor and the conformal weights of an `N`-point configuration through a chart. A chart
has complex derivative `(a d - b c) / (c z + d)²`, and its chord identity
`|ψ z - ψ w|² = |ψ' z| |ψ' w| |z - w|²` off the pole feeds the transformation rule of the Coulomb
prefactor under pairwise distance scalings `√(j i j k)`. The weights `j i ^ (-(α i (∑ α - α i))/2)`
produced by that rule combine with the zero-mode exponent into the real part of the conformal
weight. A chart with `c = 0` is affine and a chart with `c ≠ 0` is an affine map of an inversion
of an affine map, off its pole.
-/

public section

open scoped BigOperators

namespace DOZZ.Proofs

/-- The difference of two chart values is the determinant times `z - w`, over the product of the
two denominators. -/
theorem mobiusMap_sub (ψ : MobiusChart) {z w : ℂ} (hz : ψ.c * z + ψ.d ≠ 0)
    (hw : ψ.c * w + ψ.d ≠ 0) :
    mobiusMap ψ z - mobiusMap ψ w =
      (ψ.a * ψ.d - ψ.b * ψ.c) * (z - w) / ((ψ.c * z + ψ.d) * (ψ.c * w + ψ.d)) := by
  unfold mobiusMap
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- Complex derivative of a chart off its pole. -/
theorem hasDerivAt_mobiusMap (ψ : MobiusChart) {z : ℂ} (hz : ψ.c * z + ψ.d ≠ 0) :
    HasDerivAt (mobiusMap ψ) ((ψ.a * ψ.d - ψ.b * ψ.c) / (ψ.c * z + ψ.d) ^ 2) z := by
  have h1 : HasDerivAt (fun z : ℂ => ψ.a * z + ψ.b) ψ.a z := by
    simpa using ((hasDerivAt_id z).const_mul ψ.a).add_const ψ.b
  have h2 : HasDerivAt (fun z : ℂ => ψ.c * z + ψ.d) ψ.c z := by
    simpa using ((hasDerivAt_id z).const_mul ψ.c).add_const ψ.d
  refine (h1.div h2 hz).congr_deriv ?_
  field_simp
  ring

/-- The modulus of the derivative of a chart off its pole. -/
theorem norm_deriv_mobiusMap (ψ : MobiusChart) {z : ℂ} (hz : ψ.c * z + ψ.d ≠ 0) :
    ‖deriv (mobiusMap ψ) z‖ = ‖ψ.a * ψ.d - ψ.b * ψ.c‖ / ‖ψ.c * z + ψ.d‖ ^ 2 := by
  rw [(hasDerivAt_mobiusMap ψ hz).deriv, norm_div, norm_pow]

/-- A chart has nonvanishing derivative off its pole. -/
theorem norm_deriv_mobiusMap_pos (ψ : MobiusChart) {z : ℂ} (hz : ψ.c * z + ψ.d ≠ 0) :
    0 < ‖deriv (mobiusMap ψ) z‖ := by
  rw [norm_deriv_mobiusMap ψ hz]
  exact div_pos (norm_pos_iff.mpr ψ.determinant_ne) (pow_pos (norm_pos_iff.mpr hz) 2)

/-- The chord identity of a chart: squared chord length is the product of the derivative moduli
times the squared source chord length. -/
theorem norm_mobiusMap_sub_sq (ψ : MobiusChart) {z w : ℂ} (hz : ψ.c * z + ψ.d ≠ 0)
    (hw : ψ.c * w + ψ.d ≠ 0) :
    ‖mobiusMap ψ z - mobiusMap ψ w‖ ^ 2 =
      ‖deriv (mobiusMap ψ) z‖ * ‖deriv (mobiusMap ψ) w‖ * ‖z - w‖ ^ 2 := by
  have hz' : ‖ψ.c * z + ψ.d‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hw' : ‖ψ.c * w + ψ.d‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [mobiusMap_sub ψ hz hw, norm_deriv_mobiusMap ψ hz,
    norm_deriv_mobiusMap ψ hw, norm_div, norm_mul, norm_mul]
  field_simp

/-- With `c = 0`, the denominator `d` is nonzero. -/
theorem mobiusChart_d_ne_zero_of_c_eq_zero (ψ : MobiusChart) (hc : ψ.c = 0) : ψ.d ≠ 0 := by
  have h := ψ.determinant_ne
  rw [hc, mul_zero, sub_zero] at h
  exact (mul_ne_zero_iff.mp h).2

/-- With `c = 0`, the leading coefficient `a` is nonzero. -/
theorem mobiusChart_a_ne_zero_of_c_eq_zero (ψ : MobiusChart) (hc : ψ.c = 0) : ψ.a ≠ 0 := by
  have h := ψ.determinant_ne
  rw [hc, mul_zero, sub_zero] at h
  exact (mul_ne_zero_iff.mp h).1

/-- A chart with `c = 0` is affine. -/
theorem mobiusMap_of_c_eq_zero (ψ : MobiusChart) (hc : ψ.c = 0) (z : ℂ) :
    mobiusMap ψ z = ψ.a / ψ.d * z + ψ.b / ψ.d := by
  have hd := mobiusChart_d_ne_zero_of_c_eq_zero ψ hc
  unfold mobiusMap
  rw [hc, zero_mul, zero_add]
  field_simp

/-- A chart with `c ≠ 0` is an affine map of an inversion of an affine map, off its pole. -/
theorem mobiusMap_of_c_ne_zero (ψ : MobiusChart) (hc : ψ.c ≠ 0) {z : ℂ}
    (hz : ψ.c * z + ψ.d ≠ 0) :
    mobiusMap ψ z =
      -((ψ.a * ψ.d - ψ.b * ψ.c) / ψ.c) * (ψ.c * z + ψ.d)⁻¹ + ψ.a / ψ.c := by
  have h : ψ.a * z + ψ.b = -((ψ.a * ψ.d - ψ.b * ψ.c) / ψ.c) + ψ.a / ψ.c * (ψ.c * z + ψ.d) := by
    field_simp
    ring
  unfold mobiusMap
  rw [h, div_eq_mul_inv, add_mul, mul_assoc, mul_inv_cancel₀ hz, mul_one]

/-- Scaling of a real power: if `y² = p q x²` with `x, y ≥ 0` and `p, q > 0`, then
`y ^ s = p ^ (s / 2) * q ^ (s / 2) * x ^ s`. -/
theorem mobiusPrefactor_rpow_scale {x y p q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 < p)
    (hq : 0 < q) (h : y ^ 2 = p * q * x ^ 2) (s : ℝ) :
    y ^ s = p ^ (s / 2) * q ^ (s / 2) * x ^ s := by
  have hy' : y = Real.sqrt (p * q) * x := by
    rw [← Real.sqrt_sq hy, h, Real.sqrt_mul (mul_pos hp hq).le, Real.sqrt_sq hx]
  have he : (1 / (2 : ℝ)) * s = s / 2 := by ring
  have hsq : Real.sqrt (p * q) ^ s = p ^ (s / 2) * q ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_pos hp hq).le, Real.mul_rpow hp.le hq.le, he]
  rw [hy', Real.mul_rpow (Real.sqrt_nonneg _) hx, hsq]

/-- The exponents carried by the point `i` in the Coulomb prefactor, collected over the pairs
`i < k` and `k < i`, add up to `-(α i * (∑ α - α i)) / 2`. -/
theorem mobiusPrefactor_exponent_sum {N : ℕ} (α : Fin N → ℝ) (i : Fin N) :
    (∑ k, if i < k then -(α i * α k) / 2 else 0) +
        (∑ k, if k < i then -(α k * α i) / 2 else 0) =
      -(α i * ((∑ k, α k) - α i)) / 2 := by
  have h : ∀ k : Fin N, ((if i < k then -(α i * α k) / 2 else 0) +
      (if k < i then -(α k * α i) / 2 else 0)) =
        -(α i * α k) / 2 - (if k = i then -(α i * α i) / 2 else 0) := by
    intro k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne', not_lt_of_gt hik]
    · subst hik
      simp
    · simp [hik, hik.ne, not_lt_of_gt hik, mul_comm]
  have hs : ∑ k, -(α i * α k) / 2 = -(α i * ∑ k, α k) / 2 := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => h k), Finset.sum_sub_distrib, hs]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The `j`-factors of the rescaled Coulomb prefactor, over ordered pairs `i < k`, multiply to
`∏ i, j i ^ (-(α i * (∑ α - α i)) / 2)`. -/
theorem mobiusPrefactor_weight_prod {N : ℕ} (α j : Fin N → ℝ) (hj : ∀ i, 0 < j i) :
    (∏ i : Fin N, ∏ k : Fin N,
        if i < k then j i ^ (-(α i * α k) / 2) * j k ^ (-(α i * α k) / 2) else 1) =
      ∏ i : Fin N, j i ^ (-(α i * ((∑ k, α k) - α i)) / 2) := by
  have hsplit : ∀ i k : Fin N,
      (if i < k then j i ^ (-(α i * α k) / 2) * j k ^ (-(α i * α k) / 2) else 1) =
        j i ^ (if i < k then -(α i * α k) / 2 else 0) *
          j k ^ (if i < k then -(α i * α k) / 2 else 0) := by
    intro i k
    by_cases h : i < k <;> simp [h]
  simp only [hsplit, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i k => j k ^ (if i < k then -(α i * α k) / 2 else 0))]
  have h1 : ∀ i : Fin N, (∏ k : Fin N, j i ^ (if i < k then -(α i * α k) / 2 else 0)) =
      j i ^ (∑ k : Fin N, if i < k then -(α i * α k) / 2 else 0) := fun i =>
    (Real.rpow_sum_of_pos (hj i) _ _).symm
  have h2 : ∀ i : Fin N, (∏ k : Fin N, j i ^ (if k < i then -(α k * α i) / 2 else 0)) =
      j i ^ (∑ k : Fin N, if k < i then -(α k * α i) / 2 else 0) := fun i =>
    (Real.rpow_sum_of_pos (hj i) _ _).symm
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_congr rfl (fun i _ => h2 i),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Real.rpow_add (hj i), mobiusPrefactor_exponent_sum]

/-- Transformation of the Coulomb prefactor when all pair distances scale by `√(j i j k)`. The
totalized real powers satisfy it without any distinctness of the points. -/
theorem nPointCoulombPrefactor_eq_of_dist {N : ℕ} (α : Fin N → ℝ) (z w : Fin N → ℂ)
    (j : Fin N → ℝ) (hj : ∀ i, 0 < j i)
    (hdist : ∀ i k, i ≠ k → ‖w i - w k‖ ^ 2 = j i * j k * ‖z i - z k‖ ^ 2) :
    nPointCoulombPrefactor α w =
      (∏ i, j i ^ (-(α i * ((∑ k, α k) - α i)) / 2)) * nPointCoulombPrefactor α z := by
  have hpair : ∀ i k : Fin N,
      (if i < k then Real.rpow ‖w i - w k‖ (-(α i * α k)) else 1) =
        (if i < k then j i ^ (-(α i * α k) / 2) * j k ^ (-(α i * α k) / 2) else 1) *
          (if i < k then Real.rpow ‖z i - z k‖ (-(α i * α k)) else 1) := by
    intro i k
    by_cases hik : i < k
    · simp only [hik, ite_true, Real.rpow_eq_pow]
      exact mobiusPrefactor_rpow_scale (norm_nonneg _) (norm_nonneg _) (hj i) (hj k)
        (hdist i k hik.ne) _
    · simp [hik]
  unfold nPointCoulombPrefactor
  simp only [hpair, Finset.prod_mul_distrib]
  rw [mobiusPrefactor_weight_prod α j hj]

/-- The weight exponents combine to the conformal weight. -/
theorem mobius_weight_exponent (γ : ℝ) (hγ : γ ≠ 0) {N : ℕ} (α : Fin N → ℝ) (i : Fin N) :
    -(α i * ((∑ k, α k) - α i)) / 2 + γ * α i * nPointSExp γ α / 2 =
      -2 * (conformalWeight γ (α i : ℂ)).re := by
  have hre : (conformalWeight γ (α i : ℂ)).re = α i / 2 * (Q γ - α i / 2) := by
    have h : conformalWeight γ (α i : ℂ) = ((α i / 2 * (Q γ - α i / 2) : ℝ) : ℂ) := by
      unfold conformalWeight
      push_cast
      ring
    rw [h, Complex.ofReal_re]
  rw [hre]
  unfold nPointSExp
  field_simp
  ring

end DOZZ.Proofs

end
