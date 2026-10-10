/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.DualL
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.ShiftEquations.Reflection.RbarContinuity

/-!
# The dual shift of `R` at one point

From the product identity `2 R(ε) R(Q + θ) = λ ρ (-4)` (`dualShift_product`) and the inversion
`R(Q + θ) R(Q - θ) = 1`, the `l`-identities `l(x) l(1 - x) = 1` and `l(x) l(-x) = -1/x²` give the
dual shift `R(ε) = -c_γ R(ε + 2/γ)/(l(-4/γ²) l(2ε/γ) l(2 + 4/γ² - 2ε/γ))` at `ε = γ/2 - θ`, with
`c_γ = (γ²/4) μπ R(γ)` ([KRV, §10.5], last display).
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- `l(x) l(1 - x) = 1` off the integers. -/
theorem lFun_mul_lFun_one_sub_eq_one {x : ℂ} (h₁ : Complex.Gamma x ≠ 0)
    (h₂ : Complex.Gamma (1 - x) ≠ 0) : lFun x * lFun (1 - x) = 1 := by
  unfold lFun
  rw [show (1 : ℂ) - (1 - x) = x by ring]
  field_simp

/-- `4/γ²` is not an integer when `γ²` is irrational. -/
theorem four_div_sq_ne_nat {γ : ℝ} (hγ : 0 < γ) (hγirr : Irrational (γ ^ 2)) (n : ℕ) :
    (-4 / (γ : ℂ) ^ 2) ≠ -(n : ℂ) := by
  intro hn
  have hr : ((4 / γ ^ 2 : ℝ) : ℂ) = (n : ℂ) := by
    push_cast
    linear_combination -hn
  have hr' : 4 / γ ^ 2 = (n : ℝ) := by exact_mod_cast hr
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by
    rw [← hr']
    positivity
  apply hγirr
  refine ⟨4 / n, ?_⟩
  push_cast
  field_simp at hr' ⊢
  linarith

/-- **The dual shift of `R` at `ε = γ/2 - θ`** from the product identity and the inversion. -/
theorem dualShift_of_product {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2))
    {R : ℂ → ℂ} {θ : ℝ} (hθ₁ : 0 < θ) (hθ₂ : θ < γ / 4)
    (hprod : R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ) * 2 =
      (-(1 / (γ : ℂ)) * lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) * lFun (1 + 4 / (γ : ℂ) ^ 2) *
        (lFun (1 - 2 * θ / γ))⁻¹) *
      (2 * (μ * Real.pi : ℂ) * R γ /
        ((γ : ℂ) * (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4)))) * (-4))
    (hinv : R ((Q γ + θ : ℝ) : ℂ) * R ((Q γ - θ : ℝ) : ℂ) = 1)
    (hg₁ : ∀ n : ℕ, dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ) ≠ -(n : ℂ)) :
    R ((γ / 2 - θ : ℝ) : ℂ) =
      -((γ : ℂ) ^ 2 / 4 * (μ * Real.pi : ℂ) * R γ) * R (((γ / 2 - θ : ℝ) : ℂ) + 2 / γ) /
        (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * ((γ / 2 - θ : ℝ) : ℂ) / γ) *
          lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * ((γ / 2 - θ : ℝ) : ℂ) / γ)) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  set ε : ℂ := ((γ / 2 - θ : ℝ) : ℂ) with hε
  -- the shifted point
  have hshift : ε + 2 / γ = ((Q γ - θ : ℝ) : ℂ) := by
    rw [hε, hQ]
    push_cast
    ring
  -- `l(-4/γ²) l(1 + 4/γ²) = 1`
  set X : ℂ := lFun (-4 / (γ : ℂ) ^ 2) with hX
  have hXA : X * lFun (1 + 4 / (γ : ℂ) ^ 2) = 1 := by
    have h := lFun_mul_lFun_one_sub_eq_one (x := -4 / (γ : ℂ) ^ 2)
      (Complex.Gamma_ne_zero (four_div_sq_ne_nat hγ hγirr))
      (by
        rw [show (1 : ℂ) - -4 / (γ : ℂ) ^ 2 = ((1 + 4 / γ ^ 2 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.Gamma_ne_zero (fun n => by
          have := (analyticAt_Gamma_ofReal_pos (show (0 : ℝ) < 1 + 4 / γ ^ 2 by positivity))
          intro hn
          have hr : (1 + 4 / γ ^ 2 : ℝ) = -(n : ℝ) := by exact_mod_cast hn
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have : (0 : ℝ) < 1 + 4 / γ ^ 2 := by positivity
          linarith))
    rwa [show (1 : ℂ) - -4 / (γ : ℂ) ^ 2 = 1 + 4 / (γ : ℂ) ^ 2 by ring] at h
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hXA
  -- `l(2(ε - Q)/γ) l(2 + 4/γ² - 2ε/γ) = 1`
  set Y : ℂ := lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * ε / γ) with hY
  have hY1 : 1 - dualArg₁ γ ε = 2 + 4 / (γ : ℂ) ^ 2 - 2 * ε / γ := by
    unfold dualArg₁
    rw [hQ]
    push_cast
    field_simp
    ring
  have hl₁Y : lFun (dualArg₁ γ ε) * Y = 1 := by
    have hpos : (0 : ℝ) < 1 + 4 / γ ^ 2 + 2 * θ / γ := by positivity
    have h := lFun_mul_lFun_one_sub_eq_one (x := dualArg₁ γ ε) (Complex.Gamma_ne_zero hg₁)
      (by
        rw [hY1, show 2 + 4 / (γ : ℂ) ^ 2 - 2 * ε / γ = ((1 + 4 / γ ^ 2 + 2 * θ / γ : ℝ) : ℂ) by
          rw [hε]; push_cast; field_simp; ring]
        refine Complex.Gamma_ne_zero fun n hn => ?_
        have hr : (1 + 4 / γ ^ 2 + 2 * θ / γ : ℝ) = -(n : ℝ) := by exact_mod_cast hn
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    rwa [hY1] at h
  have hY0 : Y ≠ 0 := right_ne_zero_of_mul_eq_one hl₁Y
  -- `l(γ²/4) l(-γ²/4) = -16/γ⁴`
  have hPQ : lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4) = -16 / (γ : ℂ) ^ 4 := by
    have hq : ((γ : ℂ) ^ 2 / 4) ≠ 0 := div_ne_zero (pow_ne_zero 2 hγc) (by norm_num)
    have hΓ1 : Complex.Gamma ((γ : ℂ) ^ 2 / 4) ≠ 0 := by
      rw [show (γ : ℂ) ^ 2 / 4 = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring]
      refine Complex.Gamma_ne_zero fun n hn => ?_
      have hr : (γ ^ 2 / 4 : ℝ) = -(n : ℝ) := by exact_mod_cast hn
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : (0 : ℝ) < γ ^ 2 / 4 := by positivity
      linarith
    have hΓ2 : Complex.Gamma (-((γ : ℂ) ^ 2 / 4)) ≠ 0 := by
      rw [show -((γ : ℂ) ^ 2 / 4) = ((-(γ ^ 2 / 4) : ℝ) : ℂ) by push_cast; ring]
      exact Complex.Gamma_ne_zero (ofReal_ne_neg_nat_of_mem (Or.inl ⟨by nlinarith, by
        have : (0 : ℝ) < γ ^ 2 / 4 := by positivity
        linarith⟩))
    have h := lFun_mul_neg hq hΓ1 hΓ2
    rw [show -((γ : ℂ) ^ 2) / 4 = -((γ : ℂ) ^ 2 / 4) by ring, mul_comm, h]
    field_simp
    ring
  -- `l(1 - 2θ/γ) = l(2ε/γ) ≠ 0`
  have hB : lFun (1 - 2 * θ / γ) = lFun (2 * ε / γ) := by
    congr 1
    rw [hε]
    push_cast
    field_simp
  have hB0 : lFun (2 * ε / γ) ≠ 0 := by
    rw [← hB, show (1 : ℂ) - 2 * θ / γ = ((1 - 2 * θ / γ : ℝ) : ℂ) by push_cast; ring]
    have hθγ : 2 * θ / γ < 1 / 2 := by
      rw [div_lt_iff₀ hγ]
      linarith
    have hθγ' : 0 < 2 * θ / γ := by positivity
    refine lFun_ne_zero (ofReal_ne_neg_nat_of_mem (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
      ?_
    rw [show (1 : ℂ) - ((1 - 2 * θ / γ : ℝ) : ℂ) = ((2 * θ / γ : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_neg_nat_of_mem (Or.inr (Or.inl ⟨hθγ', by linarith⟩))
  -- assemble
  have hR : R ε = R ε * R ((Q γ + θ : ℝ) : ℂ) * R ((Q γ - θ : ℝ) : ℂ) := by
    rw [mul_assoc, hinv, mul_one]
  rw [hR, show R ε * R ((Q γ + θ : ℝ) : ℂ) = (R ε * R ((Q γ + θ : ℝ) : ℂ) * 2) / 2 by ring, hprod,
    hshift, ← hB]
  have hA : lFun (1 + 4 / (γ : ℂ) ^ 2) = X⁻¹ := eq_inv_of_mul_eq_one_right hXA
  have hl₁ : lFun (dualArg₁ γ ε) = Y⁻¹ := eq_inv_of_mul_eq_one_left hl₁Y
  rw [hA, hl₁, hPQ, hB]
  field_simp
  ring

end DOZZ.Proofs

end
