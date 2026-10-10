/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergWeight

/-! # The real weight of the degenerate four-point mass

The reduced four-point function integrates the Coulomb weight with roots `z, 0, 1`,
charges `-χ, α₁, α₂` and charge `α₃` at infinity. Off its three finite roots this weight is the
real number `|x - z|^{γχ} |x|^{-γα₁} |x - 1|^{-γα₂} |x|₊^{γ(α₁+α₂+α₃-χ)}`. We record it
together with a softened version in which `|x - z|²` is replaced by `|x - z|² + ε²`; the
softened weight is smooth in `z` and is used to prove regularity of the four-point function. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The `z`-independent factor of the degenerate four-point weight. -/
noncomputable def bpzBaseWeight (γ χ α₁ α₂ α₃ : ℝ) (x : ℂ) : ℝ :=
  ‖x‖ ^ (-(γ * α₁)) * ‖x - 1‖ ^ (-(γ * α₂)) * normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ))

/-- The degenerate four-point weight with the degenerate root softened at scale `ε`. At
`ε = 0` it is the Coulomb weight off the finite roots. -/
noncomputable def bpzSoftWeight (γ χ α₁ α₂ α₃ ε : ℝ) (z x : ℂ) : ℝ :=
  (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) * bpzBaseWeight γ χ α₁ α₂ α₃ x

variable {γ χ α₁ α₂ α₃ : ℝ}

theorem bpz_normPlus_pos (x : ℂ) : 0 < normPlus x :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem bpz_one_le_normPlus (x : ℂ) : 1 ≤ normPlus x := le_max_left _ _

theorem bpz_measurable_normPlus : Measurable normPlus := by
  unfold normPlus
  exact measurable_const.max measurable_norm

theorem bpz_continuous_normPlus : Continuous normPlus := by
  unfold normPlus
  exact continuous_const.max continuous_norm

theorem bpzBaseWeight_nonneg (x : ℂ) : 0 ≤ bpzBaseWeight γ χ α₁ α₂ α₃ x := by
  unfold bpzBaseWeight
  have h1 := Real.rpow_nonneg (norm_nonneg x) (-(γ * α₁))
  have h2 := Real.rpow_nonneg (norm_nonneg (x - 1)) (-(γ * α₂))
  have h3 := Real.rpow_nonneg (bpz_normPlus_pos x).le (γ * (α₁ + α₂ + α₃ - χ))
  positivity

theorem bpzBaseWeight_pos {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    0 < bpzBaseWeight γ χ α₁ α₂ α₃ x := by
  unfold bpzBaseWeight
  have h1 := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) (-(γ * α₁))
  have h2 := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx1)) (-(γ * α₂))
  have h3 := Real.rpow_pos_of_pos (bpz_normPlus_pos x) (γ * (α₁ + α₂ + α₃ - χ))
  positivity

theorem bpz_soft_base_nonneg (ε : ℝ) (z x : ℂ) : 0 ≤ Complex.normSq (x - z) + ε ^ 2 :=
  add_nonneg (Complex.normSq_nonneg _) (sq_nonneg ε)

theorem bpzSoftWeight_nonneg (ε : ℝ) (z x : ℂ) : 0 ≤ bpzSoftWeight γ χ α₁ α₂ α₃ ε z x :=
  mul_nonneg (Real.rpow_nonneg (bpz_soft_base_nonneg ε z x) _) (bpzBaseWeight_nonneg x)


theorem measurable_bpzBaseWeight : Measurable (bpzBaseWeight γ χ α₁ α₂ α₃) := by
  unfold bpzBaseWeight
  refine ((measurable_norm.pow_const _).mul ?_).mul (bpz_measurable_normPlus.pow_const _)
  exact (measurable_id.sub_const 1).norm.pow_const _


theorem measurable_bpzSoftWeight (ε : ℝ) (z : ℂ) :
    Measurable (bpzSoftWeight γ χ α₁ α₂ α₃ ε z) := by
  unfold bpzSoftWeight
  refine Measurable.mul ?_ measurable_bpzBaseWeight
  refine Measurable.pow_const ?_ _
  exact (Complex.continuous_normSq.measurable.comp (measurable_id.sub_const z)).add
    measurable_const

/-- At `ε = 0` the softened factor is the power of the distance to the degenerate root. -/
theorem bpzSoftWeight_zero (z x : ℂ) :
    bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x =
      ‖x - z‖ ^ (γ * χ) * bpzBaseWeight γ χ α₁ α₂ α₃ x := by
  have h : (Complex.normSq (x - z) + (0 : ℝ) ^ 2) ^ (γ * χ / 2) = ‖x - z‖ ^ (γ * χ) := by
    have h2 : Complex.normSq (x - z) + (0 : ℝ) ^ 2 = ‖x - z‖ ^ ((2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, Complex.normSq_eq_norm_sq]
      ring
    rw [h2, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  unfold bpzSoftWeight
  rw [h]

private theorem bpz_div_rpow_eq (n d e : ℝ) (hn : 0 < n) (hd : 0 < d) :
    (n / d) ^ e = n ^ e * d ^ (-e) := by
  rw [Real.div_rpow hn.le hd.le, Real.rpow_neg hd.le, div_eq_mul_inv]

/-- The real identity behind the Coulomb weight off the finite roots. -/
theorem bpz_coulomb_real_identity (n d₀ d₁ d₂ : ℝ) (hn : 0 < n) (h₀ : 0 < d₀) (h₁ : 0 < d₁)
    (h₂ : 0 < d₂) :
    (n / d₀) ^ (γ * -χ) * ((n / d₁) ^ (γ * α₁) * (n / d₂) ^ (γ * α₂)) * n ^ (γ * α₃) =
      d₀ ^ (γ * χ) * (d₁ ^ (-(γ * α₁)) * d₂ ^ (-(γ * α₂)) *
        n ^ (γ * (α₁ + α₂ + α₃ - χ))) := by
  rw [bpz_div_rpow_eq n d₀ _ hn h₀, bpz_div_rpow_eq n d₁ _ hn h₁, bpz_div_rpow_eq n d₂ _ hn h₂]
  have hsum : γ * (α₁ + α₂ + α₃ - χ) = γ * -χ + (γ * α₁ + (γ * α₂ + γ * α₃)) := by ring
  rw [hsum, Real.rpow_add hn, Real.rpow_add hn, Real.rpow_add hn,
    show -(γ * -χ) = γ * χ by ring]
  ring

/-- Off the three finite roots the Coulomb weight is the real weight at `ε = 0`. -/
theorem coulombWeight_eq_ofReal_bpzSoftWeight {z x : ℂ} (hxz : x ≠ z) (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) :
    coulombWeight γ ![-χ, α₁, α₂] ![z, 0, 1] α₃ x =
      ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) := by
  have hn : 0 < normPlus x := bpz_normPlus_pos x
  have h₀ : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have h₁ : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h₂ : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  unfold coulombWeight
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, sub_zero]
  change ((ENNReal.ofReal (normPlus x / ‖x - z‖)) ^ (γ * -χ) *
      ((ENNReal.ofReal (normPlus x / ‖x‖)) ^ (γ * α₁) *
      (ENNReal.ofReal (normPlus x / ‖x - 1‖)) ^ (γ * α₂))) *
      (ENNReal.ofReal (normPlus x)) ^ (γ * α₃) = _
  rw [ENNReal.ofReal_rpow_of_pos (div_pos hn h₀), ENNReal.ofReal_rpow_of_pos (div_pos hn h₁),
    ENNReal.ofReal_rpow_of_pos (div_pos hn h₂), ENNReal.ofReal_rpow_of_pos hn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hn h₁).le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hn h₀).le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (div_pos hn h₀).le _)
      (mul_nonneg (Real.rpow_nonneg (div_pos hn h₁).le _)
        (Real.rpow_nonneg (div_pos hn h₂).le _)))]
  rw [bpzSoftWeight_zero, bpz_coulomb_real_identity _ _ _ _ hn h₀ h₁ h₂]
  rfl

/-- For a measure without atoms at the three finite roots, the Coulomb mass is the
integral of the real weight. -/
theorem coulombMass_eq_lintegral_bpzSoftWeight (μ : Measure ℂ) (z : ℂ) (hz : μ {z} = 0)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    coulombMass γ μ ![-χ, α₁, α₂] ![z, 0, 1] α₃ =
      ∫⁻ x, ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) ∂μ := by
  rw [coulombMass_eq_lintegral_coulombWeight]
  apply lintegral_congr_ae
  have hz' : ∀ᵐ x ∂μ, x ≠ z := by apply ae_iff.mpr; simpa using hz
  have h0' : ∀ᵐ x ∂μ, x ≠ 0 := by apply ae_iff.mpr; simpa using h0
  have h1' : ∀ᵐ x ∂μ, x ≠ 1 := by apply ae_iff.mpr; simpa using h1
  filter_upwards [hz', h0', h1'] with x hxz hx0 hx1
  exact coulombWeight_eq_ofReal_bpzSoftWeight hxz hx0 hx1

end DOZZ.Proofs
