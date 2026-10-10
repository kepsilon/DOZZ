/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.NegativePowerDifference

/-! Uniform real-power estimates for the square-root sum-tail sandwich. -/

@[expose] public section
namespace DOZZ.Proofs

/-- A half-scale change costs one uniform power of two, also for negative decay orders. -/
theorem sumtail_rpow_half_bound (T t x r : ℝ) (hT : 0 ≤ T) (hr : r ≤ T)
    (hx : 0 < x) (ht : x/2 ≤ t) (htx : t ≤ x) :
    t^(-r) ≤ 2^T*x^(-r) := by
  by_cases h : 0 ≤ r
  · calc
      _ ≤ (x/2)^(-r) := Real.rpow_le_rpow_of_nonpos (by positivity) ht (by linarith only [h])
      _ = 2^r*x^(-r) := by
        rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        simp only [div_eq_mul_inv, inv_inv]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hr) (Real.rpow_nonneg hx.le _)
  · have he : 0 ≤ -r := by linarith only [h]
    have h2 : 1 ≤ (2:ℝ)^T := Real.one_le_rpow (by norm_num) hT
    exact (Real.rpow_le_rpow (by linarith only [hx,ht]) htx he).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hx.le _) h2)

/-- The square-root shift stays inside the positive half-scale chart. -/
theorem sumtail_sqrt_shift_bounds (x : ℝ) (hx : 4 ≤ x) :
    1 ≤ Real.sqrt x ∧ x/2 ≤ x-Real.sqrt x ∧ x-Real.sqrt x ≤ x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hsq := Real.sq_sqrt hx0
  have hs := Real.sqrt_nonneg x
  have hs2 : Real.sqrt x ≤ x/2 := by nlinarith only [hx,hsq,hs]
  exact ⟨by nlinarith only [hx,hsq,hs], by linarith only [hs2], by linarith only [hs]⟩

/-- The main power changes by an error of order `x^(-p-1/2)`. -/
theorem sumtail_power_sqrt_shift (T p x : ℝ) (hp : 0 < p) (hpT : p ≤ T) (hx : 4 ≤ x) :
    |(x-Real.sqrt x)^(-p)-x^(-p)| ≤ T*2^(T+1)*x^(-p-1/2) := by
  have hx0 : 0 < x := by linarith only [hx]
  obtain ⟨_,ht,htx⟩ := sumtail_sqrt_shift_bounds x hx
  have hb := dual_negative_power_lipschitz p (x/2) (x-Real.sqrt x) x hp
    (by positivity) ht (by linarith only [hx0])
  have hd : |x-Real.sqrt x-x| = Real.sqrt x := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (Real.sqrt_nonneg x)]
  rw [hd] at hb
  have hh := sumtail_rpow_half_bound (T+1) (x/2) x (p+1)
    (by linarith only [hp,hpT]) (by linarith only [hpT]) hx0 le_rfl (by linarith only [hx0])
  have hh' : (x/2)^(-p-1) ≤ 2^(T+1)*x^(-p-1) := by
    simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using hh
  calc
    _ ≤ p*(x/2)^(-p-1)*Real.sqrt x := hb
    _ ≤ T*(2^(T+1)*x^(-p-1))*Real.sqrt x :=
      mul_le_mul_of_nonneg_right (mul_le_mul hpT hh' (Real.rpow_nonneg (by positivity) _)
        (by linarith only [hp,hpT])) (Real.sqrt_nonneg x)
    _ = _ := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ = T*2^(T+1)*(x^(-p-1)*x^(1/2 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring

/-- A shifted one-point approximation retains the exact variable ceiling with slack. -/
theorem sumtail_shifted_one_error (Ptail : ℝ → ℝ) (T p e d θ β C H c x : ℝ)
    (hp : 0 < p) (hpT : p ≤ T) (he : e ≤ 1) (hd : 0 ≤ d) (hdθ : d ≤ θ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : |c| ≤ H) (hx : 4 ≤ x)
    (hβe : β ≤ p+e) (hβs : β ≤ p+1/2)
    (herr : |Ptail (x-Real.sqrt x)-c*(x-Real.sqrt x)^(-p)| ≤
      C*(x-Real.sqrt x)^(-p-e+d)) :
    |Ptail (x-Real.sqrt x)-c*x^(-p)| ≤
      (C+H*T)*2^(T+1)*x^(-β+θ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 : 0 < x := by linarith only [hx]
  obtain ⟨_,ht,htx⟩ := sumtail_sqrt_shift_bounds x hx
  have hh := sumtail_rpow_half_bound (T+1) (x-Real.sqrt x) x (p+e-d)
    (by linarith only [hp,hpT]) (by linarith only [hpT,he,hd]) hx0 ht htx
  have hh' : (x-Real.sqrt x)^(-p-e+d) ≤ 2^(T+1)*x^(-p-e+d) := by
    have hexp : -(p+e-d) = -p-e+d := by ring
    simpa only [hexp] using hh
  have hr1 := Real.rpow_le_rpow_of_exponent_le hx1 (show -p-e+d ≤ -β+θ by linarith only [hβe,hdθ])
  have hr2 := Real.rpow_le_rpow_of_exponent_le hx1 (show -p-1/2 ≤ -β+θ by linarith only [hβs,hdθ,hd])
  have hT : 0 ≤ T := hp.le.trans hpT
  have hshift := sumtail_power_sqrt_shift T p x hp hpT hx
  calc
    _ ≤ |Ptail (x-Real.sqrt x)-c*(x-Real.sqrt x)^(-p)|+
        |c*((x-Real.sqrt x)^(-p)-x^(-p))| := by
      have heq : Ptail (x-Real.sqrt x)-c*x^(-p) =
          (Ptail (x-Real.sqrt x)-c*(x-Real.sqrt x)^(-p))+
            c*((x-Real.sqrt x)^(-p)-x^(-p)) := by ring
      rw [heq]
      exact abs_add_le _ _
    _ ≤ C*(2^(T+1)*x^(-p-e+d))+H*(T*2^(T+1)*x^(-p-1/2)) := by
      rw [abs_mul]
      exact add_le_add (herr.trans (mul_le_mul_of_nonneg_left hh' hC))
        (mul_le_mul hc hshift (abs_nonneg _) hH)
    _ ≤ C*(2^(T+1)*x^(-β+θ))+H*(T*2^(T+1)*x^(-β+θ)) := by
      gcongr
    _ = _ := by ring

end DOZZ.Proofs
