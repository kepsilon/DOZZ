/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.IncrementIntegrability
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
/-! Relative control of the signed inverse increment under the kernel squeeze factors. -/
@[expose] public section
open Set
namespace DOZZ.Proofs

/-- The positive inverse-power loss is concave in a nonnegative added mass. -/
theorem dual_inverse_increment_concave (p A : ℝ) (hp : 0 < p) (hA : 0 < A) :
    ConcaveOn ℝ (Ici 0) (fun t : ℝ => A^(-p)-(A+t)^(-p)) := by
  let g := fun t : ℝ => A^(-p)-(A+t)^(-p)
  have hd (t : ℝ) (ht : t ∈ Ici 0) : HasDerivAt g (p*(A+t)^(-p-1)) t := by
    have ht0 : 0 ≤ t := ht
    have hh := (Real.hasDerivAt_rpow_const (x := A+t) (p := -p)
      (Or.inl (by linarith only [hA, ht0]))).comp t ((hasDerivAt_id t).const_add A)
    have hh' := hh.const_sub (A^(-p))
    convert hh' using 1 <;> simp only [g, Function.comp_def, mul_one, neg_mul, neg_neg]
  have hm : AntitoneOn (deriv g) (interior (Ici 0)) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := interior_subset hx
    have hy0 : 0 ≤ y := interior_subset hy
    rw [(hd x hx0).deriv, (hd y hy0).deriv]
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hA, hx0])
      (add_le_add le_rfl hxy) (by linarith only [hp])
  exact hm.concaveOn_of_deriv (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)

/-- Concavity controls every contraction of the added mass without using a first moment. -/
theorem dual_inverse_increment_scale_lower (p A t θ : ℝ) (hp : 0 < p) (hA : 0 < A)
    (ht : 0 ≤ t) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ*(A^(-p)-(A+t)^(-p)) ≤ A^(-p)-(A+θ*t)^(-p) := by
  have hh := (dual_inverse_increment_concave p A hp hA).2
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show t ∈ Ici 0 from ht)
    (sub_nonneg.mpr hθ1) hθ (by ring : (1-θ)+θ = 1)
  simpa only [smul_eq_mul, mul_zero, zero_add, add_zero, sub_self] using hh

/-- A relative kernel factor changes the signed inverse increment by at most the same
relative factor times the unscaled loss. This avoids using the divergent inner first moment. -/
theorem dual_negative_increment_relative_scale (p A t θ : ℝ) (hp : 0 < p)
    (hA : 0 < A) (ht : 0 ≤ t) (hθ : 0 ≤ θ) :
    |((A+θ*t)^(-p)-A^(-p))-((A+t)^(-p)-A^(-p))| ≤
      |θ-1| *(A^(-p)-(A+t)^(-p)) := by
  have hpos : 0 ≤ A^(-p)-(A+t)^(-p) := sub_nonneg.mpr
    (Real.rpow_le_rpow_of_nonpos hA (by linarith only [ht]) (neg_nonpos.mpr hp.le))
  by_cases hθ1 : θ ≤ 1
  · have hlow := dual_inverse_increment_scale_lower p A t θ hp hA ht hθ hθ1
    have hmono : (A+t)^(-p) ≤ (A+θ*t)^(-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (add_le_add le_rfl (mul_le_of_le_one_left ht hθ1)) (neg_nonpos.mpr hp.le)
    rw [abs_of_nonneg (by linarith only [hmono]), abs_of_nonpos (by linarith only [hθ1])]
    nlinarith only [hlow]
  · have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hθ1)
    have hlow := dual_inverse_increment_scale_lower p A (θ*t) (1/θ) hp hA
      (mul_nonneg hθ ht) (by positivity) ((div_le_one hθpos).mpr (le_of_not_ge hθ1))
    have he : (1/θ)*(θ*t) = t := by field_simp
    rw [he] at hlow
    have hscaled := mul_le_mul_of_nonneg_left hlow hθpos.le
    have hm : (A+θ*t)^(-p) ≤ (A+t)^(-p) :=
      Real.rpow_le_rpow_of_nonpos (by linarith only [hA, ht])
        (add_le_add le_rfl (le_mul_of_one_le_left ht (le_of_not_ge hθ1))) (neg_nonpos.mpr hp.le)
    have hcancel : θ*(1/θ*(A^(-p)-(A+θ*t)^(-p))) = A^(-p)-(A+θ*t)^(-p) := by field_simp
    rw [hcancel] at hscaled
    rw [abs_of_nonpos (by linarith only [hm]), abs_of_nonneg (by linarith only [hθpos, hθ1])]
    nlinarith only [hscaled]

/-- The literal inner-kernel squeeze gives a relative error in the signed increment,
controlled by the unscaled inverse-power loss. -/
theorem dual_negative_increment_kernel_squeeze (p A t u θlo θhi : ℝ)
    (hp : 0 < p) (hA : 0 < A) (ht : 0 ≤ t) (hlo : 0 ≤ θlo) (hhi : 0 ≤ θhi)
    (hu : θlo*t ≤ u) (hv : u ≤ θhi*t) :
    |((A+u)^(-p)-A^(-p))-((A+t)^(-p)-A^(-p))| ≤
      max |θlo-1| |θhi-1| * (A^(-p)-(A+t)^(-p)) := by
  have hu0 : 0 ≤ u := (mul_nonneg hlo ht).trans hu
  have hLoss : 0 ≤ A^(-p)-(A+t)^(-p) := sub_nonneg.mpr
    (Real.rpow_le_rpow_of_nonpos hA (by linarith only [ht]) (neg_nonpos.mpr hp.le))
  have hLower : (A+θhi*t)^(-p)-A^(-p) ≤ (A+u)^(-p)-A^(-p) := by
    simpa only [one_mul] using
      dual_negative_increment_antitone p A 1 u (θhi*t) hp.le hA zero_le_one hu0 hv
  have hUpper : (A+u)^(-p)-A^(-p) ≤ (A+θlo*t)^(-p)-A^(-p) := by
    simpa only [one_mul] using
      dual_negative_increment_antitone p A 1 (θlo*t) u hp.le hA zero_le_one (mul_nonneg hlo ht) hu
  have hLo := (dual_negative_increment_relative_scale p A t θlo hp hA ht hlo).trans
    (mul_le_mul_of_nonneg_right (le_max_left |θlo-1| |θhi-1|) hLoss)
  have hHi := (dual_negative_increment_relative_scale p A t θhi hp hA ht hhi).trans
    (mul_le_mul_of_nonneg_right (le_max_right |θlo-1| |θhi-1|) hLoss)
  obtain ⟨hHil, _⟩ := abs_le.mp hHi
  obtain ⟨_, hLou⟩ := abs_le.mp hLo
  exact abs_le.mpr ⟨by linarith only [hLower, hHil], by linarith only [hUpper, hLou]⟩

end DOZZ.Proofs
