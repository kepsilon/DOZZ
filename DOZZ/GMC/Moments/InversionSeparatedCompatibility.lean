/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAnnularKernelBounds

/-! Separated mixed and ordinary kernel comparisons for inversion compatibility. -/

@[expose] public section

open Set Metric Real
open DOZZ.Proofs.CirclePotential

namespace DOZZ.Proofs

/-- Under the geometric separation conditions, both mixed and ordinary target kernels
approach the pulled-source kernel with error at most twice the sum of cutoff radii. -/
theorem inversion_mixed_kernel_difference_le
    {x y : ℂ} {r s : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hsmall : Real.exp (-r) < ‖x‖)
    (hmixed : Real.exp (-s) * ((‖x‖ + Real.exp (-r)) * ‖y‖) ≤
      ‖x - y‖ - Real.exp (-r))
    (htarget : Real.exp (-r) + Real.exp (-s) ≤ ‖x - y‖)
    (hsource : Real.exp (-r) + Real.exp (-s) ≤ ‖x⁻¹ - y⁻¹‖) :
    |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)) -
      circleKernel x⁻¹ r y⁻¹ s| ≤ 2 * (Real.exp (-r) + Real.exp (-s)) ∧
    |circleKernel x r y s - circleKernel x⁻¹ r y⁻¹ s| ≤
      2 * (Real.exp (-r) + Real.exp (-s)) := by
  have hmix := inversion_mixed_offDiagonal_point_error_le hy hsmall hmixed
    (le_trans (le_add_of_nonneg_right (Real.exp_pos (-s)).le) htarget)
  have hsrc := abs_circleKernel_sub_gffKernel_le x⁻¹ y⁻¹ r s hsource
  rw [gffKernel_inv hx hy hxy] at hsrc
  have htgt := abs_circleKernel_sub_gffKernel_le x y r s htarget
  constructor
  · have htri := abs_sub_le
      (circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)))
      (gffKernel x y) (circleKernel x⁻¹ r y⁻¹ s)
    rw [abs_sub_comm (gffKernel x y)] at htri
    linarith only [htri, hmix, hsrc]
  · have htri := abs_sub_le (circleKernel x r y s) (gffKernel x y)
      (circleKernel x⁻¹ r y⁻¹ s)
    rw [abs_sub_comm (gffKernel x y)] at htri
    linarith only [htri, htgt, hsrc]

/-- Both separated kernel differences converge uniformly on every bounded annulus. -/
theorem inversion_separated_kernel_uniform {m R d η : ℝ}
    (hm : 0 < m) (hR : 0 ≤ R) (hd : 0 < d) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r s : ℝ,
      Real.exp (-r) ≤ δ → Real.exp (-s) ≤ δ → ∀ x y : ℂ,
      2 * m ≤ ‖x‖ → 2 * m ≤ ‖y‖ → ‖x‖ ≤ R → ‖y‖ ≤ R → d ≤ ‖x - y‖ →
      |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)) -
        circleKernel x⁻¹ r y⁻¹ s| < η ∧
      |circleKernel x r y s - circleKernel x⁻¹ r y⁻¹ s| < η := by
  let A := (R + 1) ^ 2 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith only [sq_nonneg (R + 1)]
  let δ := min (m / 2) (min 1 (min (d / (2 * A)) (η / 8)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro r s hr hs x y hxlo hylo hxhi hyhi hdist
  have hδm : δ ≤ m / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδd : δ ≤ d / (2 * A) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδη : δ ≤ η / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx : x ≠ 0 := norm_pos_iff.mp (by linarith only [hxlo, hm])
  have hy : y ≠ 0 := norm_pos_iff.mp (by linarith only [hylo, hm])
  have hxy : x ≠ y := by
    intro h
    have hz : ‖x - y‖ = 0 := by simp only [h, sub_self, norm_zero]
    linarith only [hdist, hd, hz]
  have hδA : 2 * δ * A ≤ d := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hδd
    nlinarith only [ht]
  have htarget : Real.exp (-r) + Real.exp (-s) ≤ ‖x - y‖ := by
    have ht : 2 * δ ≤ 2 * δ * A := le_mul_of_one_le_right (by positivity) hA1
    linarith only [hr, hs, ht, hδA, hdist]
  have hnorms : ‖x‖ * ‖y‖ ≤ A := by
    have hp := mul_le_mul hxhi hyhi (norm_nonneg _) hR
    dsimp [A]
    nlinarith only [hp, hR]
  have hsource : Real.exp (-r) + Real.exp (-s) ≤ ‖x⁻¹ - y⁻¹‖ := by
    rw [complexInv_distance_of_ne_zero hx hy]
    apply (le_div_iff₀ (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))).mpr
    calc
      (Real.exp (-r) + Real.exp (-s)) * (‖x‖ * ‖y‖) ≤ (2 * δ) * A :=
        mul_le_mul (by linarith only [hr, hs]) hnorms (by positivity) (by positivity)
      _ ≤ ‖x - y‖ := hδA.trans hdist
  have hproduct : (‖x‖ + Real.exp (-r)) * ‖y‖ ≤ A - 1 := by
    have hp := mul_le_mul (add_le_add hxhi (hr.trans hδ1)) hyhi (norm_nonneg _) (by positivity)
    dsimp [A]
    nlinarith only [hp, hR]
  have hmixed : Real.exp (-s) * ((‖x‖ + Real.exp (-r)) * ‖y‖) ≤
      ‖x - y‖ - Real.exp (-r) := by
    have hp := mul_le_mul hs hproduct (by positivity) hδ.le
    have hbig : δ * A ≤ d := by nlinarith only [hδA, hA, hδ]
    nlinarith only [hp, hbig, hr, hdist]
  have ht := inversion_mixed_kernel_difference_le hx hy hxy
    (by linarith only [hr, hδm, hxlo, hm]) hmixed htarget hsource
  have hsum : 2 * (Real.exp (-r) + Real.exp (-s)) < η := by
    linarith only [hr, hs, hδη, hη]
  exact ⟨ht.1.trans_lt hsum, ht.2.trans_lt hsum⟩

end DOZZ.Proofs
