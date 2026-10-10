/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionPuncturedApproximation
public import DOZZ.GFFStructure.AnnularWeakLimit

/-! Punctured circle approximants with convergence against continuous potentials. -/

@[expose] public section

open Filter MeasureTheory Set Metric
open scoped Topology Distributions

namespace DOZZ.Proofs

/-- Circles compactly inside the punctured chart have smooth local approximants with both
vanishing energy gap and convergence against every continuous potential. -/
theorem exists_inversionChart_circle_weak_approximation (x : ℂ) (r : ℝ)
    (hsmall : 2 * Real.exp (-r) < ‖x‖) :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) ∧
      ∀ k : ℂ → ℝ, Continuous k → Tendsto (fun n => ∫ z, f n z * k z) atTop
        (𝓝 (∫ z, k z ∂circleMeasure x r)) := by
  let R := ‖x‖ + 2 * Real.exp (-r)
  have hR : 0 < R := by dsimp [R]; positivity
  have hU n : tsupport (circleAnnularDensity x r n) ⊆ inversionChart := by
    intro z hz
    have h := tsupport_circleAnnularDensity_subset_centered x r n hz
    change z ≠ 0
    intro hz0
    have ht := Metric.mem_closedBall.mp h
    simp only [hz0, dist_zero_left] at ht
    linarith
  have hc n : HasCompactSupport (circleAnnularDensity x r n) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure
      (tsupport_circleAnnularDensity_subset x r n)
  choose a ha hab hag haU using fun n => exists_inversion_test_mask (hc n) (hU n)
  have hex n := exists_testFn_tendsto_densityCircleGap x r (circleAnnularDensity x r n)
    (continuous_circleAnnularDensity x r n) hR (tsupport_circleAnnularDensity_subset x r n)
  choose F hFs hFa _hFg using hex
  have hchoose (n : ℕ) : ∃ m : ℕ, 1 / ((m : ℝ) + 2) < 1 / ((n : ℝ) + 2) ^ 3 := by
    have ht : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
      convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 2) using 1
      ext m
      simp [Nat.cast_add]
    exact (ht.eventually (gt_mem_nhds (by positivity : 0 < 1 / ((n : ℝ) + 2) ^ 3))).exists
  choose m hm using hchoose
  let f : ℕ → TestFn := fun n =>
    ⟨fun z => F n (m n) z * a n z, (F n (m n)).contDiff.mul (ha n),
      (F n (m n)).hasCompactSupport.mul_right, subset_univ _⟩
  have hs n : tsupport (f n : ℂ → ℝ) ⊆ closedBall (0 : ℂ) (R + 1) :=
    tsupport_mul_subset_left.trans (hFs n (m n))
  have he n z : |f n z - circleAnnularDensity x r n z| < 1 / ((n : ℝ) + 2) ^ 3 := by
    have hid : circleAnnularDensity x r n z * a n z = circleAnnularDensity x r n z := by
      by_cases hz : z ∈ tsupport (circleAnnularDensity x r n)
      · rw [hag n z hz, mul_one]
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    change |F n (m n) z * a n z - circleAnnularDensity x r n z| < _
    rw [← hid, ← sub_mul, abs_mul, abs_of_nonneg (hab n z).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hab n z).2).trans_lt
      ((hFa n (m n) z).trans (hm n))
  refine ⟨f, fun n => tsupport_mul_subset_right.trans (haU n),
    tendsto_circleEnergyGap_of_cubic_approx x r f hs he, ?_⟩
  intro k hk
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  have ht3 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 3) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_pow, one_pow, zero_pow (by norm_num : 3 ≠ 0)] using ht.pow 3
  exact tendsto_integral_testFn_mul_of_circleAnnular_approx x r f
    (fun n => 1 / ((n : ℝ) + 2) ^ 3) (fun n => by positivity) ht3
    (R := R + 1) (by positivity)
    (fun n => (subset_tsupport _).trans (hs n))
    (fun n => (support_circleAnnularDensity_subset x r n).trans
      (closedBall_subset_closedBall (le_add_of_nonneg_right zero_le_one)))
    (fun n z => (he n z).le) k hk

end DOZZ.Proofs
