/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionLocalApproximation

/-! Removing the origin from smooth circle approximants without changing their energy limit. -/

@[expose] public section

open Filter Topology Set Metric MeasureTheory
open scoped Distributions

namespace DOZZ.Proofs

/-- Planar null changes do not affect the circle energy gap. -/
theorem densityCircleGap_congr_ae (x : ℂ) (r : ℝ) {f g : ℂ → ℝ}
    (h : f =ᵐ[volume] g) : densityCircleGap x r f = densityCircleGap x r g := by
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae_eq_comp h
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae_eq_comp h
  have he : densityEnergy f f = densityEnergy g g := by
    apply integral_congr_ae
    filter_upwards [hfst, hsnd] with p hp hq
    simp only [Function.comp_apply] at hp hq
    rw [hp, hq]
  have hc : (∫ z, f z * ∫ w, gffKernel z w ∂circleMeasure x r) =
      ∫ z, g z * ∫ w, gffKernel z w ∂circleMeasure x r := by
    apply integral_congr_ae
    filter_upwards [h] with z hz
    rw [hz]
  simp only [densityCircleGap, he, hc]

/-- A smooth test can be punctured near zero with arbitrarily small circle-energy error. -/
theorem exists_inversionChart_testFn_gap_approx (x : ℂ) (r : ℝ) (f : TestFn)
    {R : ℝ} (hR : 0 < R) (hs : tsupport (f : ℂ → ℝ) ⊆ closedBall (0 : ℂ) R) :
    ∃ q : ℕ → TestFn,
      (∀ n, tsupport (q n : ℂ → ℝ) ⊆ inversionChart) ∧
      Tendsto (fun n => circleEnergyGap x r (q n)) atTop (𝓝 (circleEnergyGap x r f)) := by
  let b : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
      by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  let q : ℕ → TestFn := fun n =>
    ⟨fun z => f z * (1 - b n z), f.contDiff.mul (contDiff_const.sub (b n).contDiff),
      f.hasCompactSupport.mul_right, subset_univ _⟩
  have hqU : ∀ n, tsupport (q n : ℂ → ℝ) ⊆ inversionChart := by
    intro n
    have hmask : tsupport (fun z : ℂ => 1 - b n z) ⊆
        (ball (0 : ℂ) (1 / ((n : ℝ) + 2)))ᶜ := by
      apply closure_minimal _ isOpen_ball.isClosed_compl
      intro z hz hzball
      exact hz (by dsimp only; rw [(b n).one_of_mem_closedBall (ball_subset_closedBall hzball)]; simp)
    intro z hz
    have hout := hmask (tsupport_mul_subset_right hz)
    change z ≠ 0
    intro hz0
    apply hout
    simp only [hz0, mem_ball, dist_self]; positivity
  obtain ⟨M, hM⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  let g : ℂ → ℝ := fun z => if z = 0 then 0 else f z
  have hlim : ∀ z, Tendsto (fun n => q n z) atTop (𝓝 (g z)) := by
    intro z
    by_cases hz : z = 0
    · subst z
      have hzero n : q n 0 = 0 := by
        change f 0 * (1 - b n 0) = 0
        rw [(b n).one_of_mem_closedBall (by simp [mem_closedBall, b]; positivity)]
        ring
      simpa only [hzero, g, ite_eq_left rfl] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
        convert (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
          (tendsto_add_atTop_nat 2) using 1
        ext n
        simp [Nat.cast_add]
      have hev := ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hz))
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hev] with n hn
      have hb0 : b n z = 0 := image_eq_zero_of_notMem_tsupport (by
        rw [(b n).tsupport_eq]
        simpa only [mem_closedBall, dist_zero_right, not_le, b] using hn)
      simp [q, g, hz, hb0]
  have hg : g =ᵐ[volume] (f : ℂ → ℝ) := by
    filter_upwards [(volume : Measure ℂ).ae_ne 0] with z hz
    simp [g, hz]
  refine ⟨q, hqU, ?_⟩
  simp_rw [← densityCircleGap_testFn]
  rw [← densityCircleGap_congr_ae x r hg]
  apply tendsto_densityCircleGap_of_common_support x r (fun n => q n) g hR hM0
    (fun n => (q n).continuous.measurable)
    (fun n => (subset_tsupport _).trans (tsupport_mul_subset_left.trans hs))
    _ hlim
  intro n z
  change |f z * (1 - b n z)| ≤ M
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (b n).le_one)]
  exact (mul_le_of_le_one_right (abs_nonneg _) (sub_le_self _ (b n).nonneg)).trans
    (by simpa only [Real.norm_eq_abs] using hM z)

/-- Every circle, including a circle meeting zero, admits chart-supported smooth tests
with vanishing circle energy gap. -/
theorem exists_testFn_circleEnergyGap_punctured (x : ℂ) (r : ℝ) :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) := by
  obtain ⟨F, hFs, _hFa, hFg⟩ := exists_testFn_circleEnergyGap_tendsto_zero x r
  have hR : 0 < ‖x‖ + 2 * Real.exp (-r) + 1 := by positivity
  have hex n := exists_inversionChart_testFn_gap_approx x r (F n) hR (hFs n)
  choose Q hQU hQg using hex
  have hchoose n : ∃ m : ℕ,
      |circleEnergyGap x r (Q n m) - circleEnergyGap x r (F n)| <
        1 / ((n : ℝ) + 2) := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hQg n) _
      (by positivity : 0 < 1 / ((n : ℝ) + 2))
    exact ⟨N, by simpa only [Real.dist_eq] using hN N le_rfl⟩
  choose m hm using hchoose
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  refine ⟨fun n => Q n (m n), fun n => hQU n (m n), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using hFg.sub hε) (by simpa using hFg.add hε)
  · intro n
    have h := (abs_lt.mp (hm n)).1
    simp only [one_div] at h
    linarith
  · intro n
    have h := (abs_lt.mp (hm n)).2
    simp only [one_div] at h
    linarith

end DOZZ.Proofs
