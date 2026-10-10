/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionTest
public import DOZZ.GFFStructure.AnnularCircleEnergy

/-! Smooth circle-test approximation within the punctured inversion chart. -/

@[expose] public section

open Filter Topology Set Metric MeasureTheory
open scoped Distributions

namespace DOZZ.Proofs

/-- A compact density supported away from zero admits a smooth mask equal to one on its support
and identically zero near zero. -/
theorem exists_inversion_test_mask {g : ℂ → ℝ} (hcompact : HasCompactSupport g)
    (hU : tsupport g ⊆ inversionChart) :
    ∃ a : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, 0 ≤ a x ∧ a x ≤ 1) ∧
      (∀ x ∈ tsupport g, a x = 1) ∧ tsupport a ⊆ inversionChart := by
  have h0 : (0 : ℂ) ∉ tsupport g := by
    intro h
    have := hU h
    simp [inversionChart] at this
  have hnhds : (tsupport g)ᶜ ∈ 𝓝 (0 : ℂ) :=
    hcompact.isClosed.isOpen_compl.mem_nhds h0
  obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.mp hnhds
  let b : ContDiffBump (0 : ℂ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let a : ℂ → ℝ := fun x => 1 - b x
  have ha : tsupport a ⊆ (ball (0 : ℂ) (δ / 4))ᶜ := by
    apply closure_minimal
    · intro x hx hxball
      have hb : b x = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hxball)
      exact hx (by simp [a, hb])
    · exact isOpen_ball.isClosed_compl
  refine ⟨a, contDiff_const.sub b.contDiff, ?_, ?_, ?_⟩
  · intro x
    dsimp [a]
    exact ⟨sub_nonneg.mpr b.le_one, sub_le_self _ b.nonneg⟩
  · intro x hx
    have hout : x ∉ closedBall (0 : ℂ) (δ / 2) := by
      intro hxball
      have hxδ : x ∈ ball (0 : ℂ) δ :=
        closedBall_subset_ball (by linarith) hxball
      exact hδK hxδ hx
    have hb : b x = 0 := image_eq_zero_of_notMem_tsupport (by
      rw [b.tsupport_eq]
      exact hout)
    simp [a, hb]
  · intro x hx
    change x ≠ 0
    intro hx0
    have := ha hx
    simp [hx0, mem_ball, hδ] at this

/-- Smooth density approximants can be chosen entirely inside the punctured chart, preserving
their circle-energy limit. The fixed mask controls the omitted point for every approximant. -/
theorem exists_testFn_tendsto_densityCircleGap_inversionChart
    (x : ℂ) (r : ℝ) (g : ℂ → ℝ) (hg : Continuous g)
    {R : ℝ} (hR : 0 < R) (hball : tsupport g ⊆ closedBall (0 : ℂ) R)
    (hU : tsupport g ⊆ inversionChart) :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart) ∧
      (∀ n, tsupport (f n : ℂ → ℝ) ⊆ closedBall (0 : ℂ) (R + 1)) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 (densityCircleGap x r g)) := by
  have hcompact : HasCompactSupport g :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hball
  obtain ⟨a, ha, hab, hag, haU⟩ := exists_inversion_test_mask hcompact hU
  obtain ⟨F, hFball, hFapprox, _hFgap⟩ :=
    exists_testFn_tendsto_densityCircleGap x r g hg hR hball
  let f : ℕ → TestFn := fun n =>
    ⟨fun z => F n z * a z, (F n).contDiff.mul ha,
      (F n).hasCompactSupport.mul_right, subset_univ _⟩
  have hfball : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ closedBall (0 : ℂ) (R + 1) := by
    intro n
    exact tsupport_mul_subset_left.trans (hFball n)
  have hfg : ∀ z, g z * a z = g z := by
    intro z
    by_cases hz : z ∈ tsupport g
    · rw [hag z hz, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  have happrox : ∀ n z, |f n z - g z| < 1 / ((n : ℝ) + 2) := by
    intro n z
    change |F n z * a z - g z| < _
    rw [← hfg z, ← sub_mul, abs_mul, abs_of_nonneg (hab z).1]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg _) (hab z).2) (hFapprox n z)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuous hg
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hbound : ∀ n z, |f n z| ≤ M + 1 := by
    intro n z
    have he := happrox n z
    have hεle : 1 / ((n : ℝ) + 2) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hgM : |g z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z
    have htri := abs_add_le (f n z - g z) (g z)
    rw [sub_add_cancel] at htri
    linarith
  have hlim : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    intro z
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hεlim)
      (by simpa using tendsto_const_nhds.add hεlim)
    · intro n
      change g z - ((n : ℝ) + 2)⁻¹ ≤ f n z
      have h := (abs_lt.mp (happrox n z)).1
      simp only [one_div] at h
      linarith
    · intro n
      change f n z ≤ g z + ((n : ℝ) + 2)⁻¹
      have h := (abs_lt.mp (happrox n z)).2
      simp only [one_div] at h
      linarith
  refine ⟨f, ?_, hfball, ?_⟩
  · intro n
    exact tsupport_mul_subset_right.trans haU
  · simp_rw [← densityCircleGap_testFn]
    exact tendsto_densityCircleGap_of_common_support x r (fun n => f n) g
      (R := R + 1) (M := M + 1) (by linarith) (by linarith)
      (fun n => (f n).continuous.measurable)
      (fun n => (subset_tsupport _).trans (hfball n)) hbound hlim

/-- The annular circle-density approximants stay within twice the circle radius of its center.
-/
theorem tsupport_circleAnnularDensity_subset_centered (x : ℂ) (r : ℝ) (n : ℕ) :
    tsupport (circleAnnularDensity x r n) ⊆ closedBall x (2 * Real.exp (-r)) := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hρ : DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • (z - x)) ≠ 0 := by
    intro hzero
    exact hz (by simp only [circleAnnularDensity, hzero, mul_zero])
  have hb := DOZZ.annularProbabilityDensity_radius_bound n _ hρ
  have hn : 1 ≤ (n : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hi : 1 / ((n : ℝ) + 2) ≤ 1 :=
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn).trans_eq one_div_one
  have hscale : ‖(Real.exp (-r))⁻¹ • (z - x)‖ ≤ 2 := by
    linarith [(abs_lt.mp hb).2]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.exp_pos _))] at hscale
  have hmul := mul_le_mul_of_nonneg_left hscale (Real.exp_pos (-r)).le
  rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul] at hmul
  simpa only [mem_closedBall, dist_eq_norm, mul_comm] using hmul

/-- Small circles in the punctured chart have vanishing-energy-gap smooth approximants whose
supports all lie in that chart. These tests can be inverted before taking their random L² limits.
-/
theorem exists_testFn_circleEnergyGap_inversionChart (x : ℂ) (r : ℝ)
    (hsmall : 2 * Real.exp (-r) < ‖x‖) :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) := by
  have hU : ∀ n, tsupport (circleAnnularDensity x r n) ⊆ inversionChart := by
    intro n z hz
    have hclose := tsupport_circleAnnularDensity_subset_centered x r n hz
    change z ≠ 0
    intro hz0
    have h := Metric.mem_closedBall.mp hclose
    simp only [hz0, dist_zero_left] at h
    linarith
  have hR : 0 < ‖x‖ + 2 * Real.exp (-r) := by positivity
  have hex n := exists_testFn_tendsto_densityCircleGap_inversionChart x r
    (circleAnnularDensity x r n) (continuous_circleAnnularDensity x r n) hR
    (tsupport_circleAnnularDensity_subset x r n) (hU n)
  choose F hFU hFball hFgap using hex
  have hchoose n : ∃ m : ℕ,
      |circleEnergyGap x r (F n m) - densityCircleGap x r (circleAnnularDensity x r n)| <
        1 / ((n : ℝ) + 2) := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hFgap n) _ (by positivity :
      0 < 1 / ((n : ℝ) + 2))
    exact ⟨N, by simpa only [Real.dist_eq] using hN N le_rfl⟩
  choose m hm using hchoose
  let f : ℕ → TestFn := fun n => F n (m n)
  have hεlim : Tendsto (fun n : ℕ => 6 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (6 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  have hbound n : |circleEnergyGap x r (f n)| ≤ 6 / ((n : ℝ) + 2) := by
    have he := (hm n).le
    have hb := abs_densityCircleGap_circleAnnular_le x r n
    have htri := abs_add_le
      (circleEnergyGap x r (f n) - densityCircleGap x r (circleAnnularDensity x r n))
      (densityCircleGap x r (circleAnnularDensity x r n))
    rw [sub_add_cancel] at htri
    dsimp [f] at *
    simp only [div_eq_mul_inv] at he hb ⊢
    linarith
  refine ⟨f, fun n => hFU n (m n), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hεlim.neg) hεlim
  · intro n
    exact (abs_le.mp (hbound n)).1
  · intro n
    exact (abs_le.mp (hbound n)).2

end DOZZ.Proofs
