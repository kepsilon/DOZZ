/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Weierstrass
public import Mathlib.Topology.MetricSpace.Cauchy

/-! A common canonical limit for an eventually holomorphic geometric Cauchy family. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- Uniform summable increments on an open set produce the canonical holomorphic limit even
when finitely many initial cutoff functions are not holomorphic. -/
theorem holomorphic_limit_of_eventual_geometric {N : ℕ}
    (U : Set (Fin N → ℂ)) (hU : IsOpen U) (F : ℕ → (Fin N → ℂ) → ℂ)
    (K κ : ℝ) (hK : 0 ≤ K) (hκ : 0 < κ)
    (hF : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (F n) U ∧
      ∀ x ∈ U, ‖F (n + 1) x - F n x‖ ≤ K * Real.exp (-κ * n)) :
    DifferentiableOn ℂ (fun x => limUnder atTop (fun n => F n x)) U ∧
      TendstoUniformlyOn F (fun x => limUnder atTop (fun n => F n x)) atTop U := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hF
  let G (n : ℕ) := F (n + n₀)
  let r := Real.exp (-κ)
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hG : ∀ n, DifferentiableOn ℂ (G n) U :=
    fun n => (hn₀ (n + n₀) (Nat.le_add_left n₀ n)).1
  have hstep : ∀ x ∈ U, ∀ n : ℕ, dist (G n x) (G (n + 1) x) ≤ K * r ^ n := by
    intro x hx n
    have hn := (hn₀ (n + n₀) (Nat.le_add_left n₀ n)).2 x hx
    have he : ((n + n₀ : ℕ) : ℝ) ≥ (n : ℝ) := by exact_mod_cast Nat.le_add_right n n₀
    calc
      _ = ‖F ((n + n₀) + 1) x - F (n + n₀) x‖ := by
        rw [dist_comm, dist_eq_norm]
        simp only [G, Nat.add_right_comm n 1 n₀]
      _ ≤ K * Real.exp (-κ * (n + n₀ : ℕ)) := hn
      _ ≤ K * Real.exp (-κ * n) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) hK
      _ = K * r ^ n := by
        rw [show -κ * (n : ℝ) = (n : ℝ) * (-κ) by ring, Real.exp_nat_mul]
  have hconv : ∀ x ∈ U, ∃ L, Tendsto (fun n => F n x) atTop (𝓝 L) := by
    intro x hx
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric _ _ hr (hstep x hx))
    exact ⟨L, (tendsto_add_atTop_iff_nat n₀).mp hL⟩
  let f := fun x => limUnder atTop (fun n => F n x)
  have hlim : ∀ x ∈ U, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    fun x hx => tendsto_nhds_limUnder (hconv x hx)
  have hlimG : ∀ x ∈ U, Tendsto (fun n => G n x) atTop (𝓝 (f x)) :=
    fun x hx => (tendsto_add_atTop_iff_nat n₀).mpr (hlim x hx)
  have hdist : ∀ x ∈ U, ∀ n, dist (G n x) (f x) ≤ K * r ^ n / (1 - r) :=
    fun x hx n => dist_le_of_le_geometric_of_tendsto _ _ hr (hstep x hx) (hlimG x hx) n
  have hbound : Tendsto (fun n : ℕ => K * r ^ n / (1 - r)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).const_mul K).div_const (1 - r)
  have hUG : TendstoUniformlyOn G f atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hbound.eventually (gt_mem_nhds hε)] with n hn x hx
    rw [dist_comm]
    exact (hdist x hx n).trans_lt hn
  have hUF : TendstoUniformlyOn F f atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hUG ε hε)
    filter_upwards [eventually_ge_atTop (k + n₀)] with n hn x hx
    have hn₀ : n₀ ≤ n := (Nat.le_add_left n₀ k).trans hn
    have hnk : k ≤ n - n₀ := (Nat.le_sub_iff_add_le hn₀).mpr hn
    have he := hk (n - n₀) hnk x hx
    simpa only [G, Nat.sub_add_cancel hn₀] using he
  exact ⟨(differentiableOn_of_tendstoLocallyUniformlyOn_fin U hU G f hG
    hUG.tendstoLocallyUniformlyOn).1, hUF⟩

end DOZZ.Proofs
