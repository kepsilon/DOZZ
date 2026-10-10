/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.FiniteRandomTestLimit

/-! Uniform probability approximation for correlated random compact tests. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- A uniformly negligible probability approximation preserves the cutoff limit.
The approximants may be selected using the same outcome as the chaos. -/
theorem tendstoInMeasure_uniform_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (a : ℕ → ℕ → Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hconv : ∀ k, TendstoInMeasure P (a k) atTop (b k))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ e : ℕ → ℝ≥0∞,
      Tendsto e atTop (𝓝 0) ∧
      (∀ k n, P {ω | ε ≤ ‖f n ω - a k n ω‖} ≤ e k) ∧
      (∀ k, P {ω | ε ≤ ‖b k ω - g ω‖} ≤ e k)) :
    TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let t : ℝ := ε / 3
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨e, he, hleft, hright⟩ := happrox t ht
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hd : 0 < δ / 3 := ENNReal.div_pos_iff.mpr ⟨hδ.ne', by norm_num⟩
  obtain ⟨K, hK⟩ := (ENNReal.tendsto_atTop_zero.mp he) (δ / 3) hd
  have hk : e K ≤ δ / 3 := hK K le_rfl
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp
    ((tendstoInMeasure_iff_norm.mp (hconv K)) t ht)) (δ / 3) hd
  refine ⟨N, fun n hn => ?_⟩
  let L : Set Ω := {ω | t ≤ ‖f n ω - a K n ω‖}
  let C : Set Ω := {ω | t ≤ ‖a K n ω - b K ω‖}
  let R : Set Ω := {ω | t ≤ ‖b K ω - g ω‖}
  have hsubset : {ω | ε ≤ ‖f n ω - g ω‖} ⊆ L ∪ C ∪ R := by
    intro ω hω
    by_contra hnot
    have hL : ‖f n ω - a K n ω‖ < t := lt_of_not_ge (fun h => hnot (Or.inl (Or.inl h)))
    have hC : ‖a K n ω - b K ω‖ < t := lt_of_not_ge (fun h => hnot (Or.inl (Or.inr h)))
    have hR : ‖b K ω - g ω‖ < t := lt_of_not_ge (fun h => hnot (Or.inr h))
    have htriangle : ‖f n ω - g ω‖ ≤ ‖f n ω - a K n ω‖ +
        ‖a K n ω - b K ω‖ + ‖b K ω - g ω‖ := by
      have h1 := norm_add_le (f n ω - a K n ω) (a K n ω - b K ω)
      have h2 := norm_add_le (f n ω - b K ω) (b K ω - g ω)
      have heq : f n ω - a K n ω + (a K n ω - b K ω) = f n ω - b K ω := by ring
      have heq' : f n ω - b K ω + (b K ω - g ω) = f n ω - g ω := by ring
      rw [heq] at h1
      rw [heq'] at h2
      linarith
    have hsum : ‖f n ω - g ω‖ < ε := by
      dsimp [t] at hL hC hR
      simp only [Real.norm_eq_abs] at htriangle ⊢
      linarith
    exact (not_le_of_gt hsum) hω
  calc
    P {ω | ε ≤ ‖f n ω - g ω‖} ≤ P (L ∪ C ∪ R) := measure_mono hsubset
    _ ≤ P L + P C + P R := (measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ δ / 3 + δ / 3 + δ / 3 :=
      add_le_add (add_le_add ((hleft K n).trans hk) (hN n hn)) ((hright K).trans hk)
    _ = δ := by rw [← two_mul, ← add_one_mul, show (2 : ℝ≥0∞) + 1 = 3 by norm_num,
      ENNReal.mul_div_cancel (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]


end DOZZ.Proofs
