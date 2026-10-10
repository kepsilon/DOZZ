/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WeakConv

/-! # Grid approximation of double integrals

For a finite measure `m`, the double integral of a kernel `K` that is close to a kernel `H₀` away
from the diagonal is compared with the grid sum `∑ m(Q_i) ∫ H₀(c_i, y) dm(y)` over the squares
`Q_i` with corners `c_i`. The error is bounded by the modulus of continuity of `H₀` away from the
diagonal and by the near-diagonal mass. The near-diagonal mass is itself squeezed between grid
sums, and it tends to zero as the width shrinks when `m` has no atoms. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem bpz_integrable_slice {m : Measure ℂ} [IsFiniteMeasure m] {g : ℂ → ℂ → ℝ}
    (hg : Measurable (Function.uncurry g)) {C : ℝ} (hC : ∀ x y, |g x y| ≤ C) (x : ℂ) :
    Integrable (fun y => g x y) m :=
  integrable_of_bdd_finite (hg.comp (measurable_const.prodMk measurable_id)) (hC x)

theorem bpz_measurable_inner {ν : Measure ℂ} [IsFiniteMeasure ν] {g : ℂ → ℂ → ℝ}
    (hg : Measurable (Function.uncurry g)) : Measurable (fun x => ∫ y, g x y ∂ν) :=
  (hg.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem bpz_integrable_inner {m ν : Measure ℂ} [IsFiniteMeasure m] [IsFiniteMeasure ν]
    {g : ℂ → ℂ → ℝ} (hg : Measurable (Function.uncurry g)) {C : ℝ} (hC : ∀ x y, |g x y| ≤ C) :
    Integrable (fun x => ∫ y, g x y ∂ν) m :=
  integrable_of_bdd_finite (bpz_measurable_inner hg) (C := C * ν.real Set.univ)
    (bpz_inner_integral_bdd hC)

theorem bpzNearKernel_abs_le (ρ t : ℝ) (x y : ℂ) : |bpzNearKernel ρ t x y| ≤ 1 := by
  rw [abs_of_nonneg (bpzNearKernel_nonneg ρ t x y)]; exact bpzNearKernel_le_one ρ t x y

theorem bpzNearDiag_eq (ρ t : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    bpzNearDiag ρ t μ = ∫ x, (if ‖x‖ ≤ ρ then μ.real (Metric.ball x t) else 0) ∂μ := by
  unfold bpzNearDiag
  congr 1
  funext x
  exact integral_bpzNearKernel μ ρ t x

theorem iInter_ball_inv_succ (x : ℂ) :
    ⋂ k : ℕ, Metric.ball x (1 / ((k : ℝ) + 1)) = {x} := by
  ext y
  simp only [Set.mem_iInter, Metric.mem_ball, Set.mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    have hpos : 0 < dist y x := dist_pos.mpr hne
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact absurd (hy k) (not_lt.mpr hk.le)
  · rintro rfl k
    rw [dist_self]
    positivity

/-- For a finite measure without atoms the near-diagonal mass vanishes in the limit. -/
theorem tendsto_bpzNearDiag_zero (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} = 0)
    (ρ : ℝ) : Tendsto (fun k : ℕ => bpzNearDiag ρ (1 / ((k : ℝ) + 1)) μ) atTop (𝓝 0) := by
  simp_rw [bpzNearDiag_eq]
  have hlim : ∀ x, Tendsto (fun k : ℕ =>
      if ‖x‖ ≤ ρ then μ.real (Metric.ball x (1 / ((k : ℝ) + 1))) else 0) atTop (𝓝 0) := by
    intro x
    by_cases hx : ‖x‖ ≤ ρ
    · simp only [hx, ↓reduceIte]
      have hanti : Antitone fun k : ℕ => Metric.ball x (1 / ((k : ℝ) + 1)) := by
        intro i j hij
        apply Metric.ball_subset_ball
        gcongr
      have h := tendsto_measure_iInter_atTop (μ := μ)
        (fun _ => measurableSet_ball.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rw [iInter_ball_inv_succ, hμ x] at h
      have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
      simpa [Function.comp_def, measureReal_def] using h'
    · simp only [hx, ↓reduceIte]
      exact tendsto_const_nhds
  have hint := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : ℂ => μ.real Set.univ) (F := fun (k : ℕ) x =>
      if ‖x‖ ≤ ρ then μ.real (Metric.ball x (1 / ((k : ℝ) + 1))) else 0) (f := fun _ => 0)
    (fun k => ?_) (integrable_const _) (fun k => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall hlim)
  · simpa using hint
  · have hm := bpz_measurable_inner (ν := μ) (measurable_bpzNearKernel ρ (1 / ((k : ℝ) + 1)))
    have heq : (fun x => ∫ y, bpzNearKernel ρ (1 / ((k : ℝ) + 1)) x y ∂μ) = fun x =>
        if ‖x‖ ≤ ρ then μ.real (Metric.ball x (1 / ((k : ℝ) + 1))) else 0 := by
      funext x; exact integral_bpzNearKernel μ ρ _ x
    rw [heq] at hm
    exact hm.aestronglyMeasurable
  · split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (Set.subset_univ _)
    · simp

/-- The near-diagonal mass is bounded by a grid sum. -/
theorem bpzNearDiag_le_grid (μ : Measure ℂ) [IsFiniteMeasure μ] {ρ t h : ℝ} (hh : 0 < h) :
    bpzNearDiag ρ t μ ≤ ∑ i ∈ bpzGridBox ⌈ρ / h⌉₊, μ.real (bpzGridIdx h ⁻¹' {i}) *
      μ.real (Metric.ball (bpzGridCorner h i) (t + 2 * h)) := by
  rw [← integral_bpzGrid_step h _ (fun i => μ.real (Metric.ball (bpzGridCorner h i) (t + 2 * h))),
    bpzNearDiag_eq]
  refine integral_mono (integrable_of_bdd_finite ?_ (C := μ.real Set.univ) ?_)
    (integrable_of_bdd_finite (measurable_bpzGrid_step h (bpzGridBox ⌈ρ / h⌉₊)
      (fun i => μ.real (Metric.ball (bpzGridCorner h i) (t + 2 * h)))) (C := μ.real Set.univ) ?_)
    fun x => ?_
  · have hm := bpz_measurable_inner (ν := μ) (measurable_bpzNearKernel ρ t)
    have heq : (fun x => ∫ y, bpzNearKernel ρ t x y ∂μ) = fun x =>
        if ‖x‖ ≤ ρ then μ.real (Metric.ball x t) else 0 := by
      funext x; exact integral_bpzNearKernel μ ρ t x
    rwa [heq] at hm
  · intro x
    split_ifs
    · rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (Set.subset_univ _)
    · simp
  · intro x
    split_ifs
    · rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (Set.subset_univ _)
    · simp
  · dsimp only
    by_cases hx : ‖x‖ ≤ ρ
    · have hS : bpzGridIdx h x ∈ bpzGridBox ⌈ρ / h⌉₊ := bpzGridIdx_mem_box hh hx
      rw [ite_eq_left hx, ite_eq_left hS]
      refine measureReal_mono (fun y hy => ?_)
      rw [Metric.mem_ball] at hy ⊢
      have := norm_sub_bpzGridCorner_le hh x
      rw [dist_eq_norm] at hy ⊢
      calc ‖y - bpzGridCorner h (bpzGridIdx h x)‖
          ≤ ‖y - x‖ + ‖x - bpzGridCorner h (bpzGridIdx h x)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < t + 2 * h := add_lt_add_of_lt_of_le hy this
    · rw [ite_eq_right hx]
      split_ifs
      · exact measureReal_nonneg
      · exact le_rfl

/-- A grid sum is bounded by the near-diagonal mass at a larger width and radius. -/
theorem grid_le_bpzNearDiag (μ : Measure ℂ) [IsFiniteMeasure μ] {ρ t h : ℝ} {N : ℕ}
    (hh : 0 < h) (hρ : 2 * ((N + 1) * h) ≤ ρ) :
    ∑ i ∈ bpzGridBox N, μ.real (bpzGridIdx h ⁻¹' {i}) *
      μ.real (Metric.ball (bpzGridCorner h i) (t + 2 * h)) ≤ bpzNearDiag ρ (t + 4 * h) μ := by
  rw [← integral_bpzGrid_step h _ (fun i => μ.real (Metric.ball (bpzGridCorner h i) (t + 2 * h))),
    bpzNearDiag_eq]
  refine integral_mono
    (integrable_of_bdd_finite (measurable_bpzGrid_step h (bpzGridBox N)
      (fun i => μ.real (Metric.ball (bpzGridCorner h i) (t + 2 * h)))) (C := μ.real Set.univ) ?_)
    (integrable_of_bdd_finite ?_ (C := μ.real Set.univ) ?_) fun x => ?_
  · intro x
    split_ifs
    · rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (Set.subset_univ _)
    · simp
  · have hm := bpz_measurable_inner (ν := μ) (measurable_bpzNearKernel ρ (t + 4 * h))
    have heq : (fun x => ∫ y, bpzNearKernel ρ (t + 4 * h) x y ∂μ) = fun x =>
        if ‖x‖ ≤ ρ then μ.real (Metric.ball x (t + 4 * h)) else 0 := by
      funext x; exact integral_bpzNearKernel μ ρ _ x
    rwa [heq] at hm
  · intro x
    split_ifs
    · rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (Set.subset_univ _)
    · simp
  · dsimp only
    by_cases hS : bpzGridIdx h x ∈ bpzGridBox N
    · have hx : ‖x‖ ≤ ρ := (norm_le_of_bpzGridIdx_mem_box hh hS).trans hρ
      rw [ite_eq_left hS, ite_eq_left hx]
      refine measureReal_mono (fun y hy => ?_)
      rw [Metric.mem_ball] at hy ⊢
      have := norm_sub_bpzGridCorner_le hh x
      rw [dist_eq_norm] at hy ⊢
      calc ‖y - x‖ ≤ ‖y - bpzGridCorner h (bpzGridIdx h x)‖ +
            ‖bpzGridCorner h (bpzGridIdx h x) - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < t + 2 * h + 2 * h := by
            rw [norm_sub_rev (bpzGridCorner h _)]
            exact add_lt_add_of_lt_of_le hy this
        _ = t + 4 * h := by ring
    · rw [ite_eq_right hS]
      split_ifs
      · exact measureReal_nonneg
      · exact le_rfl

theorem bpzGrid_box_radius {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h) (hh1 : h ≤ 1 / 4) :
    2 * ((⌈R / h⌉₊ + 1) * h) ≤ 2 * R + 1 := by
  have hc : (⌈R / h⌉₊ : ℝ) < R / h + 1 := Nat.ceil_lt_add_one (div_nonneg hR hh.le)
  have : ((⌈R / h⌉₊ : ℝ) + 1) * h < (R / h + 2) * h := by
    apply mul_lt_mul_of_pos_right _ hh; linarith
  have h2 : (R / h + 2) * h = R + 2 * h := by field_simp
  nlinarith

/-- Pathwise error of the grid approximation of a double integral. -/
theorem bpz_double_grid_error (m : Measure ℂ) [IsFiniteMeasure m] (K H₀ : ℂ → ℂ → ℝ)
    (hKm : Measurable (Function.uncurry K)) (hH₀m : Measurable (Function.uncurry H₀))
    {C R η ε₁ δ h : ℝ} (hR : 0 ≤ R) (hh : 0 < h) (hh1 : h ≤ 1 / 4) (hhδ : 2 * h ≤ δ)
    (hε₁ : 0 ≤ ε₁) (hKb : ∀ x y, |K x y| ≤ C) (hH₀b : ∀ x y, |H₀ x y| ≤ C)
    (hKs : ∀ x y, (R < ‖x‖ ∨ R < ‖y‖) → K x y = 0)
    (hH₀s : ∀ x y, (R < ‖x‖ ∨ R < ‖y‖) → H₀ x y = 0)
    (hKH : ∀ x y, η ≤ ‖x - y‖ → |K x y - H₀ x y| ≤ ε₁)
    (hcδ : ∀ x x' y, η ≤ ‖x - y‖ → ‖x - x'‖ ≤ δ → |H₀ x y - H₀ x' y| ≤ ε₁) :
    |∫ x, ∫ y, K x y ∂m ∂m - ∑ i ∈ bpzGridBox ⌈R / h⌉₊,
        m.real (bpzGridIdx h ⁻¹' {i}) * ∫ y, H₀ (bpzGridCorner h i) y ∂m| ≤
      2 * ε₁ * (m.real (Metric.closedBall 0 (2 * R + 1)) * m.real (Metric.closedBall 0 R)) +
        2 * C * bpzNearDiag (2 * R + 1) η m := by
  set S := bpzGridBox ⌈R / h⌉₊ with hS
  have hC : 0 ≤ C := (abs_nonneg _).trans (hKb 0 0)
  set Kt : ℂ → ℂ → ℝ := fun x y =>
    if bpzGridIdx h x ∈ S then H₀ (bpzGridCorner h (bpzGridIdx h x)) y else 0 with hKt
  have hKtm : Measurable (Function.uncurry Kt) := by
    have hc : Measurable (fun p : ℂ × ℂ => (bpzGridCorner h (bpzGridIdx h p.1), p.2)) := by
      have : Measurable (fun i : ℤ × ℤ => bpzGridCorner h i) := measurable_of_countable _
      exact (this.comp ((measurable_bpzGridIdx h).comp measurable_fst)).prodMk measurable_snd
    have hs : MeasurableSet {p : ℂ × ℂ | bpzGridIdx h p.1 ∈ S} :=
      ((measurable_bpzGridIdx h).comp measurable_fst) (Set.Finite.measurableSet S.finite_toSet)
    exact Measurable.ite hs (hH₀m.comp hc) measurable_const
  have hKtb : ∀ x y, |Kt x y| ≤ C := by
    intro x y
    simp only [hKt]
    split_ifs
    · exact hH₀b _ _
    · simpa using hC
  have hsum : ∑ i ∈ S, m.real (bpzGridIdx h ⁻¹' {i}) * ∫ y, H₀ (bpzGridCorner h i) y ∂m =
      ∫ x, ∫ y, Kt x y ∂m ∂m := by
    rw [← integral_bpzGrid_step h S (fun i => ∫ y, H₀ (bpzGridCorner h i) y ∂m)]
    congr 1
    funext x
    simp only [hKt]
    split_ifs <;> simp
  set B₂ : Set ℂ := Metric.closedBall 0 (2 * R + 1)
  set B : Set ℂ := Metric.closedBall 0 R
  set Bd : ℂ → ℂ → ℝ := fun x y =>
    2 * ε₁ * (B₂.indicator 1 x * B.indicator 1 y) + 2 * C * bpzNearKernel (2 * R + 1) η x y
    with hBd
  have hBdm : Measurable (Function.uncurry Bd) := by
    have h1 : Measurable (fun p : ℂ × ℂ => B₂.indicator (1 : ℂ → ℝ) p.1) :=
      (measurable_one.indicator measurableSet_closedBall).comp measurable_fst
    have h2 : Measurable (fun p : ℂ × ℂ => B.indicator (1 : ℂ → ℝ) p.2) :=
      (measurable_one.indicator measurableSet_closedBall).comp measurable_snd
    exact ((h1.mul h2).const_mul _).add ((measurable_bpzNearKernel _ _).const_mul _)
  have hBdb : ∀ x y, |Bd x y| ≤ 2 * ε₁ + 2 * C := by
    intro x y
    have hi1 : B₂.indicator (1 : ℂ → ℝ) x ≤ 1 := Set.indicator_le_self' (fun _ _ => zero_le_one) x
    have hi2 : B.indicator (1 : ℂ → ℝ) y ≤ 1 := Set.indicator_le_self' (fun _ _ => zero_le_one) y
    have hi1' : 0 ≤ B₂.indicator (1 : ℂ → ℝ) x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hi2' : 0 ≤ B.indicator (1 : ℂ → ℝ) y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
    have hk := bpzNearKernel_le_one (2 * R + 1) η x y
    have hk' := bpzNearKernel_nonneg (2 * R + 1) η x y
    have hprod : B₂.indicator (1 : ℂ → ℝ) x * B.indicator 1 y ≤ 1 := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    simp only [hBd]
    nlinarith
  have hpt : ∀ x y, |K x y - Kt x y| ≤ Bd x y := by
    intro x y
    have hi1' : 0 ≤ B₂.indicator (1 : ℂ → ℝ) x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hi2' : 0 ≤ B.indicator (1 : ℂ → ℝ) y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
    have hk' := bpzNearKernel_nonneg (2 * R + 1) η x y
    have hBd0 : 0 ≤ Bd x y := by simp only [hBd]; positivity
    by_cases hy : R < ‖y‖
    · have h1 : K x y = 0 := hKs x y (Or.inr hy)
      have h2 : Kt x y = 0 := by
        simp only [hKt]
        split_ifs
        · exact hH₀s _ y (Or.inr hy)
        · rfl
      rw [h1, h2, sub_zero, abs_zero]; exact hBd0
    push Not at hy
    by_cases hxS : bpzGridIdx h x ∈ S
    · have hx2 : ‖x‖ ≤ 2 * R + 1 :=
        (norm_le_of_bpzGridIdx_mem_box hh hxS).trans (bpzGrid_box_radius hR hh hh1)
      have hKt' : Kt x y = H₀ (bpzGridCorner h (bpzGridIdx h x)) y := by
        simp only [hKt]; exact ite_eq_left hxS
      have hxc : ‖x - bpzGridCorner h (bpzGridIdx h x)‖ ≤ δ :=
        (norm_sub_bpzGridCorner_le hh x).trans hhδ
      have hi1 : B₂.indicator (1 : ℂ → ℝ) x = 1 :=
        Set.indicator_of_mem (by simpa [B₂] using hx2) _
      have hi2 : B.indicator (1 : ℂ → ℝ) y = 1 := Set.indicator_of_mem (by simpa [B] using hy) _
      rw [hKt']
      by_cases hη : η ≤ ‖x - y‖
      · have e1 := hKH x y hη
        have e2 := hcδ x (bpzGridCorner h (bpzGridIdx h x)) y hη hxc
        calc |K x y - H₀ (bpzGridCorner h (bpzGridIdx h x)) y|
            ≤ |K x y - H₀ x y| + |H₀ x y - H₀ (bpzGridCorner h (bpzGridIdx h x)) y| :=
              abs_sub_le _ _ _
          _ ≤ ε₁ + ε₁ := add_le_add e1 e2
          _ ≤ Bd x y := by
              simp only [hBd, hi1, hi2, mul_one]
              have : 0 ≤ 2 * C * bpzNearKernel (2 * R + 1) η x y := by positivity
              linarith
      · push Not at hη
        have hk : bpzNearKernel (2 * R + 1) η x y = 1 := by
          unfold bpzNearKernel
          rw [ite_eq_left ⟨hx2, by rw [dist_eq_norm, norm_sub_rev]; exact hη⟩]
        calc |K x y - H₀ (bpzGridCorner h (bpzGridIdx h x)) y|
            ≤ |K x y| + |H₀ (bpzGridCorner h (bpzGridIdx h x)) y| := abs_sub _ _
          _ ≤ C + C := add_le_add (hKb x y) (hH₀b _ y)
          _ ≤ Bd x y := by
              simp only [hBd, hk, hi1, hi2, mul_one]
              linarith
    · have hx : R < ‖x‖ := by
        by_contra hcon
        push Not at hcon
        exact hxS (bpzGridIdx_mem_box hh hcon)
      have h1 : K x y = 0 := hKs x y (Or.inl hx)
      have h2 : Kt x y = 0 := by simp only [hKt]; exact ite_eq_right hxS
      rw [h1, h2, sub_zero, abs_zero]; exact hBd0
  -- integrate the pointwise bound
  have hIK : Integrable (fun x => ∫ y, K x y ∂m) m := bpz_integrable_inner hKm hKb
  have hIKt : Integrable (fun x => ∫ y, Kt x y ∂m) m := bpz_integrable_inner hKtm hKtb
  have hdiff : ∫ x, ∫ y, K x y ∂m ∂m - ∫ x, ∫ y, Kt x y ∂m ∂m =
      ∫ x, ∫ y, (K x y - Kt x y) ∂m ∂m := by
    rw [← integral_sub hIK hIKt]
    congr 1
    funext x
    rw [integral_sub (bpz_integrable_slice hKm hKb x) (bpz_integrable_slice hKtm hKtb x)]
  have hdm : Measurable (Function.uncurry fun x y => K x y - Kt x y) := hKm.sub hKtm
  have hdb : ∀ x y, |K x y - Kt x y| ≤ 2 * C := fun x y =>
    (abs_sub _ _).trans (by linarith [hKb x y, hKtb x y])
  have hbound : |∫ x, ∫ y, (K x y - Kt x y) ∂m ∂m| ≤ ∫ x, ∫ y, Bd x y ∂m ∂m := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (integral_mono
      (bpz_integrable_inner hdm hdb).norm (bpz_integrable_inner hBdm hBdb) fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      (bpz_integrable_slice hdm hdb x).abs (bpz_integrable_slice hBdm hBdb x) fun y => hpt x y)
  have hBdint : ∫ x, ∫ y, Bd x y ∂m ∂m =
      2 * ε₁ * (m.real B₂ * m.real B) + 2 * C * bpzNearDiag (2 * R + 1) η m := by
    have hin : ∀ x, ∫ y, Bd x y ∂m =
        2 * ε₁ * (B₂.indicator 1 x * m.real B) +
          2 * C * ∫ y, bpzNearKernel (2 * R + 1) η x y ∂m := by
      intro x
      simp only [hBd]
      rw [integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_indicator_one measurableSet_closedBall]
      · exact ((integrable_const _).indicator measurableSet_closedBall).const_mul _ |>.const_mul _
      · exact (bpz_integrable_slice (measurable_bpzNearKernel _ _)
          (bpzNearKernel_abs_le _ _) x).const_mul _
    simp_rw [hin]
    rw [integral_add, integral_const_mul, integral_const_mul, integral_mul_const,
      integral_indicator_one measurableSet_closedBall]
    · rfl
    · exact ((((integrable_const (1 : ℝ)).indicator measurableSet_closedBall).mul_const
        _).const_mul _)
    · exact (bpz_integrable_inner (measurable_bpzNearKernel _ _)
        (bpzNearKernel_abs_le _ _)).const_mul _
  rw [hsum, hdiff]
  exact hbound.trans hBdint.le

end DOZZ.Proofs
