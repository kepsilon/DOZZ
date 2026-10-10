/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WeakConvGrid

/-! # Double integrals under weak convergence in probability

If finite random measures `μ n` converge weakly in probability to `μ₀` and `μ₀` almost surely has
no atoms, then double integrals of bounded kernels `H n` that converge uniformly away from the
diagonal to a kernel `H₀`, continuous in the first variable away from the diagonal, converge in
probability. The proof compares both sides with finite grid sums, which converge by the single
integral convergence; the error is a modulus-of-continuity term plus the near-diagonal mass,
which is small in probability because `μ₀` has no atoms. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℕ → Ω → Measure ℂ}
  {μ₀ : Ω → Measure ℂ}

namespace BPZWeakConv

theorem measurable_integral (hμ : BPZWeakConv P μ μ₀) {f : ℂ → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω => ∫ x, f x ∂μ n ω) :=
  (measurable_integral_measure hf).comp (hμ.meas n)

theorem measurable_integral₀ (hμ : BPZWeakConv P μ μ₀) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable (fun ω => ∫ x, f x ∂μ₀ ω) :=
  (measurable_integral_measure hf).comp hμ.meas₀

/-- Finite sums of products of single integrals converge in probability. -/
theorem conv_sum_mul [IsFiniteMeasure P] (hμ : BPZWeakConv P μ μ₀) {ι : Type*} (s : Finset ι)
    (f g : ι → ℂ → ℝ) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (C R : ι → ℝ) (hfb : ∀ i x, |f i x| ≤ C i) (hgb : ∀ i x, |g i x| ≤ C i)
    (hfs : ∀ i x, R i < ‖x‖ → f i x = 0) (hgs : ∀ i x, R i < ‖x‖ → g i x = 0) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, (∫ x, f i x ∂μ n ω) * ∫ x, g i x ∂μ n ω) atTop
      (fun ω => ∑ i ∈ s, (∫ x, f i x ∂μ₀ ω) * ∫ x, g i x ∂μ₀ ω) := by
  refine bpz_tendstoInMeasure_finset_sum s
    (fun i n => ((hμ.measurable_integral (hf i) n).mul
      (hμ.measurable_integral (hg i) n)).aestronglyMeasurable) fun i _ => ?_
  exact bpz_tendstoInMeasure_mul (fun n => (hμ.measurable_integral (hf i) n).aestronglyMeasurable)
    (fun n => (hμ.measurable_integral (hg i) n).aestronglyMeasurable)
    (hμ.conv (f i) (hf i) (C i) (R i) (hfb i) (hfs i))
    (hμ.conv (g i) (hg i) (C i) (R i) (hgb i) (hgs i))

end BPZWeakConv

theorem bpz_indicator_one_abs_le (A : Set ℂ) (x : ℂ) : |A.indicator (1 : ℂ → ℝ) x| ≤ 1 := by
  by_cases hx : x ∈ A
  · simp [hx]
  · simp [hx]

theorem bpz_indicator_one_eq_zero_of_subset {A : Set ℂ} {R : ℝ}
    (hA : A ⊆ Metric.closedBall 0 R) (x : ℂ) (hx : R < ‖x‖) : A.indicator (1 : ℂ → ℝ) x = 0 := by
  refine Set.indicator_of_notMem (fun hxA => ?_) _
  have := hA hxA
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

theorem bpzGrid_cell_subset (h : ℝ) (hh : 0 < h) (i : ℤ × ℤ) :
    bpzGridIdx h ⁻¹' {i} ⊆ Metric.closedBall 0 (‖bpzGridCorner h i‖ + 2 * h) := by
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have := norm_sub_bpzGridCorner_le hh x
  rw [hx] at this
  calc ‖x‖ = ‖(x - bpzGridCorner h i) + bpzGridCorner h i‖ := by ring_nf
    _ ≤ ‖x - bpzGridCorner h i‖ + ‖bpzGridCorner h i‖ := norm_add_le _ _
    _ ≤ 2 * h + ‖bpzGridCorner h i‖ := by linarith
    _ = ‖bpzGridCorner h i‖ + 2 * h := by ring

theorem bpz_ball_subset_closedBall (c : ℂ) (r : ℝ) :
    Metric.ball c r ⊆ Metric.closedBall 0 (‖c‖ + |r|) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - c) + c‖ := by ring_nf
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ |r| + ‖c‖ := by linarith [le_abs_self r]
    _ = ‖c‖ + |r| := by ring

/-- A real random variable times a scale tending to zero is small in probability. -/
theorem bpz_exists_scale_small [IsFiniteMeasure P] {W : Ω → ℝ} (hW : Measurable W) {s : ℝ}
    (hs : 0 < s) {t : ℝ≥0∞} (ht : 0 < t) :
    ∃ k : ℕ, P {ω | s ≤ |1 / ((k : ℝ) + 1) * W ω|} ≤ t := by
  have hconv := bpz_tendstoInMeasure_const_mul_of_tendsto (P := P)
    tendsto_one_div_add_atTop_nhds_zero_nat (f := fun _ => W) (f₀ := W)
    (fun _ => hW.aestronglyMeasurable)
    (tendstoInMeasure_of_tendsto_ae (fun _ => hW.aestronglyMeasurable)
      (Eventually.of_forall fun _ => tendsto_const_nhds))
  rw [tendstoInMeasure_iff_norm] at hconv
  have h := (ENNReal.tendsto_nhds_zero.1 (hconv s hs)) t ht
  obtain ⟨k, hk⟩ := h.exists
  refine ⟨k, le_trans (measure_mono fun ω hω => ?_) hk⟩
  simp only [Set.mem_ofPred_eq, zero_mul, sub_zero, Real.norm_eq_abs] at hω ⊢
  exact hω

namespace BPZWeakConv

/-- **Double integrals under weak convergence in probability.** Bounded kernels `H n` supported
in a ball, converging uniformly away from the diagonal to a kernel `H₀` that is uniformly
continuous in the first variable away from the diagonal, have double integrals converging in
probability, provided the limit measure has no atoms. -/
theorem tendstoInMeasure_double [IsProbabilityMeasure P] (hμ : BPZWeakConv P μ μ₀)
    (hatom : ∀ᵐ ω ∂P, ∀ x, μ₀ ω {x} = 0)
    (H : ℕ → ℂ → ℂ → ℝ) (H₀ : ℂ → ℂ → ℝ)
    (hHm : ∀ n, Measurable (Function.uncurry (H n))) (hH₀m : Measurable (Function.uncurry H₀))
    {C R : ℝ} (hR : 0 ≤ R) (hbd : ∀ n x y, |H n x y| ≤ C) (hbd₀ : ∀ x y, |H₀ x y| ≤ C)
    (hsupp : ∀ n x y, (R < ‖x‖ ∨ R < ‖y‖) → H n x y = 0)
    (hsupp₀ : ∀ x y, (R < ‖x‖ ∨ R < ‖y‖) → H₀ x y = 0)
    (hcont : ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x' y, η ≤ ‖x - y‖ →
      ‖x - x'‖ ≤ δ → |H₀ x y - H₀ x' y| ≤ ε)
    (hunif : ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x y, η ≤ ‖x - y‖ →
      |H n x y - H₀ x y| ≤ ε) :
    TendstoInMeasure P (fun n ω => ∫ x, ∫ y, H n x y ∂μ n ω ∂μ n ω) atTop
      (fun ω => ∫ x, ∫ y, H₀ x y ∂μ₀ ω ∂μ₀ ω) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbd₀ 0 0)
  set ρ₂ : ℝ := 2 * R + 1 with hρ₂
  set ρ₃ : ℝ := 2 * ρ₂ + 1 with hρ₃
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  -- the near-diagonal masses of the limit tend to zero in measure
  set ND : ℕ → Ω → ℝ := fun k ω => bpzNearDiag ρ₃ (1 / ((k : ℝ) + 1)) (μ₀ ω) with hND
  have hNDm : ∀ k, Measurable (ND k) := fun k =>
    bpz_measurable_double_integral hμ.meas₀ hμ.fin₀ hμ.meas₀ hμ.fin₀ _
      (measurable_bpzNearKernel _ _)
  have hNDconv : TendstoInMeasure P ND atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun k => (hNDm k).aestronglyMeasurable) ?_
    filter_upwards [hatom] with ω hω
    have := hμ.fin₀ ω
    exact tendsto_bpzNearDiag_zero (μ₀ ω) hω ρ₃
  set Wv : Ω → ℝ := fun ω => (μ₀ ω).real (Metric.closedBall 0 ρ₃) with hWv
  have hWm : Measurable Wv :=
    ((Measure.measurable_coe measurableSet_closedBall).comp hμ.meas₀).ennreal_toReal
  refine bpz_tendstoInMeasure_of_approx fun ε hε => ?_
  set C' : ℝ := C + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  -- choose the near-diagonal width
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, P {ω | ε / (8 * C') ≤ ND k₁ ω} ≤ ENNReal.ofReal (ε / 4) := by
    rw [tendstoInMeasure_iff_norm] at hNDconv
    have h := (ENNReal.tendsto_nhds_zero.1 (hNDconv (ε / (8 * C')) (by positivity)))
      (ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.2 (by positivity))
    obtain ⟨k, hk⟩ := h.exists
    refine ⟨k, le_trans (measure_mono fun ω hω => ?_) hk⟩
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    exact hω.trans (le_abs_self _)
  -- choose the uniform tolerance
  obtain ⟨k₂, hk₂⟩ := bpz_exists_scale_small (P := P) (hWm.mul hWm) (s := ε / 8) (by positivity)
    (t := ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.2 (by positivity))
  set t : ℝ := 1 / ((k₁ : ℝ) + 1) with ht
  have ht0 : 0 < t := by positivity
  set η : ℝ := t / 2 with hη
  have hη0 : 0 < η := by positivity
  set ε₁ : ℝ := 1 / ((k₂ : ℝ) + 1) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ, hcδ⟩ := hcont η hη0 ε₁ hε₁0
  set h : ℝ := min (min (η / 4) (1 / 4)) (δ / 2) with hhdef
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hhη : h ≤ η / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hhδ : 2 * h ≤ δ := by have := min_le_right (min (η / 4) (1 / 4)) (δ / 2); linarith
  set S := bpzGridBox ⌈R / h⌉₊ with hS
  set S' := bpzGridBox ⌈ρ₂ / h⌉₊ with hS'
  set c := bpzGridCorner h with hc
  set cell : ℤ × ℤ → Set ℂ := fun i => bpzGridIdx h ⁻¹' {i} with hcell
  have hcellm : ∀ i, MeasurableSet (cell i) := measurableSet_bpzGridCell h
  -- the approximating grid sums
  set A : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ S, (μ n ω).real (cell i) * ∫ y, H₀ (c i) y ∂μ n ω
    with hA
  set A₀ : Ω → ℝ := fun ω => ∑ i ∈ S, (μ₀ ω).real (cell i) * ∫ y, H₀ (c i) y ∂μ₀ ω with hA₀
  have hslice : ∀ i, Measurable (fun y => H₀ (c i) y) := fun i =>
    hH₀m.comp (measurable_const.prodMk measurable_id)
  have hAconv : TendstoInMeasure P A atTop A₀ := by
    have h := hμ.conv_sum_mul S (fun i => (cell i).indicator 1) (fun i y => H₀ (c i) y)
      (fun i => measurable_one.indicator (hcellm i)) hslice (fun _ => max 1 C)
      (fun i => max (‖c i‖ + 2 * h) R)
      (fun i x => (bpz_indicator_one_abs_le _ x).trans (le_max_left _ _))
      (fun i x => (hbd₀ _ x).trans (le_max_right _ _))
      (fun i x hx => bpz_indicator_one_eq_zero_of_subset (bpzGrid_cell_subset h hh0 i) x
        (lt_of_le_of_lt (le_max_left _ _) hx))
      (fun i x hx => hsupp₀ _ x (Or.inr (lt_of_le_of_lt (le_max_right _ _) hx)))
    simp only [integral_indicator_one (hcellm _)] at h
    exact h
  -- the near-diagonal grid sums
  set G : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S', (μ n ω).real (cell i) * (μ n ω).real (Metric.ball (c i) (η + 2 * h)) with hG
  set G₀ : Ω → ℝ := fun ω =>
    ∑ i ∈ S', (μ₀ ω).real (cell i) * (μ₀ ω).real (Metric.ball (c i) (η + 2 * h)) with hG₀
  have hGconv : TendstoInMeasure P G atTop G₀ := by
    have h := hμ.conv_sum_mul S' (fun i => (cell i).indicator 1)
      (fun i => (Metric.ball (c i) (η + 2 * h)).indicator 1)
      (fun i => measurable_one.indicator (hcellm i))
      (fun i => measurable_one.indicator measurableSet_ball) (fun _ => 1)
      (fun i => max (‖c i‖ + 2 * h) (‖c i‖ + |η + 2 * h|))
      (fun i x => bpz_indicator_one_abs_le _ x) (fun i x => bpz_indicator_one_abs_le _ x)
      (fun i x hx => bpz_indicator_one_eq_zero_of_subset (bpzGrid_cell_subset h hh0 i) x
        (lt_of_le_of_lt (le_max_left _ _) hx))
      (fun i x hx => bpz_indicator_one_eq_zero_of_subset (bpz_ball_subset_closedBall _ _) x
        (lt_of_le_of_lt (le_max_right _ _) hx))
    simp only [integral_indicator_one (hcellm _), integral_indicator_one measurableSet_ball] at h
    exact h
  have hmassm : ∀ (s : Set ℂ), MeasurableSet s → ∀ n, Measurable fun ω => (μ n ω).real s :=
    fun s hs n => ((Measure.measurable_coe hs).comp (hμ.meas n)).ennreal_toReal
  have hmassm₀ : ∀ (s : Set ℂ), MeasurableSet s → Measurable fun ω => (μ₀ ω).real s :=
    fun s hs => ((Measure.measurable_coe hs).comp hμ.meas₀).ennreal_toReal
  have hGm : ∀ n, Measurable (G n) := fun n => Finset.measurable_sum _ fun i _ =>
    (hmassm _ (hcellm i) n).mul (hmassm _ measurableSet_ball n)
  -- the error bounds
  set B₂ : Set ℂ := Metric.closedBall 0 ρ₂
  set B : Set ℂ := Metric.closedBall 0 R
  set Bn : ℕ → Ω → ℝ := fun n ω =>
    2 * ε₁ * ((μ n ω).real B₂ * (μ n ω).real B) + 2 * C * G n ω with hBn
  set B₀ : Ω → ℝ := fun ω => 2 * ε₁ * ((μ₀ ω).real B₂ * (μ₀ ω).real B) + 2 * C * G₀ ω
    with hB₀
  have hBconv : TendstoInMeasure P Bn atTop B₀ := by
    have hm1 : ∀ n, Measurable fun ω => (μ n ω).real B₂ * (μ n ω).real B := fun n =>
      (hmassm _ measurableSet_closedBall n).mul (hmassm _ measurableSet_closedBall n)
    have h1 : TendstoInMeasure P (fun n ω => (μ n ω).real B₂ * (μ n ω).real B) atTop
        (fun ω => (μ₀ ω).real B₂ * (μ₀ ω).real B) := by
      have h := hμ.conv_sum_mul {()} (fun _ => B₂.indicator 1) (fun _ => B.indicator 1)
        (fun _ => measurable_one.indicator measurableSet_closedBall)
        (fun _ => measurable_one.indicator measurableSet_closedBall) (fun _ => 1)
        (fun _ => max ρ₂ R) (fun _ x => bpz_indicator_one_abs_le _ x)
        (fun _ x => bpz_indicator_one_abs_le _ x)
        (fun _ x hx => bpz_indicator_one_eq_zero_of_subset subset_rfl x
          (lt_of_le_of_lt (le_max_left _ _) hx))
        (fun _ x hx => bpz_indicator_one_eq_zero_of_subset subset_rfl x
          (lt_of_le_of_lt (le_max_right _ _) hx))
      have hB₂m : MeasurableSet B₂ := measurableSet_closedBall
      have hBm : MeasurableSet B := measurableSet_closedBall
      simp only [Finset.sum_singleton, integral_indicator_one hB₂m, integral_indicator_one hBm] at h
      exact h
    exact bpz_tendstoInMeasure_add
      (fun n => ((hm1 n).const_mul _).aestronglyMeasurable)
      (fun n => ((hGm n).const_mul _).aestronglyMeasurable)
      (bpz_tendstoInMeasure_const_mul_of_tendsto tendsto_const_nhds
        (fun n => (hm1 n).aestronglyMeasurable) h1)
      (bpz_tendstoInMeasure_const_mul_of_tendsto tendsto_const_nhds
        (fun n => (hGm n).aestronglyMeasurable) hGconv)
  -- the limit bound in terms of the chosen small quantities
  have hB₀le : ∀ ω, B₀ ω ≤ 2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω := by
    intro ω
    have := hμ.fin₀ ω
    have hsub2 : B₂ ⊆ Metric.closedBall 0 ρ₃ :=
      Metric.closedBall_subset_closedBall (by linarith)
    have hsub : B ⊆ Metric.closedBall 0 ρ₃ :=
      Metric.closedBall_subset_closedBall (by linarith)
    have hm2 : (μ₀ ω).real B₂ * (μ₀ ω).real B ≤ Wv ω * Wv ω :=
      mul_le_mul (measureReal_mono hsub2) (measureReal_mono hsub) measureReal_nonneg
        measureReal_nonneg
    have hgrid : G₀ ω ≤ ND k₁ ω := by
      have h1 := grid_le_bpzNearDiag (μ₀ ω) (t := η) (N := ⌈ρ₂ / h⌉₊) hh0
        (ρ := ρ₃) (bpzGrid_box_radius hρ₂0 hh0 hh1)
      have h2 : bpzNearDiag ρ₃ (η + 4 * h) (μ₀ ω) ≤ bpzNearDiag ρ₃ t (μ₀ ω) :=
        bpzNearDiag_mono le_rfl (by linarith) _
      exact h1.trans h2
    simp only [hB₀]
    have h1 := mul_le_mul_of_nonneg_left hgrid (mul_nonneg zero_le_two hC)
    have h2 := mul_le_mul_of_nonneg_left hm2 (mul_nonneg zero_le_two hε₁0.le)
    linarith only [h1, h2]
  -- the probability bound on the limit
  have hP₀ : P {ω | ε / 2 ≤ 2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω} ≤
      ENNReal.ofReal (ε / 2) := by
    have hsub : {ω | ε / 2 ≤ 2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω} ⊆
        {ω | ε / 8 ≤ |ε₁ * (Wv ω * Wv ω)|} ∪ {ω | ε / (8 * C') ≤ ND k₁ ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hND0 : 0 ≤ ND k₁ ω := by
        have := hμ.fin₀ ω; exact bpzNearDiag_nonneg _ _ _
      have h1' : ε₁ * (Wv ω * Wv ω) < ε / 8 := lt_of_le_of_lt (le_abs_self _) h1
      have h2' : 2 * C * ND k₁ ω < ε / 4 := by
        have : C * ND k₁ ω ≤ C' * ND k₁ ω := mul_le_mul_of_nonneg_right (by linarith) hND0
        have h3 : C' * ND k₁ ω < C' * (ε / (8 * C')) := mul_lt_mul_of_pos_left h2 hC'0
        have h4 : C' * (ε / (8 * C')) = ε / 8 := by field_simp
        linarith
      linarith
    calc P {ω | ε / 2 ≤ 2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω}
        ≤ P ({ω | ε / 8 ≤ |ε₁ * (Wv ω * Wv ω)|} ∪ {ω | ε / (8 * C') ≤ ND k₁ ω}) :=
          measure_mono hsub
      _ ≤ P {ω | ε / 8 ≤ |ε₁ * (Wv ω * Wv ω)|} + P {ω | ε / (8 * C') ≤ ND k₁ ω} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := add_le_add hk₂ hk₁
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  refine ⟨A, A₀, hAconv, ?_, ?_⟩
  · -- the sequence side
    obtain ⟨n₀, hn₀⟩ := (hunif η hη0 ε₁ hε₁0).exists_forall_of_atTop
    set E : ℕ → Ω → ℝ := fun n ω => if n₀ ≤ n then
      (∫ x, ∫ y, H n x y ∂μ n ω ∂μ n ω) - A n ω else 0 with hE
    have hEB : ∀ n, ∀ᵐ ω ∂P, |E n ω| ≤ Bn n ω := by
      intro n
      refine Eventually.of_forall fun ω => ?_
      have := hμ.fin n ω
      have hBn0 : 0 ≤ Bn n ω := by
        have h1 : 0 ≤ G n ω := Finset.sum_nonneg fun i _ =>
          mul_nonneg measureReal_nonneg measureReal_nonneg
        simp only [hBn]
        have : 0 ≤ (μ n ω).real B₂ * (μ n ω).real B :=
          mul_nonneg measureReal_nonneg measureReal_nonneg
        exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two hε₁0.le) this)
          (mul_nonneg (mul_nonneg zero_le_two hC) h1)
      simp only [hE]
      split_ifs with hn
      · have herr := bpz_double_grid_error (μ n ω) (H n) H₀ (hHm n) hH₀m hR hh0 hh1 hhδ
          hε₁0.le (hbd n) hbd₀ (hsupp n) hsupp₀ (hn₀ n hn) hcδ
        have hnd := bpzNearDiag_le_grid (μ n ω) (ρ := ρ₂) (t := η) hh0
        calc _ ≤ 2 * ε₁ * ((μ n ω).real B₂ * (μ n ω).real B) +
              2 * C * bpzNearDiag ρ₂ η (μ n ω) := herr
          _ ≤ Bn n ω := by
              simp only [hBn, hG]
              have := mul_le_mul_of_nonneg_left hnd (mul_nonneg zero_le_two hC)
              linarith only [this]
      · rw [abs_zero]; exact hBn0
    have hfin := bpz_eventually_measure_le_of_le_tendstoInMeasure hBconv hEB hε
      (lt_of_le_of_lt ((measure_mono fun ω hω => (by
        simp only [Set.mem_ofPred_eq] at hω ⊢
        exact hω.trans (hB₀le ω))).trans hP₀)
        (ENNReal.ofReal_lt_ofReal_iff hε |>.2 (by linarith)))
    filter_upwards [hfin, eventually_ge_atTop n₀] with n hn hn'
    simp only [hE, ite_eq_left hn'] at hn
    exact hn
  · -- the limit side
    have hle : ∀ ω, |(∫ x, ∫ y, H₀ x y ∂μ₀ ω ∂μ₀ ω) - A₀ ω| ≤
        2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω := by
      intro ω
      have := hμ.fin₀ ω
      have herr := bpz_double_grid_error (μ₀ ω) H₀ H₀ hH₀m hH₀m hR hh0 hh1 hhδ hε₁0.le hbd₀ hbd₀
        hsupp₀ hsupp₀ (fun x y _ => by rw [sub_self, abs_zero]; exact hε₁0.le) hcδ
      have hnd : bpzNearDiag ρ₂ η (μ₀ ω) ≤ ND k₁ ω :=
        bpzNearDiag_mono (by linarith) (by linarith) _
      have hsub2 : B₂ ⊆ Metric.closedBall 0 ρ₃ :=
        Metric.closedBall_subset_closedBall (by linarith)
      have hsub : B ⊆ Metric.closedBall 0 ρ₃ :=
        Metric.closedBall_subset_closedBall (by linarith)
      have hm2 : (μ₀ ω).real B₂ * (μ₀ ω).real B ≤ Wv ω * Wv ω :=
        mul_le_mul (measureReal_mono hsub2) (measureReal_mono hsub) measureReal_nonneg
          measureReal_nonneg
      calc _ ≤ 2 * ε₁ * ((μ₀ ω).real B₂ * (μ₀ ω).real B) + 2 * C * bpzNearDiag ρ₂ η (μ₀ ω) :=
            herr
        _ ≤ 2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω := by
            have h1 := mul_le_mul_of_nonneg_left hnd (mul_nonneg zero_le_two hC)
            have h2 := mul_le_mul_of_nonneg_left hm2 (mul_nonneg zero_le_two hε₁0.le)
            linarith only [h1, h2]
    calc P {ω | ε ≤ |(∫ x, ∫ y, H₀ x y ∂μ₀ ω ∂μ₀ ω) - A₀ ω|}
        ≤ P {ω | ε / 2 ≤ 2 * (ε₁ * (Wv ω * Wv ω)) + 2 * C * ND k₁ ω} :=
          measure_mono fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω ⊢
            linarith [hle ω]
      _ ≤ ENNReal.ofReal (ε / 2) := hP₀
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

end BPZWeakConv

end DOZZ.Proofs
