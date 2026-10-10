/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.FourPointWard
public import DOZZ.FourPoint.BPZ.SoftUniform

/-! # A singular negative moment of the four-point mass

For `z ∉ {0, 1}` and `q ≥ 1`, `E[I^{-q} ∫ (1 + |x − z|^{-2}) k dM] < ∞`. Away from `z` the
integrand is a multiple of `k`, giving `E[I^{1-q}] < ∞`. Near `z` the weight is
`|x − z|^{γχ − 2}` times a bounded factor, and the rooted bound reduces the expectation to the
Lebesgue integral of `|x − z|^{γχ − 2}` over a disk, which is finite since `γχ > 0`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

theorem continuousOn_bpzBaseWeight :
    ContinuousOn (bpzBaseWeight γ χ α₁ α₂ α₃) {x | x ≠ 0 ∧ x ≠ 1} := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold bpzBaseWeight
  have h0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
  have h1 : ‖x - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx.2)
  exact ((continuous_norm.continuousAt.rpow_const (Or.inl h0)).mul
    ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.rpow_const
      (Or.inl h1))).mul
    (bpz_continuous_normPlus.continuousAt.rpow_const (Or.inl (bpz_normPlus_pos x).ne'))

/-- The base factor is bounded near a regular root. -/
theorem bpz_base_bdd_near {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall z r, bpzBaseWeight γ χ α₁ α₂ α₃ x ≤ C := by
  set r : ℝ := min ‖z‖ ‖z - 1‖ / 2 with hr
  have hz0' : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hz1' : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hr0 : 0 < r := by positivity
  have hsub : Metric.closedBall z r ⊆ {x | x ≠ 0 ∧ x ≠ 1} := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have hm1 := min_le_left ‖z‖ ‖z - 1‖
    have hm2 := min_le_right ‖z‖ ‖z - 1‖
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, zero_sub, norm_neg] at hx; linarith
    · rw [h, ← norm_neg, neg_sub] at hx; linarith
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    (continuousOn_bpzBaseWeight.mono hsub)
  refine ⟨r, hr0, max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x hx
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

theorem bpzSoftWeight_zero_norm (z x : ℂ) :
    bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x = ‖x - z‖ ^ (γ * χ) * bpzBaseWeight γ χ α₁ α₂ α₃ x := by
  unfold bpzSoftWeight
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, add_zero, Complex.normSq_eq_norm_sq,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  push_cast
  ring

theorem bpz_rpow_neg_mul_le_rpow_sub (x : ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    x ^ (-q) * x ≤ x ^ (-(q - 1)) := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rcases eq_or_ne x ⊤ with rfl | ht
  · rw [ENNReal.top_rpow_of_neg (by linarith), zero_mul]; exact zero_le
  · refine le_of_eq ?_
    calc x ^ (-q) * x = x ^ (-q) * x ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = x ^ (-q + 1) := (ENNReal.rpow_add _ _ h0 ht).symm
      _ = x ^ (-(q - 1)) := by ring_nf

/-- **A singular negative moment of the four-point mass.** -/
theorem bpz_singular_moment_lt_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hχ : 0 < χ) {q : ℝ} (hq1 : 1 ≤ q) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) *
      ∫⁻ x, ENNReal.ofReal ((1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) ∂M ω
        ∂P < ⊤ := by
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨r, hr0, CB, hCB0, hCB⟩ := bpz_base_bdd_near (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) hz0 hz1
  set k : ℂ → ℝ := bpzSoftWeight γ χ α₁ α₂ α₃ 0 z with hk
  have hkm : Measurable k := measurable_bpzSoftWeight 0 z
  have hk0 : ∀ x, 0 ≤ k x := bpzSoftWeight_nonneg 0 z
  set B : Set ℂ := Metric.closedBall z r with hB
  set f : ℂ → ℝ≥0∞ := B.indicator fun x => ENNReal.ofReal (CB * ‖x - z‖ ^ (γ * χ - 2)) with hf
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_id.sub measurable_const).norm.pow_const _))).indicator measurableSet_closedBall
  -- the pointwise splitting
  have hpt : ∀ x, ENNReal.ofReal ((1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) ≤
      ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * ENNReal.ofReal (k x) + f x := by
    intro x
    rcases eq_or_ne x z with rfl | hxz
    · have : k x = 0 := by
        rw [hk, bpzSoftWeight_zero_norm, sub_self, norm_zero,
          Real.zero_rpow (by positivity), zero_mul]
      rw [this, mul_zero, ENNReal.ofReal_zero]; exact zero_le
    have hxz' : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    by_cases hxB : x ∈ B
    · have hfx : f x = ENNReal.ofReal (CB * ‖x - z‖ ^ (γ * χ - 2)) := Set.indicator_of_mem hxB _
      have hsing : ‖x - z‖ ^ (-2 : ℝ) * k x ≤ CB * ‖x - z‖ ^ (γ * χ - 2) := by
        rw [hk, bpzSoftWeight_zero_norm, ← mul_assoc, ← Real.rpow_add hxz']
        rw [show (-2 : ℝ) + γ * χ = γ * χ - 2 by ring, mul_comm]
        exact mul_le_mul_of_nonneg_right (hCB x hxB) (Real.rpow_nonneg hxz'.le _)
      rw [hfx, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add
        (mul_nonneg (by positivity) (hk0 x)) (mul_nonneg hCB0 (Real.rpow_nonneg (norm_nonneg _) _))]
      apply ENNReal.ofReal_le_ofReal
      have : k x ≤ (1 + r ^ (-2 : ℝ)) * k x := by
        have := Real.rpow_nonneg hr0.le (-2 : ℝ)
        nlinarith [hk0 x]
      nlinarith
    · have hfx : f x = 0 := Set.indicator_of_notMem hxB _
      rw [hfx, add_zero, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hrx : r ≤ ‖x - z‖ := by
        rw [hB, Metric.mem_closedBall, dist_eq_norm, not_le] at hxB; exact hxB.le
      have : ‖x - z‖ ^ (-2 : ℝ) ≤ r ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hr0 hrx (by norm_num)
      exact mul_le_mul_of_nonneg_right (by linarith) (hk0 x)
  -- integrate over the chaos
  have hint : ∀ ω, ∫⁻ x, ENNReal.ofReal ((1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) ∂M ω ≤
      ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z + ∫⁻ x, f x ∂M ω := by
    intro ω
    calc _ ≤ ∫⁻ x, (ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * ENNReal.ofReal (k x) + f x) ∂M ω :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z +
            ∫⁻ x, f x ∂M ω := by
          rw [lintegral_add_right _ hfm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rfl
  -- the two expectations
  obtain ⟨Bq, hBq, hBqz⟩ := bpzMass_negMoment_uniform (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) P X hX hγ hγ2 M hM ‖z‖ (norm_nonneg z) (q - 1) (by linarith)
  obtain ⟨C, hC0, hCz⟩ := bpz_near_root_bound (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
    P X hX hγ hγ2 M hM (norm_nonneg z) hq0
  have hmeasI : AEMeasurable (fun ω => bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q)) P :=
    (gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (ENNReal.measurable_ofReal.comp hkm)).pow_const _
  have h1 : ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) *
      (ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z) ∂P < ⊤ := by
    calc _ = ENNReal.ofReal (1 + r ^ (-2 : ℝ)) *
          ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) * bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ∂P := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1; funext ω; ring
      _ ≤ ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * Bq := by
          gcongr
          calc _ ≤ ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-(q - 1)) ∂P :=
                lintegral_mono fun ω => bpz_rpow_neg_mul_le_rpow_sub _ hq1
            _ ≤ Bq := hBqz z le_rfl 0 le_rfl zero_le_one
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBq
  have h2 : ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) * ∫⁻ x, f x ∂M ω ∂P < ⊤ := by
    refine lt_of_le_of_lt (hCz z le_rfl 0 le_rfl zero_le_one f hfm) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hball : ∫⁻ x, f x ∂volume ≤ ENNReal.ofReal CB *
        ∫⁻ x in Metric.ball z (2 * r), ENNReal.ofReal (‖x - z‖ ^ (γ * χ - 2)) := by
      rw [hf, lintegral_indicator measurableSet_closedBall]
      calc ∫⁻ x in B, ENNReal.ofReal (CB * ‖x - z‖ ^ (γ * χ - 2))
          = ENNReal.ofReal CB * ∫⁻ x in B, ENNReal.ofReal (‖x - z‖ ^ (γ * χ - 2)) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1; funext x
            rw [ENNReal.ofReal_mul hCB0]
        _ ≤ _ := mul_le_mul_right (lintegral_mono_set
              (Metric.closedBall_subset_ball (x := z) (show r < 2 * r by linarith))) _
    refine lt_of_le_of_lt hball (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    exact lt_of_le_of_lt (bpz_lintegral_ball_rpow_le (by nlinarith [mul_pos hγ hχ])
      (by positivity) z) ENNReal.ofReal_lt_top
  calc _ ≤ ∫⁻ ω, (bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) *
        (ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z) +
        bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) * ∫⁻ x, f x ∂M ω) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← mul_add]
        gcongr
        exact hint ω
    _ = (∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) *
          (ENNReal.ofReal (1 + r ^ (-2 : ℝ)) * bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z) ∂P) +
        ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) * ∫⁻ x, f x ∂M ω ∂P := by
        refine lintegral_add_left' ?_ _
        exact hmeasI.mul (aemeasurable_const.mul (gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM
          _ (ENNReal.measurable_ofReal.comp hkm)))
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h1, h2⟩

end DOZZ.Proofs
