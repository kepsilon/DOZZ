/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.FourPointSingular

/-! # Near-root contributions to the softened four-point moments

Near a regular root `z₀`, the base factor of the four-point weight is bounded. For roots `z` within
`r/2` of `z₀` and any softening `0 ≤ ε ≤ 1`, the rooted bound shows that
`E[I_ε(z)^{-p} ∫_{|x - z₀| < r} base(x) |x - z|^β dM(x)]` is at most a constant times
`r^{β + 2}/(β + 2)` for every `β > -2`, uniformly in `z` and `ε`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The base factor restricted to the disk of radius `r` around `z₀`. -/
noncomputable def bpzNearWeight (γ χ α₁ α₂ α₃ : ℝ) (z₀ : ℂ) (r : ℝ) (x : ℂ) : ℝ :=
  if ‖x - z₀‖ < r then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0

/-- The base factor away from the disk of radius `r` around `z₀`. -/
noncomputable def bpzFarWeight (γ χ α₁ α₂ α₃ : ℝ) (z₀ : ℂ) (r : ℝ) (x : ℂ) : ℝ :=
  if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0


theorem bpzNearWeight_nonneg (z₀ : ℂ) (r : ℝ) (x : ℂ) :
    0 ≤ bpzNearWeight γ χ α₁ α₂ α₃ z₀ r x := by
  unfold bpzNearWeight; split_ifs
  · exact bpzBaseWeight_nonneg x
  · exact le_rfl


theorem measurable_bpzNearWeight (z₀ : ℂ) (r : ℝ) :
    Measurable (bpzNearWeight γ χ α₁ α₂ α₃ z₀ r) := by
  unfold bpzNearWeight
  exact Measurable.ite (measurableSet_lt (measurable_id.sub measurable_const).norm
    measurable_const) measurable_bpzBaseWeight measurable_const




/-- **Near-root expectation bound**, uniform in the root and the softening. -/
theorem bpz_near_expect_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {p : ℝ} (hp : 0 ≤ p) {z₀ : ℂ} (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ z : ℂ,
      ‖z - z₀‖ ≤ r / 2 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ β : ℝ, -2 < β →
        ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) *
            ∫⁻ x, ENNReal.ofReal (bpzNearWeight γ χ α₁ α₂ α₃ z₀ r x * ‖x - z‖ ^ β) ∂M ω ∂P ≤
          ENNReal.ofReal (C * (2 * Real.pi * (2 * r) ^ (β + 2) / (β + 2))) := by
  obtain ⟨r₁, hr₁, CB, hCB0, hCB⟩ := bpz_base_bdd_near (γ := γ) (χ := χ) (α₁ := α₁)
    (α₂ := α₂) (α₃ := α₃) hz0 hz1
  obtain ⟨Cn, hCn0, hCn⟩ := bpz_near_root_bound (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
    P X hX hγ hγ2 M hM (R := ‖z₀‖ + r₁) (by positivity) hp
  refine ⟨r₁, hr₁, Cn * CB, by positivity, fun r hr hrr₁ z hz ε hε0 hε1 β hβ => ?_⟩
  have hzR : ‖z‖ ≤ ‖z₀‖ + r₁ := by
    have := norm_le_norm_add_norm_sub' z z₀
    linarith
  set f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (bpzNearWeight γ χ α₁ α₂ α₃ z₀ r x * ‖x - z‖ ^ β)
    with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp
    ((measurable_bpzNearWeight z₀ r).mul ((measurable_id.sub measurable_const).norm.pow_const _))
  refine (hCn z hzR ε hε0 hε1 f hfm).trans ?_
  -- the Lebesgue integral
  have hpt : ∀ x, f x ≤ (Metric.ball z (2 * r)).indicator
      (fun x => ENNReal.ofReal (CB * ‖x - z‖ ^ β)) x := by
    intro x
    by_cases hx : ‖x - z₀‖ < r
    · have hxb : x ∈ Metric.ball z (2 * r) := by
        rw [Metric.mem_ball, dist_eq_norm]
        have := norm_sub_le_norm_sub_add_norm_sub x z₀ z
        rw [norm_sub_rev z₀ z] at this
        linarith
      rw [Set.indicator_of_mem hxb, hf]
      apply ENNReal.ofReal_le_ofReal
      unfold bpzNearWeight
      rw [ite_eq_left hx]
      have hxB : x ∈ Metric.closedBall z₀ r₁ := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      exact mul_le_mul_of_nonneg_right (hCB x hxB) (Real.rpow_nonneg (norm_nonneg _) _)
    · have h0 : f x = 0 := by
        simp only [hf, bpzNearWeight, hx, ↓reduceIte, zero_mul, ENNReal.ofReal_zero]
      rw [h0]; exact zero_le
  calc ENNReal.ofReal Cn * ∫⁻ x, f x ∂volume
      ≤ ENNReal.ofReal Cn * ∫⁻ x, (Metric.ball z (2 * r)).indicator
          (fun x => ENNReal.ofReal (CB * ‖x - z‖ ^ β)) x ∂volume :=
        mul_le_mul_right (lintegral_mono hpt) _
    _ = ENNReal.ofReal Cn * (ENNReal.ofReal CB *
          ∫⁻ x in Metric.ball z (2 * r), ENNReal.ofReal (‖x - z‖ ^ β)) := by
        rw [lintegral_indicator measurableSet_ball]
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext x
        rw [ENNReal.ofReal_mul hCB0]
    _ ≤ ENNReal.ofReal Cn * (ENNReal.ofReal CB *
          ENNReal.ofReal (2 * Real.pi * (2 * r) ^ (β + 2) / (β + 2))) := by
        gcongr
        exact bpz_lintegral_ball_rpow_le hβ (by positivity) z
    _ = ENNReal.ofReal (Cn * CB * (2 * Real.pi * (2 * r) ^ (β + 2) / (β + 2))) := by
        have h2 : 0 ≤ 2 * Real.pi * (2 * r) ^ (β + 2) / (β + 2) := by
          have : 0 < β + 2 := by linarith
          positivity
        rw [← ENNReal.ofReal_mul hCB0, ← ENNReal.ofReal_mul hCn0]
        congr 1
        ring

end DOZZ.Proofs
