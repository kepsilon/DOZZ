/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy of parametric integrals

If `f : ℂ → Ω → ℂ` is such that almost every section `z ↦ f z ω` is holomorphic on an open set
`U`, and `‖f ζ ω‖` is dominated, uniformly for `ζ` in a closed disc around each point of `U`, by an
integrable function of `ω`, then every section `f z` is integrable and
`z ↦ ∫ f z ω ∂P` is holomorphic on `U`.

The proof applies the Cauchy estimate on a disc of half the radius to bound the `z`-derivative of
the integrand by `2 g ω / r`, and then differentiates under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The measurability of the derivative in `ω` is
obtained as an almost everywhere limit of difference quotients.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric

namespace DOZZ.Proofs

/-- Under the same local domination every section is integrable. -/
theorem integrable_of_locally_dominated {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {U : Set ℂ} (f : ℂ → Ω → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (f z) P)
    (hdom : ∀ z ∈ U, ∃ r > 0, closedBall z r ⊆ U ∧ ∃ g : Ω → ℝ, Integrable g P ∧
      ∀ᵐ ω ∂P, ∀ ζ ∈ closedBall z r, ‖f ζ ω‖ ≤ g ω) :
    ∀ z ∈ U, Integrable (f z) P := by
  intro z hz
  obtain ⟨r, hr, -, g, hg, hbound⟩ := hdom z hz
  refine hg.mono' (hmeas z hz) ?_
  filter_upwards [hbound] with ω hω using hω z (mem_closedBall_self hr.le)

/-- The `z`-derivative at `z₀` of a family which is measurable in `ω` for `z` near `z₀`, and
almost surely differentiable at `z₀`, is almost everywhere strongly measurable: it is the limit
of the difference quotients along the sequence `z₀ + r / (2 (n + 1))`. -/
theorem aestronglyMeasurable_deriv_of_ae_differentiableAt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℂ → Ω → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hmeas : ∀ z ∈ ball z₀ r, AEStronglyMeasurable (f z) P)
    (hdiff : ∀ᵐ ω ∂P, DifferentiableAt ℂ (fun z => f z ω) z₀) :
    AEStronglyMeasurable (fun ω => deriv (fun z => f z ω) z₀) P := by
  obtain ⟨t, ht_pos, ht_le, ht_zero⟩ : ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ (∀ n, t n ≤ r / 2) ∧
      Tendsto t atTop (𝓝 0) := by
    refine ⟨fun n => r / 2 / ((n : ℝ) + 1), fun n => by positivity, fun n => ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), half_pos hr]
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / 2)
      rw [mul_zero] at h
      exact h.congr fun n => mul_one_div _ _
  have hh_zero : Tendsto (fun n => (t n : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).comp ht_zero
    · simpa using (ht_pos n).ne'
  have hh_mem : ∀ n, z₀ + (t n : ℂ) ∈ ball z₀ r := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (ht_pos n).le]
    linarith [ht_le n, half_pos hr]
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n ω => ((t n : ℂ))⁻¹ • (f (z₀ + (t n : ℂ)) ω - f z₀ ω)) (fun n => ?_) ?_
  · exact ((hmeas _ (hh_mem n)).sub (hmeas z₀ (mem_ball_self hr))).const_smul ((t n : ℂ)⁻¹)
  · filter_upwards [hdiff] with ω hω
    exact hω.hasDerivAt.tendsto_slope_zero.comp hh_zero

/-- **Holomorphy of a parametric integral** under local uniform domination: if almost every
section `z ↦ f z ω` is holomorphic on the open set `U` and `‖f‖` is dominated near each point of
`U` by an integrable function, then `z ↦ ∫ f z ω ∂P` is holomorphic on `U`. -/
theorem differentiableOn_integral_of_locally_dominated {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {U : Set ℂ} (hU : IsOpen U) (f : ℂ → Ω → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (f z) P)
    (hdiff : ∀ᵐ ω ∂P, DifferentiableOn ℂ (fun z => f z ω) U)
    (hdom : ∀ z ∈ U, ∃ r > 0, closedBall z r ⊆ U ∧ ∃ g : Ω → ℝ, Integrable g P ∧
      ∀ᵐ ω ∂P, ∀ ζ ∈ closedBall z r, ‖f ζ ω‖ ≤ g ω) :
    DifferentiableOn ℂ (fun z => ∫ ω, f z ω ∂P) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hrU, g, hg, hbound⟩ := hdom z₀ hz₀
  have hhalf : 0 < r / 2 := half_pos hr
  have hballU : ball z₀ (r / 2) ⊆ U :=
    (ball_subset_ball (by linarith)).trans (ball_subset_closedBall.trans hrU)
  have hderiv_bound : ∀ᵐ ω ∂P, ∀ ζ ∈ ball z₀ (r / 2),
      ‖deriv (fun z => f z ω) ζ‖ ≤ g ω / (r / 2) := by
    filter_upwards [hdiff, hbound] with ω hω hωg ζ hζ
    have hsub : closedBall ζ (r / 2) ⊆ closedBall z₀ r :=
      closedBall_subset_closedBall' (by rw [mem_ball] at hζ; linarith)
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf
      (hω.diffContOnCl_ball (hsub.trans hrU))
      fun w hw => hωg w (hsub (sphere_subset_closedBall hw))
  have hderiv_diff : ∀ᵐ ω ∂P, ∀ ζ ∈ ball z₀ (r / 2),
      HasDerivAt (fun z => f z ω) (deriv (fun z => f z ω) ζ) ζ := by
    filter_upwards [hdiff] with ω hω ζ hζ
    exact (hω.differentiableAt (hU.mem_nhds (hballU hζ))).hasDerivAt
  have hF'_meas : AEStronglyMeasurable (fun ω => deriv (fun z => f z ω) z₀) P :=
    aestronglyMeasurable_deriv_of_ae_differentiableAt hr
      (fun z hz => hmeas z (hrU (ball_subset_closedBall hz)))
      (hdiff.mono fun ω hω => hω.differentiableAt (hU.mem_nhds hz₀))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (F := f) (x₀ := z₀)
    (s := ball z₀ (r / 2)) (bound := fun ω => g ω / (r / 2)) (ball_mem_nhds z₀ hhalf)
    (eventually_of_mem (hU.mem_nhds hz₀) hmeas)
    (integrable_of_locally_dominated P f hmeas hdom z₀ hz₀)
    (F' := fun z ω => deriv (fun w => f w ω) z) hF'_meas hderiv_bound (hg.div_const _) hderiv_diff
  exact key.2.differentiableAt.differentiableWithinAt

end DOZZ.Proofs

end
