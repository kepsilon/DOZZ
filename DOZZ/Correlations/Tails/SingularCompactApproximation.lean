/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedCompactChaosLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Increasing compact tests for the full extended-real insertion singularity. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Regularize the inverse radial power while keeping the support of the compact test. -/
noncomputable def singularCompactTest (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (β : ℝ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ := by
  let F : ℂ → ℝ := fun x => f x * (max ‖x‖ (1 / ((n : ℝ)+1))) ^ (-β)
  have hcont : Continuous F := f.continuous.mul
    ((continuous_norm.max continuous_const).rpow_const (fun x => Or.inl (ne_of_gt
      (lt_of_lt_of_le (by positivity : 0 < 1 / ((n : ℝ)+1)) (le_max_right _ _)))))
  have hs : HasCompactSupport F := hfc.mul_right
  let hb := hcont.bounded_above_of_compact_support hs
  exact BoundedContinuousFunction.ofNormedAddCommGroup F hcont hb.choose hb.choose_spec

theorem singular_compact_test_support (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (β : ℝ) (n : ℕ) :
    tsupport (singularCompactTest f hfc β n : ℂ → ℝ) ⊆ tsupport (f : ℂ → ℝ) :=
  tsupport_mul_subset_left

theorem singular_compact_test_nonneg (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (hf : ∀ x, 0 ≤ f x) (β : ℝ) (n : ℕ) (x : ℂ) :
    0 ≤ singularCompactTest f hfc β n x :=
  mul_nonneg (hf x) (Real.rpow_nonneg (by positivity) _)

/-- The compact radial approximants increase, including at the insertion center. -/
theorem singular_compact_test_mono (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (hf : ∀ x, 0 ≤ f x) (β : ℝ) (hβ : 0 ≤ β) (x : ℂ) :
    Monotone (fun n => singularCompactTest f hfc β n x) := by
  intro n m hnm
  change f x * (max ‖x‖ (1 / ((n : ℝ)+1))) ^ (-β) ≤
    f x * (max ‖x‖ (1 / ((m : ℝ)+1))) ^ (-β)
  apply mul_le_mul_of_nonneg_left _ (hf x)
  apply Real.rpow_le_rpow_of_nonpos
    (lt_of_lt_of_le (by positivity : 0 < 1 / ((m : ℝ)+1)) (le_max_right _ _)) _ (neg_nonpos.mpr hβ)
  exact max_le_max le_rfl (one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hnm 1))

/-- The pointwise limit is the literal ENNReal inverse power, with no convention at zero
silently replacing its infinite value. -/
theorem singular_compact_test_tendsto (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (hf : ∀ x, 0 ≤ f x) (β : ℝ) (x : ℂ) :
    Tendsto (fun n => ENNReal.ofReal (singularCompactTest f hfc β n x)) atTop
      (𝓝 (ENNReal.ofReal (f x) * (ENNReal.ofReal ‖x‖) ^ (-β))) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hbase : Tendsto (fun n : ℕ => ENNReal.ofReal (max ‖x‖ (1 / ((n : ℝ)+1)))) atTop
      (𝓝 (ENNReal.ofReal ‖x‖)) := by
    simpa only [max_eq_left (norm_nonneg x), Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto _ |>.comp ((tendsto_const_nhds (x := ‖x‖)).max hδ)
  have hpow : Tendsto (fun n : ℕ =>
      (ENNReal.ofReal (max ‖x‖ (1 / ((n : ℝ)+1)))) ^ (-β)) atTop
      (𝓝 ((ENNReal.ofReal ‖x‖) ^ (-β))) :=
    ENNReal.continuous_rpow_const.tendsto (ENNReal.ofReal ‖x‖) |>.comp hbase
  have hprod := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (f x)) hpow
    (Or.inr ENNReal.ofReal_ne_top)
  convert hprod using 1
  funext n
  change ENNReal.ofReal (f x * (max ‖x‖ (1 / ((n : ℝ)+1))) ^ (-β)) = _
  rw [ENNReal.ofReal_mul (hf x), ENNReal.ofReal_rpow_of_pos
    (lt_of_lt_of_le (by positivity : 0 < 1 / ((n : ℝ)+1)) (le_max_right _ _))]

/-- Increasing radial truncations converge under the spatial integral, including infinite
singular masses. This is the singular-cutoff passage after the compact chaos law. -/
theorem singular_compact_lintegral_tendsto (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (hf : ∀ x, 0 ≤ f x) (β : ℝ) (hβ : 0 ≤ β)
    (μ : Measure ℂ) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (singularCompactTest f hfc β n x) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) * (ENNReal.ofReal ‖x‖) ^ (-β) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (ENNReal.measurable_ofReal.comp
      (singularCompactTest f hfc β n).continuous.measurable).aemeasurable)
    (ae_of_all _ fun x => ?_) (ae_of_all _ fun x =>
      singular_compact_test_tendsto f hfc hf β x)
  intro n m hnm
  exact ENNReal.ofReal_le_ofReal (singular_compact_test_mono f hfc hf β hβ x hnm)


end DOZZ.Proofs
