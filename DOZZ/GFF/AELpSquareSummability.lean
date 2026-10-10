/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# DOZZ.GFF.AELpSquareSummability

Finite total second moment of a countable family implies almost-sure square summability.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ

/-- The L¹ size of the square of a scalar function is the square of its L² size. -/
theorem eLpNorm_sq_eq_eLpNorm_two_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun ω => (f ω) ^ 2) 1 μ = (eLpNorm f 2 μ) ^ 2 := by
  have hfun : (fun ω => (f ω) ^ 2) =ᵐ[μ] (fun ω => ‖f ω‖ ^ (2 : ℝ)) := by
    filter_upwards with ω
    simp [Real.norm_eq_abs, sq_abs]
  rw [eLpNorm_congr_ae hfun]
  simpa using eLpNorm_norm_rpow (p := (1 : ℝ≥0∞)) f hf (by norm_num : 0 < (2 : ℝ))

/-- If the sum of the L¹ norms of the squared coordinates is finite, then the coordinates are
square summable almost everywhere. -/
theorem ae_summable_sq_of_tsum_eLpNorm_sq_ne_top {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω} (f : ι → Ω → ℝ)
    (hfinite : ∑' i, eLpNorm (fun ω => (f i ω) ^ 2) 1 μ ≠ ∞) :
    ∀ᵐ ω ∂μ, Summable (fun i => (f i ω) ^ 2) := by
  have hsum := MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top
    (μ := μ) (p := (1 : ℝ≥0∞)) (by norm_num)
    (f := fun i ω => (f i ω) ^ 2) hfinite
  filter_upwards [hsum] with ω hω
  have hω' : Summable (fun i => |(f i ω) ^ 2|) := by
    simpa only [Real.norm_eq_abs] using hω
  exact hω'.congr fun i => abs_of_nonneg (sq_nonneg (f i ω))

end DOZZ

end
