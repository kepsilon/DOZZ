/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives

/-! Normalized holomorphic primitives on disks for the Picard construction. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Choose the primitive of a holomorphic disk field normalized to have value `y` at `c`.
This is the primitive step used to define the local Picard iterates. -/
noncomputable def normalizedDiskPrimitive (c : ℂ) (r : ℝ) (f : ℂ → E) (y : E)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) : ℂ → E :=
  Classical.choose (hf.isExactOn_ball.with_val_at c y)

theorem normalizedDiskPrimitive_apply_center (c : ℂ) (r : ℝ) (f : ℂ → E) (y : E)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    normalizedDiskPrimitive c r f y hf c = y := by
  exact (Classical.choose_spec (hf.isExactOn_ball.with_val_at c y)).1

theorem hasDerivAt_normalizedDiskPrimitive {c z : ℂ} {r : ℝ} {f : ℂ → E} {y : E}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    HasDerivAt (normalizedDiskPrimitive c r f y hf) (f z) z := by
  exact (Classical.choose_spec (hf.isExactOn_ball.with_val_at c y)).2 z hz

theorem differentiableOn_normalizedDiskPrimitive (c : ℂ) (r : ℝ) (f : ℂ → E) (y : E)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    DifferentiableOn ℂ (normalizedDiskPrimitive c r f y hf) (Metric.ball c r) := by
  intro z hz
  exact (hasDerivAt_normalizedDiskPrimitive hf hz).differentiableAt.differentiableWithinAt

end DOZZ.Proofs
