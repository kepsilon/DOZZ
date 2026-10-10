/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.UniquenessEndpoints
public import DOZZ.Hypergeom.ODE.PicardSum

/-! Uniform-radius local solutions and the one-step disk-chain continuation operation. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic solution of `Y' = H Y` on one disk, with its center value recorded. -/
structure HolomorphicDiskSolution (H : ℂ → E →L[ℂ] E) (r : ℝ) where
  center : ℂ
  initial : E
  solution : ℂ → E
  solution_center : solution center = initial
  derivative : ∀ z ∈ Metric.ball center r,
    HasDerivAt solution (H z (solution z)) z

/-- The Picard construction gives a solution on the full prescribed disk when the coefficient
has a uniform bound there. -/
noncomputable def holomorphicDiskSolutionOfBound
    (c : ℂ) (r M : ℝ) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E)
    (hM : 0 ≤ M) (hbound : ∀ z ∈ Metric.ball c r, ‖H z‖ ≤ M) :
    HolomorphicDiskSolution H r :=
  ⟨c, y, holomorphicPicardSolution c r H hH y, by
      exact holomorphicPicardSolution_apply_center c r H hH y,
    fun z hz => holomorphicPicardSolution_hasDerivAt c r M H hH y hM hbound hz⟩

/-- Extend a disk solution to a nearby disk of the same radius. The two solutions agree on the
concentric half-radius disk around the new center, which is the overlap fact used in a finite
continuation chain. -/
noncomputable def extendHolomorphicDiskSolution
    (r M : ℝ) (H : ℂ → E →L[ℂ] E) (hM : 0 ≤ M)
    (D : HolomorphicDiskSolution H r) (d : ℂ)
    (hH : DifferentiableOn ℂ H (Metric.ball d r))
    (hbound : ∀ z ∈ Metric.ball d r, ‖H z‖ ≤ M) : HolomorphicDiskSolution H r :=
  holomorphicDiskSolutionOfBound d r M H hH (D.solution d)
    hM hbound

theorem extendHolomorphicDiskSolution_agrees
    (r M : ℝ) (H : ℂ → E →L[ℂ] E) (hM : 0 ≤ M)
    (D : HolomorphicDiskSolution H r) (d : ℂ)
    (hd : dist d D.center < r / 2)
    (hH : DifferentiableOn ℂ H (Metric.ball d r))
    (hbound : ∀ z ∈ Metric.ball d r, ‖H z‖ ≤ M) :
    ∀ z ∈ Metric.ball d (r / 2),
      D.solution z = (extendHolomorphicDiskSolution r M H hM D d hH hbound).solution z := by
  let D' := extendHolomorphicDiskSolution r M H hM D d hH hbound
  have hr : 0 < r := by
    have hdist : 0 ≤ dist d D.center := dist_nonneg
    linarith
  have hsub : Metric.ball d (r / 2) ⊆ Metric.ball D.center r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    calc
      dist z D.center ≤ dist z d + dist d D.center := dist_triangle z d D.center
      _ < r / 2 + r / 2 := add_lt_add_of_lt_of_le hz hd.le
      _ = r := by ring
  intro z hz
  have hboundHalf : ∀ w ∈ Metric.ball d (r / 2), ‖H w‖ ≤ M :=
    fun w hw => hbound w (Metric.ball_subset_ball (by linarith) hw)
  have hEq := holomorphic_linear_system_solution_unique_of_eq_at
    d (r / 2) M H hM hboundHalf
    (fun w hw => D.derivative w (hsub hw))
    (fun w hw => D'.derivative w (Metric.ball_subset_ball (by linarith) hw))
    (Metric.mem_ball_self (by linarith)) hz
    (by
      change D.solution d = holomorphicPicardSolution d r H hH (D.solution d) d
      rw [holomorphicPicardSolution_apply_center])
  exact hEq

end DOZZ.Proofs
