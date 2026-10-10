/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.UniquenessEndpoints
public import DOZZ.Hypergeom.ODE.PicardSum

/-! Composition of local continuation steps and compatibility around a small homotopy square. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Coefficient data for the local Picard solution on a disk centered at `c`. -/
structure LocalHolomorphicODEData (r M : ℝ) (H : ℂ → E →L[ℂ] E) (c : ℂ) where
  differentiable : DifferentiableOn ℂ H (Metric.ball c r)
  bounded : ∀ z ∈ Metric.ball c r, ‖H z‖ ≤ M

/-- Continue an initial value from the center of a coefficient disk to a point in that disk. -/
noncomputable def localPicardTransfer
    (r M : ℝ) (H : ℂ → E →L[ℂ] E) {c : ℂ}
    (D : LocalHolomorphicODEData r M H c) (y : E) (z : ℂ) : E :=
  holomorphicPicardSolution c r H D.differentiable y z

theorem localPicardTransfer_comp_eq
    (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (H : ℂ → E →L[ℂ] E) {c d e : ℂ}
    (Dc : LocalHolomorphicODEData r M H c)
    (Dd : LocalHolomorphicODEData r M H d)
    (hdc : dist d c < r / 4) (hec : dist e c < r / 4) (y : E) :
    localPicardTransfer r M H Dd
        (localPicardTransfer r M H Dc y d) e =
      localPicardTransfer r M H Dc y e := by
  have hde : dist e d < r / 2 := by
    have htri : dist e d ≤ dist e c + dist c d := dist_triangle e c d
    rw [dist_comm c d] at htri
    linarith
  have hballSubset : Metric.ball d (r / 2) ⊆ Metric.ball c r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    calc
      dist z c ≤ dist z d + dist d c := dist_triangle z d c
      _ < r / 2 + r / 4 := add_lt_add_of_lt_of_le hz hdc.le
      _ < r := by linarith
  have hboundHalf : ∀ z ∈ Metric.ball d (r / 2), ‖H z‖ ≤ M :=
    fun z hz => Dd.bounded z (Metric.ball_subset_ball (by linarith) hz)
  let F : ℂ → E := localPicardTransfer r M H Dc y
  let G : ℂ → E := localPicardTransfer r M H Dd (F d)
  have hF : ∀ z ∈ Metric.ball d (r / 2), HasDerivAt F (H z (F z)) z := by
    intro z hz
    exact holomorphicPicardSolution_hasDerivAt c r M H Dc.differentiable y hM
      Dc.bounded (z := z) (hballSubset hz)
  have hG : ∀ z ∈ Metric.ball d (r / 2), HasDerivAt G (H z (G z)) z := by
    intro z hz
    exact holomorphicPicardSolution_hasDerivAt d r M H Dd.differentiable (F d) hM
      Dd.bounded (z := z) (Metric.ball_subset_ball (by linarith) hz)
  have hstart : F d = G d := by
    simp [F, G, localPicardTransfer, holomorphicPicardSolution_apply_center]
  have he : e ∈ Metric.ball d (r / 2) := Metric.mem_ball.mpr hde
  have hEq := holomorphic_linear_system_solution_unique_of_eq_at
    d (r / 2) M H hM hboundHalf hF hG
    (Metric.mem_ball_self (by linarith)) he hstart
  simpa [F, G] using hEq.symm

theorem localPicardTransfer_square_commutes
    (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (H : ℂ → E →L[ℂ] E) {c cRight cUp cDiag : ℂ}
    (Dc : LocalHolomorphicODEData r M H c)
    (DRight : LocalHolomorphicODEData r M H cRight)
    (DUp : LocalHolomorphicODEData r M H cUp)
    (hRight : dist cRight c < r / 4)
    (hUp : dist cUp c < r / 4)
    (hDiag : dist cDiag c < r / 4) (y : E) :
    localPicardTransfer r M H DRight
        (localPicardTransfer r M H Dc y cRight) cDiag =
      localPicardTransfer r M H DUp
        (localPicardTransfer r M H Dc y cUp) cDiag := by
  calc
    localPicardTransfer r M H DRight
        (localPicardTransfer r M H Dc y cRight) cDiag =
        localPicardTransfer r M H Dc y cDiag :=
          localPicardTransfer_comp_eq r M hr hM H Dc DRight hRight hDiag y
    _ = localPicardTransfer r M H DUp
        (localPicardTransfer r M H Dc y cUp) cDiag :=
          (localPicardTransfer_comp_eq r M hr hM H Dc DUp hUp hDiag y).symm

end DOZZ.Proofs
