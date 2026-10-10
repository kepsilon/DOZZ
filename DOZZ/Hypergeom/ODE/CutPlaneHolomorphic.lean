/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneLocalGluing

/-! The path-independent scalar endpoint is holomorphic on the principal cut plane. -/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- Extend the first component of the selected cut-plane endpoint state to a total function on ℂ.
Its values off the cut plane are immaterial. -/
noncomputable def gaussCutPlaneScalarState (a b c : ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ gaussCutPlane then
    (gaussCutPlaneContinuationState a b c ⟨z, hz⟩).1
  else 0

private theorem gaussCutPlaneScalarState_eq_picard_near
    (a b c : ℂ) (z : gaussCutPlane) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ r ≤ R / 2 ∧
      ∃ D : HolomorphicDiskSolution (gaussSystemOperator a b c) R,
        D.center = (z : ℂ) ∧ Metric.ball (z : ℂ) r ⊆ gaussCutPlane ∧
        ∀ w ∈ Metric.ball (z : ℂ) r,
          gaussCutPlaneScalarState a b c w = (D.solution w).1 := by
  obtain ⟨R, δ, hR, hδ, hδR, D, hcenter, hlocal⟩ :=
    gaussCutPlaneContinuationState_locally_eq_picard a b c z
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (gaussCutPlane_isOpen.mem_nhds z.property)
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  have hrδ : r ≤ δ := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  have hball : Metric.ball (z : ℂ) r ⊆ gaussCutPlane := by
    intro w hw
    exact hεball (Metric.ball_subset_ball hrε hw)
  refine ⟨R, r, hR, hr, le_trans hrδ hδR, D, hcenter, hball, ?_⟩
  intro w hw
  have hwcut := hball hw
  have hwδ : dist w (z : ℂ) < δ := lt_of_lt_of_le (Metric.mem_ball.mp hw) hrδ
  have hstate := hlocal ⟨w, hwcut⟩ hwδ
  dsimp [gaussCutPlaneScalarState]
  rw [dite_eq_left hwcut]
  exact congrArg Prod.fst hstate

/-- The first component of the path-independent cut-plane endpoint is holomorphic in the endpoint.
-/
theorem gaussCutPlaneScalarState_differentiableOn
    (a b c : ℂ) :
    DifferentiableOn ℂ (gaussCutPlaneScalarState a b c) gaussCutPlane := by
  intro z hz
  let z' : gaussCutPlane := ⟨z, hz⟩
  obtain ⟨R, r, hR, hr, hrR, D, hcenter, hball, hEq⟩ :=
    gaussCutPlaneScalarState_eq_picard_near a b c z'
  have hDmem : z ∈ Metric.ball D.center R := by
    rw [hcenter]
    exact Metric.mem_ball_self hR
  have hDAt : DifferentiableAt ℂ D.solution z := (D.derivative z hDmem).differentiableAt
  have hDat : DifferentiableAt ℂ (fun w => (D.solution w).1) z := hDAt.fst
  have hnear : gaussCutPlaneScalarState a b c =ᶠ[𝓝 z]
      (fun w => (D.solution w).1) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    exact hEq w hw
  exact (hDat.congr_of_eventuallyEq hnear).differentiableWithinAt

end DOZZ.Proofs
