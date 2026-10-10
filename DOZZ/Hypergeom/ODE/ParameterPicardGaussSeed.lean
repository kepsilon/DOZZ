/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterPicardDerivativeTerms
public import DOZZ.Hypergeom.ODE.ParameterSpatialDerivative
public import DOZZ.Hypergeom.ODE.ParameterCompactBounds

/-! Local parameter differentiability of the Gauss-system Picard series seeded by a characterized
family at the ordinary-series point `1/2`. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The three complex Gauss parameters, in the order `(a,b,c)`. -/
abbrev GaussParam := ℂ × ℂ × ℂ

/-- The first-order state `(H,H')` of a characterized Gauss family at one spatial point. -/
noncomputable def gaussFamilyStateAt (H : ℂ → ℂ → ℂ → ℂ → ℂ) (z : ℂ) :
    GaussParam → ℂ × ℂ := fun p =>
  (H p.1 p.2.1 p.2.2 z,
    deriv (fun w => H p.1 p.2.1 p.2.2 w) z)

/-- The parameter derivative of the first-order Gauss state at a fixed spatial point. -/
noncomputable def gaussFamilyStateFDerivAt (H : ℂ → ℂ → ℂ → ℂ → ℂ) (z : ℂ) :
    GaussParam → GaussParam →L[ℂ] (ℂ × ℂ) := fun p =>
  fderiv ℂ (gaussFamilyStateAt H z) p

private theorem gaussRegularPlane_closedBall_half :
    Metric.closedBall ((1 / 2 : ℝ) : ℂ) (1 / 4 : ℝ) ⊆ gaussRegularPlane := by
  intro z hz
  constructor
  · intro hzero
    subst z
    norm_num [Metric.mem_closedBall, dist_eq_norm] at hz
  · intro hone
    subst z
    norm_num [Metric.mem_closedBall, dist_eq_norm] at hz

private theorem gaussParamOperator_deriv_continuousOn
    (p : GaussParam) :
    ContinuousOn (gaussParamOperatorFDeriv p)
      (Metric.ball ((1 / 2 : ℝ) : ℂ) (1 / 4 : ℝ)) := by
  exact (gaussSystemOperator_param_fderiv_continuousOn p).mono
    (fun z hz => gaussRegularPlane_closedBall_half (Metric.ball_subset_closedBall hz))


end DOZZ.Proofs
