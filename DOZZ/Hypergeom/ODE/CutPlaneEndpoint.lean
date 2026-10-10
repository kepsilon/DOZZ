/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneCanonicalPath

/-! A path-independent Gauss-system state at every point of the principal cut plane. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A chosen finite-chain continuation of the series initial state along the canonical path to
`z`. -/
noncomputable def gaussCutPlaneCanonicalContinuationLift (a b c : ℂ) (z : gaussCutPlane) :
    PathContinuationLift (gaussCutPlanePathFunction (gaussCutPlaneCanonicalPath z))
      (gaussSystemOperator a b c) (ordinaryHypergeometricState a b c (1 / 2 : ℂ)) :=
  Classical.choice (exists_gauss_cut_plane_canonical_continuation a b c z)

/-- The endpoint vector obtained by continuing the ordinary-series state to `z` in the cut plane.
-/
noncomputable def gaussCutPlaneContinuationState (a b c : ℂ) (z : gaussCutPlane) : ℂ × ℂ :=
  (gaussCutPlaneCanonicalContinuationLift a b c z).value 1

/-- Every finite-chain continuation to `z` along any cut-plane path has the selected endpoint
vector. -/
theorem gauss_cut_plane_continuation_path_endpoint_eq
    (a b c : ℂ) (z : gaussCutPlane)
    {p : Path gaussCutPlaneMidpoint z}
    (L : PathContinuationLift (gaussCutPlanePathFunction p)
      (gaussSystemOperator a b c) (ordinaryHypergeometricState a b c (1 / 2 : ℂ))) :
    L.value 1 = gaussCutPlaneContinuationState a b c z := by
  exact gauss_cut_plane_path_lifts_endpoint_eq a b c p
    (gaussCutPlaneCanonicalPath z) (ordinaryHypergeometricState a b c (1 / 2 : ℂ))
    L (gaussCutPlaneCanonicalContinuationLift a b c z)

end DOZZ.Proofs
