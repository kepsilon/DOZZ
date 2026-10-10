/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlanePathIndependence
public import DOZZ.Hypergeom.ODE.SeriesSeed

/-! Canonical paths from the ordinary-series basepoint to points of the principal cut plane. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- The regular basepoint at which the ordinary Gauss series initializes continuation. -/
noncomputable def gaussCutPlaneMidpoint : gaussCutPlane :=
  ⟨(1 / 2 : ℂ), by change _ ∨ _; right; norm_num⟩

/-- The straight path in the star-convex cut plane from `1/2` to `z`. -/
noncomputable def gaussCutPlaneCanonicalPath (z : gaussCutPlane) :
    Path gaussCutPlaneMidpoint z := by
  let g : unitInterval → ℂ := fun t =>
    (1 - (t : ℝ)) • (1 / 2 : ℂ) + (t : ℝ) • (z : ℂ)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hgmem : ∀ t, g t ∈ gaussCutPlane := by
    intro t
    change (1 - (t : ℝ)) • (1 / 2 : ℂ) + (t : ℝ) • (z : ℂ) ∈ gaussCutPlane
    exact gaussCutPlane_starConvex z.property
      (a := 1 - (t : ℝ)) (b := (t : ℝ))
      (by linarith [t.property.2]) t.property.1 (by ring)
  let f : C(unitInterval, gaussCutPlane) :=
    ⟨fun t => ⟨g t, hgmem t⟩, hg.subtype_mk hgmem⟩
  refine ⟨f, ?_, ?_⟩
  · apply Subtype.ext
    simp [f, g, gaussCutPlaneMidpoint]
  · apply Subtype.ext
    simp [f, g]

/-- The canonical path function is continuous on its real parameter interval. -/
theorem gaussCutPlaneCanonicalPath_continuousOn (z : gaussCutPlane) :
    ContinuousOn (gaussCutPlanePathFunction (gaussCutPlaneCanonicalPath z))
      (Icc (0 : ℝ) 1) := by
  exact (gaussCutPlanePathFunction_continuous _).continuousOn

/-- The canonical path stays in the cut plane. -/
theorem gaussCutPlaneCanonicalPath_mem (z : gaussCutPlane) (t : ℝ) :
    gaussCutPlanePathFunction (gaussCutPlaneCanonicalPath z) t ∈ gaussCutPlane :=
  gaussCutPlanePathFunction_mem _ t

/-- A finite-chain continuation of the ordinary-series state exists along the canonical cut-plane
path to every point. -/
theorem exists_gauss_cut_plane_canonical_continuation
    (a b c : ℂ) (z : gaussCutPlane) :
    Nonempty (PathContinuationLift (gaussCutPlanePathFunction (gaussCutPlaneCanonicalPath z))
      (gaussSystemOperator a b c) (ordinaryHypergeometricState a b c (1 / 2 : ℂ))) := by
  apply exists_path_continuation_lift
    (gaussCutPlaneCanonicalPath_continuousOn z) gaussRegularPlane
    gaussRegularPlane_isOpen (gaussSystemOperator a b c)
    (gaussSystemOperator_differentiableOn a b c)
  · intro t ht
    exact gaussCutPlane_subset_regularPlane (gaussCutPlaneCanonicalPath_mem z t)

end DOZZ.Proofs
