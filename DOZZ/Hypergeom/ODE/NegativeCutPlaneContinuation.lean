/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.NegativeCutPlaneTopology
public import DOZZ.Hypergeom.ODE.CutPlanePathIndependence
public import DOZZ.Hypergeom.ODE.SeriesSeed

/-! Path-independent Gauss-system continuation on the negative cut plane. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- Regular initial point for continuation on the negative cut plane. -/
noncomputable def gaussNegativeCutPlaneBasepoint : gaussNegativeCutPlane :=
  ⟨(-1 / 2 : ℂ), by change _ ∨ _; right; norm_num⟩

/-- The straight path in the star-convex negative cut plane from `-1/2` to `z`. -/
noncomputable def gaussNegativeCutPlaneCanonicalPath (z : gaussNegativeCutPlane) :
    Path gaussNegativeCutPlaneBasepoint z := by
  let g : unitInterval → ℂ := fun t =>
    (1 - (t : ℝ)) • (-1 / 2 : ℂ) + (t : ℝ) • (z : ℂ)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hgmem : ∀ t, g t ∈ gaussNegativeCutPlane := by
    intro t
    change (1 - (t : ℝ)) • (-1 / 2 : ℂ) + (t : ℝ) • (z : ℂ) ∈
      gaussNegativeCutPlane
    exact gaussNegativeCutPlane_starConvex z.property
      (a := 1 - (t : ℝ)) (b := (t : ℝ))
      (by linarith [t.property.2]) t.property.1 (by ring)
  let f : C(unitInterval, gaussNegativeCutPlane) :=
    ⟨fun t => ⟨g t, hgmem t⟩, hg.subtype_mk hgmem⟩
  refine ⟨f, ?_, ?_⟩
  · apply Subtype.ext
    simp [f, g, gaussNegativeCutPlaneBasepoint]
  · apply Subtype.ext
    simp [f, g]

/-- The canonical negative-cut path is continuous on its real parameter interval. -/
theorem gaussNegativeCutPlaneCanonicalPath_continuousOn (z : gaussNegativeCutPlane) :
    ContinuousOn (subtypePathFunction (gaussNegativeCutPlaneCanonicalPath z))
      (Icc (0 : ℝ) 1) := by
  change ContinuousOn
    (fun t => ((gaussNegativeCutPlaneCanonicalPath z)
      (Set.projIcc 0 1 zero_le_one t) : ℂ)) _
  exact (continuous_subtype_val.comp
    ((gaussNegativeCutPlaneCanonicalPath z).continuous.comp continuous_projIcc)).continuousOn

/-- The canonical path remains in the negative cut plane under endpoint projection. -/
theorem gaussNegativeCutPlaneCanonicalPath_mem (z : gaussNegativeCutPlane) (t : ℝ) :
    subtypePathFunction (gaussNegativeCutPlaneCanonicalPath z) t ∈ gaussNegativeCutPlane :=
  (gaussNegativeCutPlaneCanonicalPath z
    (Set.projIcc 0 1 zero_le_one t)).property

/-- A finite-chain continuation exists along the canonical path to every negative-cut point. -/
theorem exists_gauss_negative_cut_plane_canonical_continuation
    (a b c : ℂ) (z : gaussNegativeCutPlane) :
    Nonempty (PathContinuationLift
      (subtypePathFunction (gaussNegativeCutPlaneCanonicalPath z))
      (gaussSystemOperator a b c)
      (ordinaryHypergeometricState a b c (-1 / 2 : ℂ))) := by
  apply exists_path_continuation_lift
    (gaussNegativeCutPlaneCanonicalPath_continuousOn z) gaussRegularPlane
    gaussRegularPlane_isOpen (gaussSystemOperator a b c)
    (gaussSystemOperator_differentiableOn a b c)
  · intro t ht
    exact gaussNegativeCutPlane_subset_regularPlane
      (gaussNegativeCutPlaneCanonicalPath_mem z t)

/-- A chosen finite-chain continuation of the series state from `-1/2` to `z`. -/
noncomputable def gaussNegativeCutPlaneCanonicalContinuationLift
    (a b c : ℂ) (z : gaussNegativeCutPlane) :
    PathContinuationLift
      (subtypePathFunction (gaussNegativeCutPlaneCanonicalPath z))
      (gaussSystemOperator a b c)
      (ordinaryHypergeometricState a b c (-1 / 2 : ℂ)) :=
  Classical.choice (exists_gauss_negative_cut_plane_canonical_continuation a b c z)

/-- The endpoint vector obtained by continuing the series state to `z` in the negative cut plane.
-/
noncomputable def gaussNegativeCutPlaneContinuationState
    (a b c : ℂ) (z : gaussNegativeCutPlane) : ℂ × ℂ :=
  (gaussNegativeCutPlaneCanonicalContinuationLift a b c z).value 1

/-- Every finite-chain continuation along any negative-cut path has the selected endpoint vector.
-/
theorem gauss_negative_cut_plane_continuation_path_endpoint_eq
    (a b c : ℂ) (z : gaussNegativeCutPlane)
    {p : Path gaussNegativeCutPlaneBasepoint z}
    (L : PathContinuationLift (subtypePathFunction p)
      (gaussSystemOperator a b c)
      (ordinaryHypergeometricState a b c (-1 / 2 : ℂ))) :
    L.value 1 = gaussNegativeCutPlaneContinuationState a b c z := by
  exact subtype_path_lifts_endpoint_eq_of_simplyConnected
    gaussNegativeCutPlane_subset_regularPlane a b c p
    (gaussNegativeCutPlaneCanonicalPath z)
    (ordinaryHypergeometricState a b c (-1 / 2 : ℂ)) L
    (gaussNegativeCutPlaneCanonicalContinuationLift a b c z)

end DOZZ.Proofs
