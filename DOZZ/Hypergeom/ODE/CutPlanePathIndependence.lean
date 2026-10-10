/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlanePathHomotopy
public import DOZZ.Hypergeom.ODE.HomotopyContinuation
public import DOZZ.Hypergeom.ODE.GaussSystem

/-! Finite-chain Gauss continuation endpoints are independent of paths in the principal cut
plane. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- A path in any subtype of ℂ, viewed as a real-parameter complex-valued map and extended by
endpoint projection outside `[0,1]`. -/
noncomputable def subtypePathFunction {U : Set ℂ} {x y : U} (p : Path x y) : ℝ → ℂ :=
  fun t => (p (Set.projIcc 0 1 zero_le_one t) : ℂ)

/-- The real-parameter projection of a subtype path is continuous. -/
theorem subtypePathFunction_continuous {U : Set ℂ} {x y : U} (p : Path x y) :
    Continuous (subtypePathFunction p) := by
  change Continuous (fun t => (p (Set.projIcc 0 1 zero_le_one t) : ℂ))
  exact continuous_subtype_val.comp (p.continuous.comp continuous_projIcc)

/-- Every projected value of a subtype path remains in its subtype. -/
theorem subtypePathFunction_mem
    {U : Set ℂ} {x y : U} (p : Path x y) (t : ℝ) :
    subtypePathFunction p t ∈ U :=
  (p (Set.projIcc 0 1 zero_le_one t)).property

/-- The real-parameter form of a path in the subtype `gaussCutPlane`, extended by endpoint
projection outside `[0,1]`. -/
noncomputable def gaussCutPlanePathFunction {x y : gaussCutPlane} (p : Path x y) : ℝ → ℂ :=
  subtypePathFunction p

/-- A cut-plane path, viewed as a real-parameter complex-valued map, is continuous. -/
theorem gaussCutPlanePathFunction_continuous {x y : gaussCutPlane} (p : Path x y) :
    Continuous (gaussCutPlanePathFunction p) := by
  exact subtypePathFunction_continuous p

/-- Every value of the endpoint-projected real path remains in the cut plane. -/
theorem gaussCutPlanePathFunction_mem {x y : gaussCutPlane} (p : Path x y) (t : ℝ) :
    gaussCutPlanePathFunction p t ∈ gaussCutPlane := by
  exact subtypePathFunction_mem p t

/-- Any two finite-chain lifts of the same initial Gauss state along paths with common endpoints
in a simply connected subtype of the regular plane have the same terminal value. -/
theorem subtype_path_lifts_endpoint_eq_of_simplyConnected
    {U : Set ℂ} [SimplyConnectedSpace U] (hU : U ⊆ gaussRegularPlane)
    (a b c : ℂ) {x₀ x₁ : U} (p q : Path x₀ x₁)
    (initial : ℂ × ℂ)
    (A : PathContinuationLift (subtypePathFunction p)
      (gaussSystemOperator a b c) initial)
    (B : PathContinuationLift (subtypePathFunction q)
      (gaussSystemOperator a b c) initial) :
    A.value 1 = B.value 1 := by
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic p q
  obtain ⟨Γ, hΓ, hleft, hright, hbottom, htop, himage⟩ :=
    subtype_paths_real_homotopy F
  let bottom : ℝ → ℂ := fun t => Γ (t, 0)
  let top : ℝ → ℂ := fun t => Γ (t, 1)
  have hbottomPath : ∀ t ∈ Icc (0 : ℝ) 1,
      bottom t = subtypePathFunction p t := by
    intro t ht
    change Γ (t, 0) = (p (Set.projIcc 0 1 zero_le_one t) : ℂ)
    rw [hbottom t ht]
    exact congrArg (fun s : unitInterval => (p s : ℂ))
      (Set.projIcc_of_mem zero_le_one ht).symm
  have htopPath : ∀ t ∈ Icc (0 : ℝ) 1,
      top t = subtypePathFunction q t := by
    intro t ht
    change Γ (t, 1) = (q (Set.projIcc 0 1 zero_le_one t) : ℂ)
    rw [htop t ht]
    exact congrArg (fun s : unitInterval => (q s : ℂ))
      (Set.projIcc_of_mem zero_le_one ht).symm
  let A' := path_continuation_lift_congr A (fun t ht => (hbottomPath t ht).symm)
  let B' := path_continuation_lift_congr B (fun t ht => (htopPath t ht).symm)
  exact homotopy_path_continuation_endpoint_eq hΓ gaussRegularPlane
    gaussRegularPlane_isOpen (gaussSystemOperator a b c)
    (gaussSystemOperator_differentiableOn a b c)
    (fun z hz => hU (himage z hz))
    x₀ x₁ hleft hright initial A' B'

/-- Any two finite-chain lifts of the same initial Gauss state along paths with common endpoints
in the principal cut plane have the same terminal value. -/
theorem gauss_cut_plane_path_lifts_endpoint_eq
    (a b c : ℂ) {x₀ x₁ : gaussCutPlane} (p q : Path x₀ x₁)
    (initial : ℂ × ℂ)
    (A : PathContinuationLift (gaussCutPlanePathFunction p)
      (gaussSystemOperator a b c) initial)
    (B : PathContinuationLift (gaussCutPlanePathFunction q)
      (gaussSystemOperator a b c) initial) :
    A.value 1 = B.value 1 := by
  exact subtype_path_lifts_endpoint_eq_of_simplyConnected gaussCutPlane_subset_regularPlane
    a b c p q initial A B

end DOZZ.Proofs
