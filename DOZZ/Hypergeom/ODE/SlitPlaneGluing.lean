/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.BranchOverlap
public import DOZZ.Hypergeom.ODE.SeriesEquation

/-! Glue the principal and negative-axis ODE branches to the ordinary germ. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

/-- A point in both regular cut planes is nonreal. -/
private theorem gaussCutPlane_negative_overlap_im_ne_zero {z : ℂ}
    (hz : z ∈ gaussCutPlane) (hw : z ∈ gaussNegativeCutPlane) : z.im ≠ 0 := by
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  change z.im ≠ 0 ∨ z.re < 0 at hw
  rcases hz with him | ⟨hpos, _⟩
  · exact him
  · rcases hw with him | hneg
    · exact him
    · exact False.elim (by linarith)

/-- Every point of the slit plane is covered by one regular branch or is the origin. -/
private theorem gaussSlitPlane_subset_cut_union_negative_or_zero :
    gaussSlitPlane ⊆ gaussCutPlane ∪
      (gaussNegativeCutPlane ∪ ({(0 : ℂ)} : Set ℂ)) := by
  intro z hz
  change z ∈ gaussCutPlane ∨ (z ∈ gaussNegativeCutPlane ∨ z = 0)
  change z.im ≠ 0 ∨ z.re < 1 at hz
  by_cases him : z.im ≠ 0
  · left
    change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)
    exact Or.inl him
  · have himz : z.im = 0 := not_ne_iff.mp him
    by_cases hneg : z.re < 0
    · right
      left
      change z.im ≠ 0 ∨ z.re < 0
      exact Or.inr hneg
    · by_cases hpos : 0 < z.re
      · have hre : z.re < 1 := hz.resolve_left him
        left
        change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)
        exact Or.inr ⟨hpos, hre⟩
      · have hre : z.re = 0 := by linarith
        right
        right
        exact Complex.ext hre himz

/-- The scalar function obtained by gluing the two path-independent ODE branches. -/
noncomputable def gaussSlitScalarState (a b c : ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact if hz : z ∈ gaussCutPlane then gaussCutPlaneScalarState a b c z
      else if hz : z ∈ gaussNegativeCutPlane then gaussNegativeCutPlaneScalarState a b c z
      else ordinaryHypergeometric (𝔸 := ℂ) a b c z

private theorem gaussSlitScalarState_eq_negative_on_negativeCut
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : z ∈ gaussNegativeCutPlane) :
    gaussSlitScalarState a b c z = gaussNegativeCutPlaneScalarState a b c z := by
  classical
  by_cases hcut : z ∈ gaussCutPlane
  · have him := gaussCutPlane_negative_overlap_im_ne_zero hcut hz
    rw [gaussSlitScalarState, dite_eq_left hcut]
    exact gaussBranches_eq_of_im_ne_zero a b c hc him
  · rw [gaussSlitScalarState, dite_eq_right hcut, dite_eq_left hz]

/-- On the open unit disk, the glued value is the ordinary Gauss series. -/
theorem gaussSlitScalarState_eq_ordinary_on_unitDisk
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hznorm : ‖z‖ < 1) :
    gaussSlitScalarState a b c z = ordinaryHypergeometric (𝔸 := ℂ) a b c z := by
  classical
  have hzslit : z ∈ gaussSlitPlane := by
    change z.im ≠ 0 ∨ z.re < 1
    by_cases him : z.im ≠ 0
    · exact Or.inl him
    · right
      have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have : z.re ≤ |z.re| := le_abs_self _
      linarith
  rcases gaussSlitPlane_subset_cut_union_negative_or_zero hzslit with hcut | hrest
  · rw [gaussSlitScalarState, dite_eq_left hcut]
    exact gaussCutPlaneScalarState_eq_ordinary_on_unitDisk a b c hc hcut hznorm
  · rcases hrest with hnegative | hzero
    · by_cases hcut : z ∈ gaussCutPlane
      · rw [gaussSlitScalarState, dite_eq_left hcut]
        exact gaussCutPlaneScalarState_eq_ordinary_on_unitDisk a b c hc hcut hznorm
      · rw [gaussSlitScalarState, dite_eq_right hcut, dite_eq_left hnegative]
        exact gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk
          a b c hc hnegative hznorm
    · have hz0 : z = 0 := Set.mem_singleton_iff.mp hzero
      subst z
      simp [gaussSlitScalarState, gaussCutPlane, gaussNegativeCutPlane]

/-- The glued scalar function is holomorphic on the slit plane. -/
theorem gaussSlitScalarState_differentiableOn
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    DifferentiableOn ℂ (gaussSlitScalarState a b c) gaussSlitPlane := by
  classical
  intro z hz
  rcases gaussSlitPlane_subset_cut_union_negative_or_zero hz with hcut | hrest
  · have hstateAt : DifferentiableAt ℂ (gaussCutPlaneScalarState a b c) z :=
      (gaussCutPlaneScalarState_differentiableOn a b c).differentiableAt
        (gaussCutPlane_isOpen.mem_nhds hcut)
    have hnear : gaussSlitScalarState a b c =ᶠ[𝓝 z]
        gaussCutPlaneScalarState a b c := by
      filter_upwards [gaussCutPlane_isOpen.mem_nhds hcut] with w hw
      simp [gaussSlitScalarState, hw]
    exact (hstateAt.congr_of_eventuallyEq hnear).differentiableWithinAt
  · rcases hrest with hnegative | hzero
    · have hstateAt : DifferentiableAt ℂ (gaussNegativeCutPlaneScalarState a b c) z :=
        (gaussNegativeCutPlaneScalarState_differentiableOn a b c).differentiableAt
          (gaussNegativeCutPlane_isOpen.mem_nhds hnegative)
      have hnear : gaussSlitScalarState a b c =ᶠ[𝓝 z]
          gaussNegativeCutPlaneScalarState a b c := by
        filter_upwards [gaussNegativeCutPlane_isOpen.mem_nhds hnegative] with w hw
        exact gaussSlitScalarState_eq_negative_on_negativeCut a b c hc hw
      exact (hstateAt.congr_of_eventuallyEq hnear).differentiableWithinAt
    · have hz0 : z = 0 := Set.mem_singleton_iff.mp hzero
      subst z
      have hseriesAt : DifferentiableAt ℂ (ordinaryHypergeometric (𝔸 := ℂ) a b c) 0 := by
        have ha : AnalyticAt ℂ (ordinaryHypergeometric (𝔸 := ℂ) a b c) 0 :=
          ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc 0
            (by simp [Metric.mem_ball])
        exact ha.differentiableAt
      have hnear : gaussSlitScalarState a b c =ᶠ[𝓝 (0 : ℂ)]
          ordinaryHypergeometric (𝔸 := ℂ) a b c := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)]
          with w hw
        apply gaussSlitScalarState_eq_ordinary_on_unitDisk a b c hc
        simpa [Metric.mem_ball, dist_zero_right] using hw
      exact (hseriesAt.congr_of_eventuallyEq hnear).differentiableWithinAt

/-- The ordinary-series germ extends to the principal slit plane for every admissible `c`. -/
theorem gauss_hypergeometric_exists :
    ∃ H : ℂ → ℂ → ℂ → ℂ → ℂ, IsGaussHypergeometricFamily H := by
  let H : ℂ → ℂ → ℂ → ℂ → ℂ := fun a b c z => gaussSlitScalarState a b c z
  refine ⟨H, ?_⟩
  intro a b c hc
  change IsGaussHypergeometric a b c (gaussSlitScalarState a b c)
  constructor
  · exact gaussSlitScalarState_differentiableOn a b c hc
  · intro z hznorm
    exact gaussSlitScalarState_eq_ordinary_on_unitDisk a b c hc hznorm

end DOZZ.Proofs
