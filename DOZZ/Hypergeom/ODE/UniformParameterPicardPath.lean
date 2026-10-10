/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterCompactBounds
public import DOZZ.Hypergeom.ODE.FamilySystem

/-! Uniform Gauss-system coefficient and parameter-derivative bounds on compact path tubes. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- A compact parameter family and a fixed compact regular path share one disk radius on which
the Gauss-system operator, its parameter derivative, and both spatial regularity properties are
uniform. -/
theorem exists_uniform_gaussSystem_parameterized_disks_on_path
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussRegularPlane)
    (hpathSlit : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussSlitPlane) :
    ∃ r M L : ℝ, 0 < r ∧ 0 ≤ M ∧ 0 ≤ L ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (∀ z ∈ Metric.ball (γ t) r,
          z ∈ gaussRegularPlane ∧ z ∈ gaussSlitPlane) ∧
        (∀ p ∈ K, DifferentiableOn ℂ
          (gaussSystemOperator p.1 p.2.1 p.2.2) (Metric.ball (γ t) r)) ∧
        (∀ p ∈ K, ContinuousOn (gaussParamOperatorFDeriv p)
          (Metric.ball (γ t) r)) ∧
        (∀ p ∈ K, ∀ z ∈ Metric.ball (γ t) r,
          ‖gaussSystemOperator p.1 p.2.1 p.2.2 z‖ ≤ M) ∧
        (∀ p ∈ K, ∀ z ∈ Metric.ball (γ t) r,
          ‖gaussParamOperatorFDeriv p z‖ ≤ L) ∧
        (∀ p ∈ K, ∀ z ∈ Metric.ball (γ t) r,
          HasFDerivAt (fun q =>
            gaussSystemOperator q.1 q.2.1 q.2.2 z)
            (gaussParamOperatorFDeriv p z) p) := by
  let I : Set ℝ := Icc (0 : ℝ) 1
  let S : Set ℂ := γ '' I
  have hScompact : IsCompact S := by
    dsimp [S, I]
    exact isCompact_Icc.image_of_continuousOn hγ
  have hSreg : S ⊆ gaussRegularPlane := by
    rintro z ⟨t, ht, rfl⟩
    exact hpath t ht
  have hSslit : S ⊆ gaussSlitPlane := by
    rintro z ⟨t, ht, rfl⟩
    exact hpathSlit t ht
  have hUopen : IsOpen (gaussRegularPlane ∩ gaussSlitPlane) :=
    gaussRegularPlane_isOpen.inter gaussSlitPlane_isOpen
  have hSU : S ⊆ gaussRegularPlane ∩ gaussSlitPlane := fun z hz =>
    ⟨hSreg hz, hSslit hz⟩
  obtain ⟨δ, hδ, hthick⟩ :=
    hScompact.exists_cthickening_subset_open hUopen hSU
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let W : Set ℂ := Metric.closedBall (0 : ℂ) r
  have hWcompact : IsCompact W := isCompact_closedBall (0 : ℂ) r
  let plus : ℂ × ℂ → ℂ := fun x => x.1 + x.2
  let Z : Set ℂ := plus '' (S ×ˢ W)
  have hplus : ContinuousOn plus (S ×ˢ W) := by
    dsimp [plus]
    fun_prop
  have hZcompact : IsCompact Z :=
    (hScompact.prod hWcompact).image_of_continuousOn hplus
  have hZsubset : Z ⊆ gaussRegularPlane ∩ gaussSlitPlane := by
    rintro z ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
    rcases hx with ⟨t, ht, rfl⟩
    have hwNorm : ‖w‖ ≤ r := by
      simpa [W, Metric.mem_closedBall, dist_zero_right] using hw
    have hdist : dist (γ t + w) (γ t) ≤ r := by
      rw [dist_eq_norm]
      have hsub : γ t + w - γ t = w := by abel
      rw [hsub]
      exact hwNorm
    have hrδ : r ≤ δ := by dsimp [r]; linarith
    apply hthick
    exact Metric.mem_cthickening_of_dist_le (γ t + w) (γ t) δ S
      ⟨t, ht, rfl⟩ (hdist.trans hrδ)
  have hZreg : Z ⊆ gaussRegularPlane := fun z hz => (hZsubset hz).1
  obtain ⟨M, hM, hMbound⟩ :=
    exists_joint_uniform_gaussSystemOperator_norm_bound hK hZcompact hZreg
  obtain ⟨L, hL, hLbound⟩ :=
    exists_joint_uniform_gaussSystemOperator_param_fderiv_norm_bound hK hZcompact hZreg
  have hballZ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.ball (γ t) r, z ∈ Z := by
    intro t ht z hz
    let w : ℂ := z - γ t
    have hw : w ∈ W := by
      apply Metric.mem_closedBall.mpr
      have hdist : dist z (γ t) < r := Metric.mem_ball.mp hz
      have hnorm : ‖z - γ t‖ < r := by simpa [dist_eq_norm] using hdist
      simpa [W, dist_zero_right, w] using hnorm.le
    refine ⟨(γ t, w), ⟨⟨t, ht, rfl⟩, hw⟩, ?_⟩
    dsimp [plus, w]
    ring
  refine ⟨r, M, L, hr, hM, hL, ?_⟩
  intro t ht
  have hballReg : Metric.ball (γ t) r ⊆ gaussRegularPlane := by
    intro z hz
    exact hZreg (hballZ t ht z hz)
  have hballSlit : Metric.ball (γ t) r ⊆ gaussSlitPlane := by
    intro z hz
    exact (hZsubset (hballZ t ht z hz)).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨hballReg hz, hballSlit hz⟩
  · intro p hp
    exact (gaussSystemOperator_differentiableOn p.1 p.2.1 p.2.2).mono hballReg
  · intro p hp
    exact (gaussSystemOperator_param_fderiv_continuousOn p).mono hballReg
  · intro p hp z hz
    exact hMbound p hp z (hballZ t ht z hz)
  · intro p hp z hz
    exact hLbound p hp z (hballZ t ht z hz)
  · intro p hp z hz
    exact gaussSystemOperator_param_hasFDerivAt p z

end DOZZ.Proofs
