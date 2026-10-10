/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.DiskContinuation
public import DOZZ.Hypergeom.ODE.PathSubdivision

/-! Iteration of the one-step disk extension along finitely many nearby centers. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A finite chain of local Picard solutions exists along any finite sequence of nearby centers
on which one coefficient bound is valid. The returned sequence records the center value at each
step and equality on the half-radius overlap. -/
theorem exists_finite_holomorphic_disk_chain
    (N : ℕ) (centers : ℕ → ℂ) (r M : ℝ)
    (H : ℂ → E →L[ℂ] E) (hM : 0 ≤ M)
    (hH : ∀ i ≤ N, DifferentiableOn ℂ H (Metric.ball (centers i) r))
    (hbound : ∀ i ≤ N, ∀ z ∈ Metric.ball (centers i) r, ‖H z‖ ≤ M)
    (hclose : ∀ i < N, dist (centers (i + 1)) (centers i) < r / 2)
    (y : E) :
    ∃ D : ℕ → HolomorphicDiskSolution H r,
      (D 0).center = centers 0 ∧ (D 0).initial = y ∧
      (∀ i ≤ N, (D i).center = centers i) ∧
      ∀ i < N,
        (D (i + 1)).center = centers (i + 1) ∧
        (D (i + 1)).initial = (D i).solution (centers (i + 1)) ∧
        ∀ z ∈ Metric.ball (centers (i + 1)) (r / 2),
          (D i).solution z = (D (i + 1)).solution z := by
  let Dzero := holomorphicDiskSolutionOfBound (centers 0) r M H (hH 0 (by omega)) y hM
    (hbound 0 (by omega))
  let D : ℕ → HolomorphicDiskSolution H r := Nat.rec Dzero fun i Di =>
    if hi : i < N then
      extendHolomorphicDiskSolution r M H hM Di (centers (i + 1))
        (hH (i + 1) (by omega)) (hbound (i + 1) (by omega))
    else Di
  have hcenter (i : ℕ) (hi : i ≤ N) : (D i).center = centers i := by
    induction i with
    | zero => simp [D, Dzero, holomorphicDiskSolutionOfBound]
    | succ i ih =>
        have hi' : i < N := by omega
        have hi_le : i ≤ N := by omega
        simp [D, hi', extendHolomorphicDiskSolution, holomorphicDiskSolutionOfBound]
  refine ⟨D, hcenter 0 (by omega), ?_, ?_, ?_⟩
  · simp [D, Dzero, holomorphicDiskSolutionOfBound]
  · exact hcenter
  · intro i hi
    have hi1 : i + 1 ≤ N := by omega
    have hprev : i ≤ N := by omega
    have hcenterNext := hcenter (i + 1) hi1
    have hbuild : (D (i + 1)) =
        extendHolomorphicDiskSolution r M H hM (D i) (centers (i + 1))
          (hH (i + 1) hi1) (hbound (i + 1) hi1) := by
      simp [D, hi]
    refine ⟨hcenterNext, ?_, ?_⟩
    · rw [hbuild]
      rfl
    · intro z hz
      rw [hbuild]
      have hnear : dist (centers (i + 1)) (D i).center < r / 2 := by
        rw [hcenter i hprev]
        exact hclose i hi
      exact extendHolomorphicDiskSolution_agrees r M H hM (D i)
        (centers (i + 1)) hnear (hH (i + 1) hi1) (hbound (i + 1) hi1) z hz

/-- A continuous path with one uniform family of holomorphic coefficient disks and a uniform
operator bound admits a finite analytic continuation chain from its initial value. -/
theorem exists_path_holomorphic_disk_chain
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (H : ℂ → E →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableOn ℂ H (Metric.ball (γ t) r))
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.ball (γ t) r, ‖H z‖ ≤ M)
    (y : E) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ → HolomorphicDiskSolution H r,
      (D 0).center = γ 0 ∧ (D 0).initial = y ∧
      (∀ i ≤ N, (D i).center = γ ((i : ℝ) / (N : ℝ))) ∧
      (∀ i < N, (D (i + 1)).initial =
        (D i).solution (γ (((i + 1 : ℕ) : ℝ) / (N : ℝ)))) ∧
      (∀ i < N, ∀ t ∈ Icc ((i : ℝ) / (N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
        γ t ∈ Metric.ball ((D i).center) (r / 2)) ∧
      ∀ i < N, ∀ z ∈ Metric.ball (γ (((i + 1 : ℕ) : ℝ) / (N : ℝ))) (r / 2),
        (D i).solution z = (D (i + 1)).solution z := by
  obtain ⟨N, hN, hpartition⟩ :=
    exists_path_subdivision hγ (by linarith : 0 < r / 2)
  have hclose := fun i hi => (hpartition i hi).1
  have hcover := fun i hi t ht => (hpartition i hi).2 t ht
  let centers : ℕ → ℂ := fun i => γ ((i : ℝ) / (N : ℝ))
  have htime (i : ℕ) (hi : i ≤ N) : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    constructor
    · positivity
    · apply (div_le_one hNreal).2
      exact_mod_cast hi
  have hHcenters : ∀ i ≤ N, DifferentiableOn ℂ H (Metric.ball (centers i) r) := by
    intro i hi
    simpa [centers] using hH _ (htime i hi)
  have hboundCenters : ∀ i ≤ N, ∀ z ∈ Metric.ball (centers i) r, ‖H z‖ ≤ M := by
    intro i hi
    simpa [centers] using hbound _ (htime i hi)
  have hcloseCenters : ∀ i < N, dist (centers (i + 1)) (centers i) < r / 2 := by
    intro i hi
    simpa [centers, dist_comm] using (hclose i hi)
  obtain ⟨D, hD0c, hD0i, hDcenters, hDstep⟩ :=
    exists_finite_holomorphic_disk_chain N centers r M H hM hHcenters
      hboundCenters hcloseCenters y
  refine ⟨N, hN, D, ?_, hD0i, ?_, ?_, ?_, ?_⟩
  · simpa [centers] using hD0c
  · intro i hi
    simpa [centers] using hDcenters i hi
  · intro i hi
    have hstep := hDstep i hi
    simpa [centers] using hstep.2.1
  · intro i hi t ht
    have hcenter := hDcenters i (Nat.le_of_lt hi)
    rw [hcenter]
    exact Metric.mem_ball.mpr (by simpa [centers] using hcover i hi t ht)
  · intro i hi z hz
    have hstep := hDstep i hi
    simpa [centers] using hstep.2.2 z hz

end DOZZ.Proofs
