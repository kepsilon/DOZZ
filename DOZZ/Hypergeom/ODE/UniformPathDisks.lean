/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Bounded
public import DOZZ.Hypergeom.ODE.FiniteDiskChain

/-! A compact path in an open regular domain has a uniform family of coefficient disks with a
uniform coefficient bound. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_uniform_holomorphic_disks_along_path
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        DifferentiableOn ℂ H (Metric.ball (γ t) r) ∧
          ∀ z ∈ Metric.ball (γ t) r, ‖H z‖ ≤ M := by
  let K : Set ℂ := γ '' Icc (0 : ℝ) 1
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.image_of_continuousOn hγ
  have hKU : K ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    exact hpath t ht
  obtain ⟨V, hKV, hVopen, hVbounded⟩ :=
    Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      hK hU hKU hH.continuousOn
  let W := V ∩ U
  have hWopen : IsOpen W := hVopen.inter hU
  have hKW : K ⊆ W := by
    intro z hz
    exact ⟨hKV hz, hKU hz⟩
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hWopen hKW
  let r := δ / 2
  obtain ⟨B, hB⟩ := hVbounded.subset_closedBall (H (γ 0))
  let M := max 0 (B + ‖H (γ 0)‖)
  refine ⟨r, M, by dsimp [r]; linarith, le_max_left _ _, ?_⟩
  intro t ht
  have hγtK : γ t ∈ K := ⟨t, ht, rfl⟩
  have hballW : Metric.ball (γ t) r ⊆ W := by
    intro z hz
    apply hδW
    apply Metric.mem_cthickening_of_dist_le z (γ t) δ K hγtK
    have hdist : dist z (γ t) < r := Metric.mem_ball.mp hz
    have hrδ : r ≤ δ := by dsimp [r]; linarith
    exact hdist.le.trans hrδ
  have hballU : Metric.ball (γ t) r ⊆ U := fun _ hz => (hballW hz).2
  have hballV : Metric.ball (γ t) r ⊆ V := fun _ hz => (hballW hz).1
  refine ⟨hH.mono hballU, ?_⟩
  intro z hz
  have hzV := hballV hz
  have hdist := hB ⟨z, hzV, rfl⟩
  have hnorm : ‖H z - H (γ 0)‖ ≤ B := by
    simpa [dist_eq_norm] using hdist
  calc
    ‖H z‖ = ‖(H z - H (γ 0)) + H (γ 0)‖ := by congr 1; abel
    _ ≤ ‖H z - H (γ 0)‖ + ‖H (γ 0)‖ := norm_add_le _ _
    _ ≤ B + ‖H (γ 0)‖ := by linarith
    _ ≤ M := le_max_right _ _

/-- Every continuous path in an open regular domain admits a finite chain of holomorphic local
solutions for the linear system, starting at an arbitrary initial vector. -/
theorem exists_holomorphic_path_continuation_chain
    [CompleteSpace E]
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (y : E) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        DifferentiableOn ℂ H (Metric.ball (γ t) r) ∧
          ∀ z ∈ Metric.ball (γ t) r, ‖H z‖ ≤ M) ∧
      ∃ N : ℕ, 0 < N ∧
        ∃ D : ℕ → HolomorphicDiskSolution H r,
          (D 0).center = γ 0 ∧ (D 0).initial = y ∧ (D N).center = γ 1 ∧
          (∀ i ≤ N, (D i).center = γ ((i : ℝ) / (N : ℝ))) ∧
          (∀ i < N, (D (i + 1)).initial =
            (D i).solution (γ (((i + 1 : ℕ) : ℝ) / (N : ℝ)))) ∧
          (∀ i < N, ∀ t ∈ Icc ((i : ℝ) / (N : ℝ))
            (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
            γ t ∈ Metric.ball ((D i).center) (r / 2)) ∧
          ∀ i < N, ∀ z ∈ Metric.ball
            (γ (((i + 1 : ℕ) : ℝ) / (N : ℝ))) (r / 2),
            (D i).solution z = (D (i + 1)).solution z := by
  obtain ⟨r, M, hr, hM, hlocal⟩ :=
    exists_uniform_holomorphic_disks_along_path hγ U hU H hH hpath
  have hHpath : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableOn ℂ H (Metric.ball (γ t) r) := fun t ht => (hlocal t ht).1
  have hboundPath : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ z ∈ Metric.ball (γ t) r, ‖H z‖ ≤ M := fun t ht => (hlocal t ht).2
  obtain ⟨N, hN, D, hD0c, hD0i, hDcenters, hDinitials, hcover, hoverlap⟩ :=
    exists_path_holomorphic_disk_chain hγ r M hr hM H hHpath hboundPath y
  have hDNc : (D N).center = γ 1 := by
    have h := hDcenters N le_rfl
    have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self (by exact_mod_cast hN.ne')
    simpa [hNN] using h
  exact ⟨r, M, hr, hM, hlocal, N, hN, D, hD0c, hD0i, hDNc,
    hDcenters, hDinitials, hcover, hoverlap⟩

end DOZZ.Proofs
