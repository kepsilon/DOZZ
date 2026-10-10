/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.HomotopyGrid
public import DOZZ.Hypergeom.ODE.PathLift

/-! The finite homotopy grid supplies continuous Picard lifts on its lower and upper boundary
paths, with equal endpoint values. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- One horizontal Picard transfer in a finite homotopy grid. -/
noncomputable def homotopyGridRight
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (i j : ℕ) (v : E) : E :=
  if hi : i < G.N then
    if hj : j ≤ G.N then
      localPicardTransfer G.r G.M H (G.data i (Nat.le_of_lt hi) j hj) v (G.node (i + 1) j)
    else v
  else v

/-- The disk solution at one node of a horizontal row, initialized by the accumulated transfers
from the left boundary. -/
noncomputable def homotopyGridRowDisk
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) (hi : i ≤ G.N) : HolomorphicDiskSolution H G.r :=
  holomorphicDiskSolutionOfBound (G.node i j) G.r G.M H
    (G.data i hi j hj).differentiable
    (finiteGridHorizontal (homotopyGridRight G) 0 j i y)
    G.M_nonneg (G.data i hi j hj).bounded

/-- Extend the row-disk definition to all natural indices; only indices at most `N` are used. -/
noncomputable def homotopyGridRowChain
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) : HolomorphicDiskSolution H G.r :=
  homotopyGridRowDisk G j hj (min i G.N) (Nat.min_le_right _ _)

theorem homotopyGridRowChain_center
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) (hi : i ≤ G.N) :
    (homotopyGridRowChain G j hj i).center =
      Γ ((i : ℝ) / (G.N : ℝ), (j : ℝ) / (G.N : ℝ)) := by
  simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi,
    holomorphicDiskSolutionOfBound, G.node_eq i hi j hj]

theorem homotopyGridRowChain_initial
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) (hi : i ≤ G.N) :
    (homotopyGridRowChain G j hj i).initial =
      finiteGridHorizontal (homotopyGridRight G) 0 j i y := by
  simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi,
    holomorphicDiskSolutionOfBound]

theorem homotopyGridRowChain_next_initial
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) (hi : i < G.N) :
    (homotopyGridRowChain G j hj (i + 1)).initial =
      (homotopyGridRowChain G j hj i).solution (G.node (i + 1) j) := by
  have hi' : i ≤ G.N := Nat.le_of_lt hi
  have hi1 : i + 1 ≤ G.N := Nat.succ_le_iff.mpr hi
  simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi',
    holomorphicDiskSolutionOfBound,
    finiteGridHorizontal, homotopyGridRight, localPicardTransfer, hi, hj]

/-- A finite homotopy grid yields continuous local-solution lifts of both boundary paths, and
their terminal values agree. The local formulas are retained for later lift-uniqueness arguments. -/
theorem homotopy_grid_boundary_lifts_endpoint_eq_with_formulas
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y)
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    ∃ bottom top : ℝ → E,
      ContinuousOn bottom (Icc (0 : ℝ) 1) ∧
      ContinuousOn top (Icc (0 : ℝ) 1) ∧
      bottom 0 = y ∧ top 0 = y ∧ bottom 1 = top 1 ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        bottom t = (homotopyGridRowChain G 0 (by omega) i).solution (Γ (t, 0))) ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        top t = (homotopyGridRowChain G G.N le_rfl i).solution (Γ (t, 1))) ∧
      (∀ i ≤ G.N, (homotopyGridRowChain G 0 (by omega) i).center =
        Γ ((i : ℝ) / (G.N : ℝ), 0)) ∧
      (∀ i ≤ G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G 0 (by omega) i).center G.r, ‖H z‖ ≤ G.M) ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        Γ (t, 0) ∈ Metric.ball (homotopyGridRowChain G 0 (by omega) i).center (G.r / 2)) ∧
      (∀ i < G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G 0 (by omega) (i + 1)).center (G.r / 2),
        (homotopyGridRowChain G 0 (by omega) i).solution z =
          (homotopyGridRowChain G 0 (by omega) (i + 1)).solution z) ∧
      (∀ i ≤ G.N, (homotopyGridRowChain G G.N le_rfl i).center =
        Γ ((i : ℝ) / (G.N : ℝ), 1)) ∧
      (∀ i ≤ G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G G.N le_rfl i).center G.r, ‖H z‖ ≤ G.M) ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        Γ (t, 1) ∈ Metric.ball (homotopyGridRowChain G G.N le_rfl i).center (G.r / 2)) ∧
      (∀ i < G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G G.N le_rfl (i + 1)).center (G.r / 2),
        (homotopyGridRowChain G G.N le_rfl i).solution z =
          (homotopyGridRowChain G G.N le_rfl (i + 1)).solution z) := by
  let N := G.N
  let bottomPath : ℝ → ℂ := fun t => Γ (t, 0)
  let topPath : ℝ → ℂ := fun t => Γ (t, 1)
  have hN : 0 < N := G.N_pos
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNdiv : (N : ℝ) / (N : ℝ) = 1 := div_self hNreal.ne'
  have hGNN : (G.N : ℝ) / (G.N : ℝ) = 1 := by
    exact div_self (by exact_mod_cast G.N_pos.ne')
  have hbottomCont : ContinuousOn bottomPath (Icc (0 : ℝ) 1) := by
    apply hΓ.comp (by fun_prop)
    intro t ht
    exact ⟨ht, by norm_num⟩
  have htopCont : ContinuousOn topPath (Icc (0 : ℝ) 1) := by
    apply hΓ.comp (by fun_prop)
    intro t ht
    exact ⟨ht, by norm_num⟩
  let Db : ℕ → HolomorphicDiskSolution H G.r := homotopyGridRowChain G 0 (by omega)
  let Dt : ℕ → HolomorphicDiskSolution H G.r := homotopyGridRowChain G N le_rfl
  have hbc (i : ℕ) (hi : i ≤ N) : (Db i).center = bottomPath ((i : ℝ) / (N : ℝ)) := by
    simpa [Db, bottomPath] using homotopyGridRowChain_center G 0 (by omega) i hi
  have htc (i : ℕ) (hi : i ≤ N) : (Dt i).center = topPath ((i : ℝ) / (N : ℝ)) := by
    simpa [Dt, topPath, N, hGNN] using homotopyGridRowChain_center G G.N le_rfl i hi
  have hbi : (Db 0).initial = y := by
    calc
      (Db 0).initial = finiteGridHorizontal (homotopyGridRight G) 0 0 0 y := by
        simpa [Db] using homotopyGridRowChain_initial G 0 (by omega) 0 (by omega)
      _ = y := by simp [finiteGridHorizontal]
  have hti : (Dt 0).initial = y := by
    calc
      (Dt 0).initial = finiteGridHorizontal (homotopyGridRight G) 0 N 0 y := by
        simpa [Dt] using homotopyGridRowChain_initial G N le_rfl 0 (by omega)
      _ = y := by simp [finiteGridHorizontal]
  have hbcover : ∀ i < N, ∀ t ∈ Icc ((i : ℝ) / (N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
      bottomPath t ∈ Metric.ball (Db i).center (G.r / 2) := by
    intro i hi t ht
    have hz : (0 : ℝ) ∈ Icc (((0 : ℕ) : ℝ) / (G.N : ℝ))
        (((0 + 1 : ℕ) : ℝ) / (G.N : ℝ)) := by
      constructor
      · norm_num
      · positivity
    have hj : 0 < G.N := G.N_pos
    have hi' : i ≤ G.N := Nat.le_of_lt hi
    have hnear := G.cell_image i hi 0 hj t (by simpa [N] using ht) 0 hz
    have hnear' : dist (bottomPath t) (bottomPath ((i : ℝ) / (N : ℝ))) < G.r / 4 := by
      simpa [bottomPath, N] using hnear
    rw [Metric.mem_ball, hbc i hi']
    exact lt_of_lt_of_le (by simpa [dist_comm] using hnear') (by linarith only [G.r_pos])
  have htcover : ∀ i < N, ∀ t ∈ Icc ((i : ℝ) / (N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
      topPath t ∈ Metric.ball (Dt i).center (G.r / 2) := by
    intro i hi t ht
    have hlast : G.N - 1 < G.N := by omega
    have hlastSucc : G.N - 1 + 1 = G.N := by omega
    have hlastReal : (((G.N - 1 + 1 : ℕ) : ℝ) / (G.N : ℝ)) = 1 := by
      rw [hlastSucc, hGNN]
    have hlastMem : (1 : ℝ) ∈ Icc (((G.N - 1 : ℕ) : ℝ) / (G.N : ℝ))
        (((G.N - 1 + 1 : ℕ) : ℝ) / (G.N : ℝ)) := by
      rw [hlastReal]
      constructor
      · apply (div_le_one hNreal).2
        exact_mod_cast (Nat.sub_le G.N 1)
      · exact le_rfl
    have hnear := G.cell_image i hi (G.N - 1) hlast t (by simpa [N] using ht) 1 hlastMem
    have hvert := (G.cells i hi (G.N - 1) hlast).2.1
    have htopNode : dist
        (Γ ((i : ℝ) / (N : ℝ), 1))
        (Γ ((i : ℝ) / (N : ℝ), ((G.N - 1 : ℕ) : ℝ) / (N : ℝ))) < G.r / 4 := by
      simpa [N, G.node_eq i (Nat.le_of_lt hi) G.N le_rfl,
        G.node_eq i (Nat.le_of_lt hi) (G.N - 1) (by omega), hGNN,
        hlastSucc] using hvert
    have hnear' : dist (Γ (t, 1))
        (Γ ((i : ℝ) / (N : ℝ), ((G.N - 1 : ℕ) : ℝ) / (N : ℝ))) < G.r / 4 := by
      simpa [N] using hnear
    have htri : dist (Γ (t, 1)) (Γ ((i : ℝ) / (N : ℝ), 1)) ≤
        dist (Γ (t, 1)) (Γ ((i : ℝ) / (N : ℝ), ((G.N - 1 : ℕ) : ℝ) / (N : ℝ))) +
            dist (Γ ((i : ℝ) / (N : ℝ), ((G.N - 1 : ℕ) : ℝ) / (N : ℝ)))
              (Γ ((i : ℝ) / (N : ℝ), 1)) := dist_triangle _ _ _
    have htopNode' : dist
        (Γ ((i : ℝ) / (N : ℝ), ((G.N - 1 : ℕ) : ℝ) / (N : ℝ)))
        (Γ ((i : ℝ) / (N : ℝ), 1)) < G.r / 4 := by
      simpa [dist_comm] using htopNode
    have hsum : dist (Γ (t, 1)) (Γ ((i : ℝ) / (N : ℝ), 1)) < G.r / 2 := by
      calc
        _ ≤ _ := htri
        _ < G.r / 4 + G.r / 4 := add_lt_add hnear' htopNode'
        _ = G.r / 2 := by ring
    rw [Metric.mem_ball, htc i (Nat.le_of_lt hi)]
    simpa [topPath, dist_comm] using hsum
  have hbdistance : ∀ i < N,
      dist (G.node (i + 1) 0) (G.node i 0) < G.r / 2 := by
    intro i hi
    exact lt_trans (G.cells i hi 0 (by omega)).1 (by linarith only [G.r_pos])
  have htdistance : ∀ i < N,
      dist (G.node (i + 1) N) (G.node i N) < G.r / 2 := by
    intro i hi
    have hlast : G.N - 1 < G.N := by omega
    have hsucc : G.N - 1 + 1 = G.N := by omega
    have hdiag := (G.cells i hi (G.N - 1) hlast).2.2
    have hvert := (G.cells i hi (G.N - 1) hlast).2.1
    have htri : dist (G.node (i + 1) N) (G.node i N) ≤
        dist (G.node (i + 1) N) (G.node i (N - 1)) +
          dist (G.node i (N - 1)) (G.node i N) := dist_triangle _ _ _
    have hdiag' : dist (G.node (i + 1) N) (G.node i (N - 1)) < G.r / 4 := by
      simpa [N, hsucc] using hdiag
    have hvert' : dist (G.node i (N - 1)) (G.node i N) < G.r / 4 := by
      simpa [N, hsucc, dist_comm] using hvert
    calc
      _ ≤ _ := htri
      _ < G.r / 4 + G.r / 4 := add_lt_add hdiag' hvert'
      _ = G.r / 2 := by ring
  have hboverlap : ∀ i < N, ∀ z ∈ Metric.ball (Db (i + 1)).center (G.r / 2),
      (Db i).solution z = (Db (i + 1)).solution z := by
    intro i hi z hz
    have hi1 : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
    have hcent := hbc (i + 1) hi1
    have hinit := homotopyGridRowChain_next_initial G 0 (by omega) i hi
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
      norm_num [Nat.cast_add]
    have hnode : G.node (i + 1) 0 = bottomPath (((i : ℝ) + 1) / (N : ℝ)) := by
      simpa [bottomPath, N, hcast] using G.node_eq (i + 1) hi1 0 (by omega)
    have hcent' : (Db (i + 1)).center = bottomPath (((i : ℝ) + 1) / (N : ℝ)) := by
      simpa [hcast] using hcent
    rw [hnode] at hinit
    have hinit' : (Db (i + 1)).initial = (Db i).solution
        (bottomPath (((i : ℝ) + 1) / (N : ℝ))) := by
      simpa only [Db] using hinit
    have hstart : (Db i).solution ((Db (i + 1)).center) =
        (Db (i + 1)).solution ((Db (i + 1)).center) := by
      calc
        (Db i).solution ((Db (i + 1)).center) =
            (Db i).solution (bottomPath (((i : ℝ) + 1) / (N : ℝ))) := by rw [hcent']
        _ =
            (Db (i + 1)).initial := by
              exact hinit'.symm
        _ = (Db (i + 1)).solution ((Db (i + 1)).center) :=
            (Db (i + 1)).solution_center.symm
    have hprevBall : Metric.ball (Db (i + 1)).center (G.r / 2) ⊆
        Metric.ball (Db i).center G.r := by
      intro w hw
      rw [Metric.mem_ball] at hw ⊢
      rw [hcent'] at hw
      rw [hbc i (Nat.le_of_lt hi)]
      have hstep : dist (bottomPath (((i : ℝ) + 1) / (N : ℝ)))
          (bottomPath ((i : ℝ) / (N : ℝ))) < G.r / 2 := by
        have hnext := hnode
        have hcurr : G.node i 0 = bottomPath ((i : ℝ) / (N : ℝ)) := by
          simpa [bottomPath, N] using G.node_eq i (Nat.le_of_lt hi) 0 (by omega)
        simpa only [hnode, hcurr] using hbdistance i hi
      calc
        dist w (bottomPath ((i : ℝ) / (N : ℝ))) ≤
            dist w (bottomPath (((i : ℝ) + 1) / (N : ℝ))) +
              dist (bottomPath (((i : ℝ) + 1) / (N : ℝ)))
                (bottomPath ((i : ℝ) / (N : ℝ))) := dist_triangle _ _ _
        _ < G.r / 2 + G.r / 2 := add_lt_add hw hstep
        _ = G.r := by ring
    have hnextCenter : (Db (i + 1)).center = G.node (i + 1) 0 := by
      change G.node (min (i + 1) G.N) 0 = G.node (i + 1) 0
      rw [Nat.min_eq_left (by omega)]
    have hbound : ∀ w ∈ Metric.ball (Db (i + 1)).center (G.r / 2),
        ‖H w‖ ≤ G.M := by
      intro w hw
      have hw' : w ∈ Metric.ball (G.node (i + 1) 0) (G.r / 2) := by
        simpa only [hnextCenter] using hw
      exact (G.data (i + 1) hi1 0 (by omega)).bounded w
        (Metric.ball_subset_ball (by linarith only [G.r_pos]) hw')
    have hF : ∀ w ∈ Metric.ball (Db (i + 1)).center (G.r / 2),
        HasDerivAt (Db i).solution (H w ((Db i).solution w)) w := by
      intro w hw
      exact (Db i).derivative w (hprevBall hw)
    have hG : ∀ w ∈ Metric.ball (Db (i + 1)).center (G.r / 2),
        HasDerivAt (Db (i + 1)).solution (H w ((Db (i + 1)).solution w)) w := by
      intro w hw
      exact (Db (i + 1)).derivative w (Metric.ball_subset_ball
        (by linarith only [G.r_pos]) hw)
    exact holomorphic_linear_system_solution_unique_of_eq_at
      (Db (i + 1)).center (G.r / 2) G.M H G.M_nonneg hbound hF hG
      (Metric.mem_ball_self (div_pos G.r_pos (by norm_num))) hz hstart
  have htoverlap : ∀ i < N, ∀ z ∈ Metric.ball (Dt (i + 1)).center (G.r / 2),
      (Dt i).solution z = (Dt (i + 1)).solution z := by
    intro i hi z hz
    have hi1 : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
    have hcent := htc (i + 1) hi1
    have hinit := homotopyGridRowChain_next_initial G N le_rfl i hi
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
      norm_num [Nat.cast_add]
    have hnode : G.node (i + 1) G.N = topPath (((i : ℝ) + 1) / (N : ℝ)) := by
      simpa [topPath, N, hGNN, hcast] using G.node_eq (i + 1) hi1 G.N le_rfl
    have hcent' : (Dt (i + 1)).center = topPath (((i : ℝ) + 1) / (N : ℝ)) := by
      simpa [hcast] using hcent
    rw [hnode] at hinit
    have hinit' : (Dt (i + 1)).initial = (Dt i).solution
        (topPath (((i : ℝ) + 1) / (N : ℝ))) := by
      simpa only [Dt] using hinit
    have hstart : (Dt i).solution ((Dt (i + 1)).center) =
        (Dt (i + 1)).solution ((Dt (i + 1)).center) := by
      calc
        (Dt i).solution ((Dt (i + 1)).center) =
            (Dt i).solution (topPath (((i : ℝ) + 1) / (N : ℝ))) := by rw [hcent']
        _ =
            (Dt (i + 1)).initial := by
              exact hinit'.symm
        _ = (Dt (i + 1)).solution ((Dt (i + 1)).center) :=
            (Dt (i + 1)).solution_center.symm
    have hprevBall : Metric.ball (Dt (i + 1)).center (G.r / 2) ⊆
        Metric.ball (Dt i).center G.r := by
      intro w hw
      rw [Metric.mem_ball] at hw ⊢
      rw [hcent'] at hw
      rw [htc i (Nat.le_of_lt hi)]
      have hstep : dist (topPath (((i : ℝ) + 1) / (N : ℝ)))
          (topPath ((i : ℝ) / (N : ℝ))) < G.r / 2 := by
        have hcurr : G.node i G.N = topPath ((i : ℝ) / (N : ℝ)) := by
          simpa [topPath, N, hGNN] using G.node_eq i (Nat.le_of_lt hi) G.N le_rfl
        simpa [N, hnode, hcurr] using htdistance i hi
      calc
        dist w (topPath ((i : ℝ) / (N : ℝ))) ≤
            dist w (topPath (((i : ℝ) + 1) / (N : ℝ))) +
              dist (topPath (((i : ℝ) + 1) / (N : ℝ)))
                (topPath ((i : ℝ) / (N : ℝ))) := dist_triangle _ _ _
        _ < G.r / 2 + G.r / 2 := add_lt_add hw hstep
        _ = G.r := by ring
    have hnextCenter : (Dt (i + 1)).center = G.node (i + 1) G.N := by
      change G.node (min (i + 1) G.N) G.N = G.node (i + 1) G.N
      rw [Nat.min_eq_left (by omega)]
    have hbound : ∀ w ∈ Metric.ball (Dt (i + 1)).center (G.r / 2),
        ‖H w‖ ≤ G.M := by
      intro w hw
      have hw' : w ∈ Metric.ball (G.node (i + 1) G.N) (G.r / 2) := by
        simpa only [hnextCenter] using hw
      exact (G.data (i + 1) hi1 G.N le_rfl).bounded w
        (Metric.ball_subset_ball (by linarith only [G.r_pos]) hw')
    have hF : ∀ w ∈ Metric.ball (Dt (i + 1)).center (G.r / 2),
        HasDerivAt (Dt i).solution (H w ((Dt i).solution w)) w := by
      intro w hw
      exact (Dt i).derivative w (hprevBall hw)
    have hG : ∀ w ∈ Metric.ball (Dt (i + 1)).center (G.r / 2),
        HasDerivAt (Dt (i + 1)).solution (H w ((Dt (i + 1)).solution w)) w := by
      intro w hw
      exact (Dt (i + 1)).derivative w (Metric.ball_subset_ball
        (by linarith only [G.r_pos]) hw)
    exact holomorphic_linear_system_solution_unique_of_eq_at
      (Dt (i + 1)).center (G.r / 2) G.M H G.M_nonneg hbound hF hG
      (Metric.mem_ball_self (div_pos G.r_pos (by norm_num))) hz hstart
  obtain ⟨bottom, hbottomCont, hbottomStart, hbottomEnd, hbottomFormula⟩ :=
    exists_continuous_lift_from_disk_chain H hbottomCont N hN G.r G.r_pos Db y
      (by simpa [Db] using hbc 0 (by omega)) hbi
      (by intro i hi; exact hbc i hi)
      hbcover hboverlap
  obtain ⟨top, htopCont, htopStart, htopEnd, htopFormula⟩ :=
    exists_continuous_lift_from_disk_chain H htopCont N hN G.r G.r_pos Dt y
      (by simpa [Dt] using htc 0 (by omega)) hti
      (by intro i hi; exact htc i hi)
      htcover htoverlap
  have hroute :
      finiteGridHorizontal (homotopyGridRight G) 0 0 N y =
        finiteGridHorizontal (homotopyGridRight G) 0 N N y := by
    let right : ℕ → ℕ → E → E := fun i j v =>
      if hi : i < G.N then
        if hj : j ≤ G.N then
          localPicardTransfer G.r G.M H (G.data i (Nat.le_of_lt hi) j hj) v
            (G.node (i + 1) j)
        else v
      else v
    have hright : right = homotopyGridRight G := by
      funext i j v
      simp [right, homotopyGridRight]
    have hgridTransfer := G.transfer_eq
    dsimp only at hgridTransfer
    simpa only [← hright, N] using hgridTransfer
  have hbottomRoute : (Db N).initial =
      finiteGridHorizontal (homotopyGridRight G) 0 0 N y := by
    simpa [Db] using homotopyGridRowChain_initial G 0 (by omega) N le_rfl
  have htopRoute : (Dt N).initial =
      finiteGridHorizontal (homotopyGridRight G) 0 N N y := by
    simpa [Dt] using homotopyGridRowChain_initial G N le_rfl N le_rfl
  have hbottomEndCenter : (Db N).center = bottomPath 1 := by
    simpa [Db, bottomPath, N, hNdiv] using hbc N le_rfl
  have htopEndCenter : (Dt N).center = topPath 1 := by
    simpa [Dt, topPath, N, hGNN] using htc N le_rfl
  have hendEq : bottom 1 = top 1 := by
    calc
      bottom 1 = (Db N).solution (bottomPath 1) := hbottomEnd
      _ = (Db N).solution (Db N).center := by rw [hbottomEndCenter]
      _ = (Db N).initial := (Db N).solution_center
      _ = finiteGridHorizontal (homotopyGridRight G) 0 0 N y := hbottomRoute
      _ = finiteGridHorizontal (homotopyGridRight G) 0 N N y := hroute
      _ = (Dt N).initial := htopRoute.symm
      _ = (Dt N).solution (Dt N).center := (Dt N).solution_center.symm
      _ = (Dt N).solution (topPath 1) := by rw [htopEndCenter]
      _ = top 1 := htopEnd.symm
  have hbottomFormula' : ∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
      bottom t = (homotopyGridRowChain G 0 (by omega) i).solution (Γ (t, 0)) := by
    simpa [Db, bottomPath, N] using hbottomFormula
  have htopFormula' : ∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
      top t = (homotopyGridRowChain G G.N le_rfl i).solution (Γ (t, 1)) := by
    simpa [Dt, topPath, N] using htopFormula
  have hbBound : ∀ i ≤ G.N, ∀ z ∈ Metric.ball (Db i).center G.r, ‖H z‖ ≤ G.M := by
    intro i hi z hz
    have hnode : (Db i).center = G.node i 0 := by
      calc
        (Db i).center = bottomPath ((i : ℝ) / (N : ℝ)) := hbc i hi
        _ = G.node i 0 := by
          change Γ ((i : ℝ) / (G.N : ℝ), 0) = G.node i 0
          simpa using (G.node_eq i hi 0 (by omega)).symm
    have hz' : z ∈ Metric.ball (G.node i 0) G.r := by simpa [hnode] using hz
    exact (G.data i hi 0 (by omega)).bounded z hz'
  have htBound : ∀ i ≤ G.N, ∀ z ∈ Metric.ball (Dt i).center G.r, ‖H z‖ ≤ G.M := by
    intro i hi z hz
    have hnode : (Dt i).center = G.node i G.N := by
      calc
        (Dt i).center = topPath ((i : ℝ) / (N : ℝ)) := htc i hi
        _ = G.node i G.N := by
          change Γ ((i : ℝ) / (G.N : ℝ), 1) = G.node i G.N
          simpa [hGNN] using (G.node_eq i hi G.N le_rfl).symm
    have hz' : z ∈ Metric.ball (G.node i G.N) G.r := by simpa [hnode] using hz
    exact (G.data i hi G.N le_rfl).bounded z hz'
  exact ⟨bottom, top, hbottomCont, htopCont, hbottomStart, htopStart, hendEq,
    hbottomFormula', htopFormula', hbc, hbBound, hbcover, hboverlap,
    htc, htBound, htcover, htoverlap⟩


end DOZZ.Proofs
