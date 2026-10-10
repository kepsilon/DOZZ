/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Piecewise
public import DOZZ.Hypergeom.ODE.FiniteDiskChain

/-! A finite chain of local Picard solutions glues to a continuous lift of its path. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (H : ℂ → E →L[ℂ] E) (r : ℝ)

/-- The partial lift after applying the first `n` local Picard patches. -/
noncomputable def finiteChainPathLift (γ : ℝ → ℂ)
    (D : ℕ → HolomorphicDiskSolution H r) (N : ℕ) (y : E) : ℕ → ℝ → E
  | 0 => fun _ => y
  | n + 1 =>
      (Iic ((n : ℝ) / (N : ℝ))).piecewise
        (finiteChainPathLift γ D N y n)
        (fun t => (D n).solution (γ t))

theorem exists_continuous_lift_from_disk_chain
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (N : ℕ) (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (D : ℕ → HolomorphicDiskSolution H r) (y : E)
    (hstartCenter : (D 0).center = γ 0) (hstartValue : (D 0).initial = y)
    (hcenters : ∀ i ≤ N, (D i).center = γ ((i : ℝ) / (N : ℝ)))
    (hcover : ∀ i < N, ∀ t ∈ Icc ((i : ℝ) / (N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
      γ t ∈ Metric.ball ((D i).center) (r / 2))
    (hoverlap : ∀ i < N, ∀ z ∈ Metric.ball ((D (i + 1)).center) (r / 2),
      (D i).solution z = (D (i + 1)).solution z) :
    ∃ F : ℝ → E,
      ContinuousOn F (Icc (0 : ℝ) 1) ∧ F 0 = y ∧
        F 1 = (D N).solution (γ 1) ∧
        ∀ i < N, ∀ t ∈ Icc ((i : ℝ) / (N : ℝ))
          (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
          F t = (D i).solution (γ t) := by
  classical
  let τ : ℕ → ℝ := fun i => (i : ℝ) / (N : ℝ)
  let P : ℕ → ℝ → E := finiteChainPathLift H r γ D N y
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hτmono (i j : ℕ) (hij : i ≤ j) : τ i ≤ τ j := by
    apply (div_le_div_iff_of_pos_right hNreal).2
    exact_mod_cast hij
  have hτ01 (i : ℕ) (hi : i ≤ N) : τ i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [τ]
      positivity
    · dsimp [τ]
      apply (div_le_one hNreal).2
      exact_mod_cast hi
  have hjoin : ∀ m ≤ N,
      (∀ i < m, ∀ t ∈ Icc (τ i) (τ (i + 1)),
        P m t = (D i).solution (γ t)) →
      P m (τ m) = (D m).solution (γ (τ m)) := by
    intro m hm hformula
    cases m with
    | zero =>
        have hτ0 : τ 0 = 0 := by simp [τ]
        calc
          P 0 (τ 0) = y := by simp [P, finiteChainPathLift]
          _ = (D 0).initial := hstartValue.symm
          _ = (D 0).solution ((D 0).center) := (D 0).solution_center.symm
          _ = (D 0).solution (γ (τ 0)) := by rw [hstartCenter, hτ0]
    | succ n =>
        have hnN : n < N := by omega
        have hprev := hformula n (by omega) (τ (n + 1))
          ⟨hτmono n (n + 1) (by omega), le_rfl⟩
        have hcenterNext : (D (n + 1)).center = γ (τ (n + 1)) := by
          simpa [τ] using hcenters (n + 1) (by omega)
        have hsame := hoverlap n hnN (γ (τ (n + 1)))
          (by rw [← hcenterNext]; exact Metric.mem_ball_self (by linarith))
        calc
          P (n + 1) (τ (n + 1)) = (D n).solution (γ (τ (n + 1))) := hprev
          _ = (D (n + 1)).solution (γ (τ (n + 1))) := hsame
  have hstage : ∀ m ≤ N,
      ContinuousOn (P m) (Icc (0 : ℝ) (τ m)) ∧
        ∀ i < m, ∀ t ∈ Icc (τ i) (τ (i + 1)),
          P m t = (D i).solution (γ t) := by
    intro m hm
    induction m with
    | zero =>
        have hτ0 : τ 0 = 0 := by simp [τ]
        constructor
        · simp [P, finiteChainPathLift, hτ0]
        · intro i hi
          omega
    | succ m ih =>
        have hmN : m < N := by omega
        have ⟨hprevCont, hprevFormula⟩ := ih (by omega)
        have htNext : τ m ≤ τ (m + 1) := hτmono m (m + 1) (by omega)
        have hτm_nonneg : 0 ≤ τ m := (hτ01 m (by omega)).1
        have hτnext_le : τ (m + 1) ≤ 1 := (hτ01 (m + 1) (by omega)).2
        have hjoinm := hjoin m (by omega) hprevFormula
        let g : ℝ → E := fun t => (D m).solution (γ t)
        have hDcont : ContinuousOn (D m).solution
            (Metric.ball (D m).center r) := by
          apply continuousOn_of_forall_continuousAt
          intro z hz
          exact ((D m).derivative z hz).continuousAt
        have hγseg : ContinuousOn γ (Icc (τ m) (τ (m + 1))) :=
          hγ.mono (by
            intro t ht
            exact ⟨le_trans hτm_nonneg ht.1, le_trans ht.2 hτnext_le⟩)
        have hGcont : ContinuousOn g (Icc (τ m) (τ (m + 1))) := by
          apply hDcont.comp hγseg
          intro t ht
          apply Metric.ball_subset_ball (by linarith : r / 2 ≤ r)
          exact hcover m hmN t ht
        have hboundary : ∀ t ∈ Icc (0 : ℝ) (τ (m + 1)) ∩
            frontier (Iic (τ m)), P m t = g t := by
          intro t ht
          have hfront : t = τ m := by
            simpa [frontier_Iic, mem_singleton_iff] using ht.2
          rw [hfront]
          exact hjoinm
        have hprevDomain : Icc (0 : ℝ) (τ (m + 1)) ∩ closure (Iic (τ m)) ⊆
            Icc (0 : ℝ) (τ m) := by
          intro t ht
          have ht' : t ≤ τ m := by simpa [closure_Iic] using ht.2
          exact ⟨ht.1.1, ht'⟩
        have hnewDomain : Icc (0 : ℝ) (τ (m + 1)) ∩ closure (Iic (τ m))ᶜ ⊆
            Icc (τ m) (τ (m + 1)) := by
          intro t ht
          have htLower : τ m ≤ t := by simpa [closure_Ioi] using ht.2
          exact ⟨htLower, ht.1.2⟩
        have hnewCont : ContinuousOn g
            (Icc (0 : ℝ) (τ (m + 1)) ∩ closure (Iic (τ m))ᶜ) :=
          hGcont.mono hnewDomain
        have hcont : ContinuousOn (P (m + 1))
            (Icc (0 : ℝ) (τ (m + 1))) := by
          have hpiece : ContinuousOn ((Iic (τ m)).piecewise (P m) g)
              (Icc (0 : ℝ) (τ (m + 1))) :=
            (hprevCont.mono hprevDomain).piecewise hboundary hnewCont
          simpa [P, finiteChainPathLift, g, τ] using hpiece
        constructor
        · exact hcont
        · intro i hi t ht
          by_cases him : i < m
          · have htOld : t ≤ τ m := by
              exact le_trans ht.2 (hτmono (i + 1) m (by omega))
            have hprev := hprevFormula i him t ht
            have htmem : t ∈ Iic (τ m) := htOld
            have hpiece : P (m + 1) t = P m t := by
              change (Iic (τ m)).piecewise (P m)
                (fun t => (D m).solution (γ t)) t = P m t
              exact Set.piecewise_eq_of_mem (s := Iic (τ m)) (f := P m)
                (g := fun t => (D m).solution (γ t)) htmem
            rw [hpiece]
            exact hprev
          · have hiEq : i = m := by omega
            subst i
            have htLower := ht.1
            by_cases heq : t = τ m
            · subst t
              have hpiece : P (m + 1) (τ m) = P m (τ m) := by
                change (Iic (τ m)).piecewise (P m)
                  (fun t => (D m).solution (γ t)) (τ m) = P m (τ m)
                exact Set.piecewise_eq_of_mem (s := Iic (τ m)) (f := P m)
                  (g := fun t => (D m).solution (γ t))
                  (show τ m ∈ Iic (τ m) from le_rfl)
              rw [hpiece]
              exact hjoinm
            · have htNot : t ∉ Iic (τ m) := by
                simp only [mem_Iic]
                exact not_le.mpr (lt_of_le_of_ne htLower (Ne.symm heq))
              have hpiece : P (m + 1) t = g t := by
                change (Iic (τ m)).piecewise (P m)
                  (fun t => (D m).solution (γ t)) t = (D m).solution (γ t)
                exact Set.piecewise_eq_of_notMem (s := Iic (τ m)) (f := P m)
                  (g := fun t => (D m).solution (γ t)) htNot
              rw [hpiece]
  have ⟨hcont, hformula⟩ := hstage N le_rfl
  have hτN : τ N = 1 := by
    dsimp [τ]
    exact div_self (by exact_mod_cast hN.ne')
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hstart : P N 0 = y := by
    have hmem : (0 : ℝ) ∈ Icc (τ 0) (τ 1) := by
      exact ⟨by simp [τ], by dsimp [τ]; positivity⟩
    have hval := hformula 0 (by omega) 0 hmem
    calc
      P N 0 = (D 0).solution (γ 0) := hval
      _ = (D 0).solution (D 0).center := by rw [hstartCenter]
      _ = (D 0).initial := (D 0).solution_center
      _ = y := hstartValue
  have hend : P N 1 = (D N).solution (γ 1) := by
    rw [← hτN]
    exact hjoin N le_rfl hformula
  refine ⟨P N, ?_, hstart, hend, ?_⟩
  · simpa [hτN] using hcont
  · intro i hi t ht
    exact hformula i hi t ht

end DOZZ.Proofs
