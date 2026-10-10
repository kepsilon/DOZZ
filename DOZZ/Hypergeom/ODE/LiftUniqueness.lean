/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import DOZZ.Hypergeom.ODE.UniquenessEndpoints

/-! Uniqueness of continuous lifts along a path from local holomorphic charts. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A local holomorphic ODE chart for a continuous path lift near one path parameter. -/
structure PathSolutionChart (γ : ℝ → ℂ) (H : ℂ → E →L[ℂ] E)
    (F : ℝ → E) (t : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  solution : ℂ → E
  coefficient_bound : ∀ z ∈ Metric.ball (γ t) radius, ‖H z‖ ≤ bound
  derivative : ∀ z ∈ Metric.ball (γ t) radius,
    HasDerivAt solution (H z (solution z)) z
  local_agrees : ∃ δ : ℝ, 0 < δ ∧
    ∀ s ∈ Icc (0 : ℝ) 1, dist s t < δ → F s = solution (γ s)

/-- Pull a local ODE chart back through an orientation-preserving affine change of path
parameter. -/
def PathSolutionChart.affineReparam
    {H : ℂ → E →L[ℂ] E} {γ : ℝ → ℂ} {F : ℝ → E} {a c u : ℝ}
    (A : PathSolutionChart γ H F (a + c * u)) (hc : 0 < c)
    (hparam : ∀ s ∈ Icc (0 : ℝ) 1, a + c * s ∈ Icc (0 : ℝ) 1) :
    PathSolutionChart (fun s => γ (a + c * s)) H
      (fun s => F (a + c * s)) u := by
  refine {
    radius := A.radius
    radius_pos := A.radius_pos
    bound := A.bound
    bound_nonneg := A.bound_nonneg
    solution := A.solution
    coefficient_bound := A.coefficient_bound
    derivative := A.derivative
    local_agrees := ?_
  }
  obtain ⟨δ, hδ, hagree⟩ := A.local_agrees
  refine ⟨δ / c, div_pos hδ hc, ?_⟩
  intro s hs hdist
  have hdistScale : dist (a + c * s) (a + c * u) = c * dist s u := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖(a + c * s) - (a + c * u)‖ = ‖c * (s - u)‖ := by congr 1; ring
      _ = ‖c‖ * ‖s - u‖ := norm_mul _ _
      _ = c * dist s u := by rw [Real.norm_eq_abs, abs_of_pos hc, dist_eq_norm]
  have hdist' : dist (a + c * s) (a + c * u) < δ := by
    rw [hdistScale]
    calc
      c * dist s u < c * (δ / c) := mul_lt_mul_of_pos_left hdist hc
      _ = δ := by field_simp
  exact hagree (a + c * s) (hparam s hs) hdist'

/-- Two continuous lifts that are locally represented by holomorphic solutions and agree at the
initial point agree throughout the path. The proof shows their equality locus is clopen in the
connected parameter interval; openness is local ODE uniqueness in overlapping charts. -/
theorem continuous_path_solution_lifts_unique
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (H : ℂ → E →L[ℂ] E) {F G : ℝ → E}
    (hFcont : ContinuousOn F (Icc (0 : ℝ) 1))
    (hGcont : ContinuousOn G (Icc (0 : ℝ) 1))
    (hFchart : ∀ t ∈ Icc (0 : ℝ) 1, Nonempty (PathSolutionChart γ H F t))
    (hGchart : ∀ t ∈ Icc (0 : ℝ) 1, Nonempty (PathSolutionChart γ H G t))
    (hstart : F 0 = G 0) : ∀ t ∈ Icc (0 : ℝ) 1, F t = G t := by
  let I : Type := Icc (0 : ℝ) 1
  let u : I → E := fun t => F t
  let v : I → E := fun t => G t
  have hu : Continuous u := by
    change Continuous (fun t : I => F t.1)
    exact hFcont.domRestrict
  have hv : Continuous v := by
    change Continuous (fun t : I => G t.1)
    exact hGcont.domRestrict
  let S : Set I := {t | u t = v t}
  have hclosed : IsClosed S := by
    change IsClosed {t : I | u t = v t}
    exact isClosed_eq hu hv
  have hopen : IsOpen S := by
    apply Metric.isOpen_iff.mpr
    intro t ht
    obtain ⟨A⟩ := hFchart t t.2
    obtain ⟨B⟩ := hGchart t t.2
    obtain ⟨δA, hδA, hAagree⟩ := A.local_agrees
    obtain ⟨δB, hδB, hBagree⟩ := B.local_agrees
    let ρ := min A.radius B.radius
    have hρ : 0 < ρ := lt_min A.radius_pos B.radius_pos
    have hAat : A.solution (γ t) = F t := by
      symm
      exact hAagree t t.2 (by simpa using hδA)
    have hBat : B.solution (γ t) = G t := by
      symm
      exact hBagree t t.2 (by simpa using hδB)
    have htval : F t = G t := by
      change u t = v t at ht
      exact ht
    have hsameAt : A.solution (γ t) = B.solution (γ t) := by
      calc
        A.solution (γ t) = F t := hAat
        _ = G t := htval
        _ = B.solution (γ t) := hBat.symm
    obtain ⟨δγ, hδγ, hγclose⟩ :=
      (Metric.continuousWithinAt_iff.mp (hγ.continuousWithinAt t.2)) ρ hρ
    let δ := min δγ (min δA δB)
    refine ⟨δ, lt_min hδγ (lt_min hδA hδB), ?_⟩
    intro s hs
    have hst : dist (s : ℝ) t < δ := Metric.mem_ball.mp hs
    have hstγ : dist (γ s) (γ t) < ρ := hγclose s.2
      (lt_of_lt_of_le hst (min_le_left _ _))
    have hAagreeS : F s = A.solution (γ s) :=
      hAagree s s.2 (lt_of_lt_of_le hst (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hBagreeS : G s = B.solution (γ s) :=
      hBagree s s.2 (lt_of_lt_of_le hst
        (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hAderiv : ∀ z ∈ Metric.ball (γ t) ρ,
        HasDerivAt A.solution (H z (A.solution z)) z := by
      intro z hz
      exact A.derivative z (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hBderiv : ∀ z ∈ Metric.ball (γ t) ρ,
        HasDerivAt B.solution (H z (B.solution z)) z := by
      intro z hz
      exact B.derivative z (Metric.ball_subset_ball (min_le_right _ _) hz)
    have hbound : ∀ z ∈ Metric.ball (γ t) ρ, ‖H z‖ ≤ max A.bound B.bound := by
      intro z hz
      exact (A.coefficient_bound z
        (Metric.ball_subset_ball (min_le_left _ _) hz)).trans (le_max_left _ _)
    have hlocalEq := holomorphic_linear_system_solution_unique_of_eq_at
      (γ t) ρ (max A.bound B.bound) H (le_trans A.bound_nonneg (le_max_left _ _))
      hbound hAderiv hBderiv (Metric.mem_ball_self hρ)
      (Metric.mem_ball.mpr hstγ) hsameAt
    change F s = G s
    calc
      F s = A.solution (γ s) := hAagreeS
      _ = B.solution (γ s) := hlocalEq
      _ = G s := hBagreeS.symm
  have hconn : ConnectedSpace I :=
    Subtype.connectedSpace ⟨⟨0, by simp⟩, isPreconnected_Icc⟩
  have hnonempty : S.Nonempty := by
    refine ⟨⟨0, by simp⟩, ?_⟩
    change F 0 = G 0
    exact hstart
  have huniv : S = Set.univ := by
    rcases (@isClopen_iff I _ hconn.toPreconnectedSpace S).mp ⟨hclosed, hopen⟩ with hempty | huniv
    · have hfalse : False := by
        rcases hnonempty with ⟨t, ht⟩
        rw [hempty] at ht
        simp at ht
      exact hfalse.elim
    · exact huniv
  intro t ht
  have hmem : (⟨t, ht⟩ : I) ∈ S := by rw [huniv]; trivial
  exact hmem

end DOZZ.Proofs
