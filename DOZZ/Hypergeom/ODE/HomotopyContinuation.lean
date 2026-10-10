/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.HomotopyGridLifts
public import DOZZ.Hypergeom.ODE.PathContinuation

/-! Continuation endpoints agree along fixed-endpoint homotopies in a regular domain. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Two finite-chain continuations from the same initial value have the same endpoint when their
paths are fixed-endpoint homotopic through an open regular domain. -/
theorem homotopy_path_continuation_endpoint_eq
    {Γ : ℝ × ℝ → ℂ} (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (himage : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Γ p ∈ U)
    (z₀ z₁ : ℂ)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, Γ (0, s) = z₀)
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, Γ (1, s) = z₁)
    (y : E)
    (A : PathContinuationLift (fun t => Γ (t, 0)) H y)
    (B : PathContinuationLift (fun t => Γ (t, 1)) H y) :
    A.value 1 = B.value 1 := by
  let bottomPath : ℝ → ℂ := fun t => Γ (t, 0)
  let topPath : ℝ → ℂ := fun t => Γ (t, 1)
  have hbottomCont : ContinuousOn bottomPath (Icc (0 : ℝ) 1) := by
    apply hΓ.comp (by fun_prop)
    intro t ht
    exact ⟨ht, by norm_num⟩
  have htopCont : ContinuousOn topPath (Icc (0 : ℝ) 1) := by
    apply hΓ.comp (by fun_prop)
    intro t ht
    exact ⟨ht, by norm_num⟩
  let G := homotopyPicardGridOf hΓ U hU H hH himage z₀ z₁ hleft hright y
  obtain ⟨bottom, top, hbottomCont', htopCont', hbottomStart, htopStart, hendEq,
      hbottomFormula, htopFormula, hbottomCenters, hbottomBound, hbottomCover,
      hbottomOverlap, htopCenters, htopBound, htopCover, htopOverlap⟩ :=
    homotopy_grid_boundary_lifts_endpoint_eq_with_formulas G hΓ
  let Db : ℕ → HolomorphicDiskSolution H G.r :=
    homotopyGridRowChain G 0 (by omega)
  let Dt : ℕ → HolomorphicDiskSolution H G.r :=
    homotopyGridRowChain G G.N le_rfl
  have hDbInitial : (Db 0).initial = y := by
    calc
      (Db 0).initial = finiteGridHorizontal (homotopyGridRight G) 0 0 0 y := by
        simpa [Db] using homotopyGridRowChain_initial G 0 (by omega) 0 (by omega)
      _ = y := by simp [finiteGridHorizontal]
  have hDtInitial : (Dt 0).initial = y := by
    calc
      (Dt 0).initial = finiteGridHorizontal (homotopyGridRight G) 0 G.N 0 y := by
        simpa [Dt] using homotopyGridRowChain_initial G G.N le_rfl 0 (by omega)
      _ = y := by simp [finiteGridHorizontal]
  let gridBottom : PathContinuationLift bottomPath H y := {
    subdivision := G.N
    subdivision_pos := G.N_pos
    radius := G.r
    coefficient_bound := G.M
    radius_pos := G.r_pos
    coefficient_bound_nonneg := G.M_nonneg
    disks := Db
    disks_initial := hDbInitial
    centers := by
      intro i hi
      simpa [Db, bottomPath] using hbottomCenters i hi
    operator_bound := by
      intro i hi z hz
      exact hbottomBound i hi z hz
    path_cover := by
      intro i hi t ht
      simpa [bottomPath] using hbottomCover i hi t ht
    overlap := by
      intro i hi z hz
      exact hbottomOverlap i hi z hz
    value := bottom
    value_continuous := hbottomCont'
    value_initial := hbottomStart
    local_formula := by
      intro i hi t ht
      simpa [Db, bottomPath] using hbottomFormula i hi t ht
  }
  let gridTop : PathContinuationLift topPath H y := {
    subdivision := G.N
    subdivision_pos := G.N_pos
    radius := G.r
    coefficient_bound := G.M
    radius_pos := G.r_pos
    coefficient_bound_nonneg := G.M_nonneg
    disks := Dt
    disks_initial := hDtInitial
    centers := by
      intro i hi
      simpa [Dt, topPath] using htopCenters i hi
    operator_bound := by
      intro i hi z hz
      exact htopBound i hi z hz
    path_cover := by
      intro i hi t ht
      simpa [topPath] using htopCover i hi t ht
    overlap := by
      intro i hi z hz
      exact htopOverlap i hi z hz
    value := top
    value_continuous := htopCont'
    value_initial := htopStart
    local_formula := by
      intro i hi t ht
      simpa [Dt, topPath] using htopFormula i hi t ht
  }
  have hbottomEq := path_continuation_lifts_unique hbottomCont H y A gridBottom
  have htopEq := path_continuation_lifts_unique htopCont H y gridTop B
  calc
    A.value 1 = bottom 1 := hbottomEq 1 (by norm_num)
    _ = top 1 := hendEq
    _ = B.value 1 := htopEq 1 (by norm_num)

end DOZZ.Proofs
