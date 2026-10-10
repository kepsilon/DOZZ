/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.PathChainUniqueness
public import DOZZ.Hypergeom.ODE.UniformPathDisks

/-! Packaged finite-chain continuation along a path, with existence and uniqueness. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite Picard continuation of the initial value `y` along `γ`, including its local disk data
and continuous path lift. -/
structure PathContinuationLift (γ : ℝ → ℂ) (H : ℂ → E →L[ℂ] E) (y : E) where
  subdivision : ℕ
  subdivision_pos : 0 < subdivision
  radius : ℝ
  coefficient_bound : ℝ
  radius_pos : 0 < radius
  coefficient_bound_nonneg : 0 ≤ coefficient_bound
  disks : ℕ → HolomorphicDiskSolution H radius
  disks_initial : (disks 0).initial = y
  centers : ∀ i ≤ subdivision,
    (disks i).center = γ ((i : ℝ) / (subdivision : ℝ))
  operator_bound : ∀ i ≤ subdivision, ∀ z ∈ Metric.ball (disks i).center radius,
    ‖H z‖ ≤ coefficient_bound
  path_cover : ∀ i < subdivision, ∀ t ∈ Icc ((i : ℝ) / (subdivision : ℝ))
    (((i + 1 : ℕ) : ℝ) / (subdivision : ℝ)),
    γ t ∈ Metric.ball (disks i).center (radius / 2)
  overlap : ∀ i < subdivision, ∀ z ∈ Metric.ball (disks (i + 1)).center (radius / 2),
    (disks i).solution z = (disks (i + 1)).solution z
  value : ℝ → E
  value_continuous : ContinuousOn value (Icc (0 : ℝ) 1)
  value_initial : value 0 = y
  local_formula : ∀ i < subdivision, ∀ t ∈ Icc ((i : ℝ) / (subdivision : ℝ))
    (((i + 1 : ℕ) : ℝ) / (subdivision : ℝ)),
    value t = (disks i).solution (γ t)

/-- A disk solution gives a packaged lift along a constant path at its center. -/
def constant_path_continuation_lift
    {H : ℂ → E →L[ℂ] E} {y : E} (z : ℂ) (r M : ℝ) (hr : 0 < r)
    (hM : 0 ≤ M) (D : HolomorphicDiskSolution H r)
    (hcenter : D.center = z)
    (hbound : ∀ w ∈ Metric.ball z r, ‖H w‖ ≤ M)
    (hinitial : D.initial = y) : PathContinuationLift (fun _ : ℝ => z) H y := by
  refine {
    subdivision := 1
    subdivision_pos := by norm_num
    radius := r
    coefficient_bound := M
    radius_pos := hr
    coefficient_bound_nonneg := hM
    disks := fun _ => D
    disks_initial := hinitial
    centers := ?_
    operator_bound := ?_
    path_cover := ?_
    overlap := ?_
    value := fun _ => y
    value_continuous := continuousOn_const
    value_initial := rfl
    local_formula := ?_
  }
  · intro i hi
    simp [hcenter]
  · intro i hi w hw
    exact hbound w (by simpa [hcenter] using hw)
  · intro i hi t ht
    simpa [hcenter] using
      (Metric.mem_ball_self (show 0 < r / 2 by linarith) :
        z ∈ Metric.ball z (r / 2))
  · intro i hi w hw
    rfl
  · intro i hi t ht
    calc
      y = D.solution D.center := (D.solution_center.trans hinitial).symm
      _ = D.solution z := by rw [hcenter]

/-- Every mesh point of a positive equal subdivision belongs to `[0,1]`. -/
theorem pathContinuationMeshPoint_mem_unitInterval {N i : ℕ} (hN : 0 < N)
    (hi : i ≤ N) : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  constructor
  · positivity
  · apply (div_le_one hNreal).2
    exact_mod_cast hi

/-- Every segment of a positive equal subdivision lies in `[0,1]`. -/
theorem pathContinuationSegment_mem_unitInterval {N i : ℕ} (hN : 0 < N)
    (hi : i < N) {t : ℝ}
    (ht : t ∈ Icc ((i : ℝ) / (N : ℝ)) (((i + 1 : ℕ) : ℝ) / (N : ℝ))) :
    t ∈ Icc (0 : ℝ) 1 := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hi1 : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
  have hupper : ((i + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
    apply (div_le_one hNreal).2
    exact_mod_cast hi1
  exact ⟨le_trans (by positivity) ht.1, le_trans ht.2 hupper⟩

/-- A packaged finite-chain lift inherits local holomorphic charts along its path. -/
theorem path_continuation_lift_has_solution_charts
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {H : ℂ → E →L[ℂ] E} {y : E} (A : PathContinuationLift γ H y) :
    ∀ t ∈ Icc (0 : ℝ) 1, Nonempty (PathSolutionChart γ H A.value t) := by
  exact disk_chain_lift_has_path_solution_charts hγ A.subdivision A.subdivision_pos
    A.radius A.coefficient_bound A.radius_pos A.coefficient_bound_nonneg H A.disks
    A.centers A.operator_bound A.path_cover A.overlap A.local_formula

/-- Re-express a continuation along another path function with the same values on `[0,1]`. -/
def path_continuation_lift_congr
    {H : ℂ → E →L[ℂ] E} {y : E} {γ δ : ℝ → ℂ}
    (A : PathContinuationLift γ H y)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t = δ t) :
    PathContinuationLift δ H y := by
  refine {
    subdivision := A.subdivision
    subdivision_pos := A.subdivision_pos
    radius := A.radius
    coefficient_bound := A.coefficient_bound
    radius_pos := A.radius_pos
    coefficient_bound_nonneg := A.coefficient_bound_nonneg
    disks := A.disks
    disks_initial := A.disks_initial
    centers := ?_
    operator_bound := A.operator_bound
    path_cover := ?_
    overlap := A.overlap
    value := A.value
    value_continuous := A.value_continuous
    value_initial := A.value_initial
    local_formula := ?_
  }
  · intro i hi
    have hτ := pathContinuationMeshPoint_mem_unitInterval A.subdivision_pos hi
    calc
      (A.disks i).center = γ ((i : ℝ) / (A.subdivision : ℝ)) := A.centers i hi
      _ = δ ((i : ℝ) / (A.subdivision : ℝ)) := hpath _ hτ
  · intro i hi t ht
    have ht01 := pathContinuationSegment_mem_unitInterval A.subdivision_pos hi ht
    rw [← hpath t ht01]
    exact A.path_cover i hi t ht
  · intro i hi t ht
    have ht01 := pathContinuationSegment_mem_unitInterval A.subdivision_pos hi ht
    calc
      A.value t = (A.disks i).solution (γ t) := A.local_formula i hi t ht
      _ = (A.disks i).solution (δ t) := by rw [hpath t ht01]

/-- Change the named initial vector of a packaged lift along an equality. -/
def path_continuation_lift_initial_congr
    {H : ℂ → E →L[ℂ] E} {y y' : E} {γ : ℝ → ℂ}
    (A : PathContinuationLift γ H y) (h : y = y') :
    PathContinuationLift γ H y' := by
  refine {
    subdivision := A.subdivision
    subdivision_pos := A.subdivision_pos
    radius := A.radius
    coefficient_bound := A.coefficient_bound
    radius_pos := A.radius_pos
    coefficient_bound_nonneg := A.coefficient_bound_nonneg
    disks := A.disks
    disks_initial := A.disks_initial.trans h
    centers := A.centers
    operator_bound := A.operator_bound
    path_cover := A.path_cover
    overlap := A.overlap
    value := A.value
    value_continuous := A.value_continuous
    value_initial := A.value_initial.trans h
    local_formula := A.local_formula
  }

/-- Every path in an open regular domain has a packaged finite-chain continuation from any initial
vector. -/
theorem exists_path_continuation_lift [CompleteSpace E]
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) (y : E) :
    Nonempty (PathContinuationLift γ H y) := by
  obtain ⟨r, M, hr, hM, hlocal, N, hN, D, hD0c, hD0i, hDNc,
      hcenters, hinitials, hcover, hoverlap⟩ :=
    exists_holomorphic_path_continuation_chain hγ U hU H hH hpath y
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcoord (i : ℕ) (hi : i ≤ N) :
      (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hNreal).2
      exact_mod_cast hi
  have hbound : ∀ i ≤ N, ∀ z ∈ Metric.ball (D i).center r, ‖H z‖ ≤ M := by
    intro i hi z hz
    have h := (hlocal ((i : ℝ) / (N : ℝ)) (hcoord i hi)).2
    have hz' : z ∈ Metric.ball (γ ((i : ℝ) / (N : ℝ))) r := by
      rw [← hcenters i hi]
      exact hz
    exact h z hz'
  have hoverlap' : ∀ i < N, ∀ z ∈ Metric.ball (D (i + 1)).center (r / 2),
      (D i).solution z = (D (i + 1)).solution z := by
    intro i hi z hz
    have hc := hcenters (i + 1) (Nat.succ_le_iff.mpr hi)
    have hz' : z ∈ Metric.ball (γ (((i + 1 : ℕ) : ℝ) / (N : ℝ))) (r / 2) := by
      simpa [hc] using hz
    exact hoverlap i hi z hz'
  obtain ⟨F, hFcont, hFstart, _, hFformula⟩ :=
    exists_continuous_lift_from_disk_chain H hγ N hN r hr D y hD0c hD0i
      hcenters hcover hoverlap'
  exact ⟨⟨N, hN, r, M, hr, hM, D, hD0i, hcenters, hbound, hcover, hoverlap',
    F, hFcont, hFstart, hFformula⟩⟩

/-- The terminal path-lift value is the evaluation of the final disk solution. -/
theorem path_continuation_lift_value_one_eq_final_disk
    {γ : ℝ → ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (A : PathContinuationLift γ H y) :
    A.value 1 = (A.disks A.subdivision).solution (γ 1) := by
  let i := A.subdivision - 1
  have hi : i < A.subdivision := by have hpos := A.subdivision_pos; dsimp [i]; omega
  have hsucc : i + 1 = A.subdivision := by
    have hpos := A.subdivision_pos
    dsimp [i]
    omega
  have hNreal : 0 < (A.subdivision : ℝ) := by exact_mod_cast A.subdivision_pos
  have hseg : (1 : ℝ) ∈ Icc ((i : ℝ) / (A.subdivision : ℝ))
      (((i + 1 : ℕ) : ℝ) / (A.subdivision : ℝ)) := by
    constructor
    · apply (div_le_one hNreal).2
      exact_mod_cast (show i ≤ A.subdivision by omega)
    · rw [hsucc, div_self (by exact_mod_cast A.subdivision_pos.ne')]
  have hform := A.local_formula i hi 1 hseg
  have hcenter := A.centers A.subdivision le_rfl
  have hNdiv : (A.subdivision : ℝ) / (A.subdivision : ℝ) = 1 :=
    div_self hNreal.ne'
  have hfinalCenter : (A.disks (i + 1)).center = γ 1 := by
    rw [hsucc]
    simpa [hNdiv] using hcenter
  have hover := A.overlap i hi (γ 1) (by
    rw [← hfinalCenter]
    exact Metric.mem_ball_self (by linarith [A.radius_pos]))
  calc
    A.value 1 = (A.disks i).solution (γ 1) := hform
    _ = (A.disks (i + 1)).solution (γ 1) := hover
    _ = (A.disks A.subdivision).solution (γ 1) := by rw [hsucc]

/-- Restrict a packaged lift to an affine subinterval of its path. A fresh finite chain on the
subpath has the same terminal vector as the original continuous lift at the subinterval endpoint.
-/
theorem exists_path_continuation_lift_affine_reparam [CompleteSpace E]
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) {H : ℂ → E →L[ℂ] E}
    (hH : DifferentiableOn ℂ H U)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    {y : E} (A : PathContinuationLift γ H y)
    {a c : ℝ} (hc : 0 < c)
    (hparam : ∀ s ∈ Icc (0 : ℝ) 1, a + c * s ∈ Icc (0 : ℝ) 1) :
    ∃ B : PathContinuationLift (fun s => γ (a + c * s)) H (A.value a),
      B.value 1 = A.value (a + c) := by
  let φ : ℝ → ℝ := fun s => a + c * s
  have hφcont : ContinuousOn φ (Icc (0 : ℝ) 1) := by
    exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hγ' : ContinuousOn (fun s => γ (φ s)) (Icc (0 : ℝ) 1) :=
    hγ.comp hφcont (fun s hs => hparam s hs)
  have hpath' : ∀ s ∈ Icc (0 : ℝ) 1, γ (φ s) ∈ U :=
    fun s hs => hpath (φ s) (hparam s hs)
  obtain ⟨B⟩ := exists_path_continuation_lift hγ' U hU H hH hpath' (A.value a)
  let F : ℝ → E := fun s => A.value (φ s)
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    A.value_continuous.comp hφcont (fun s hs => hparam s hs)
  have hFchart : ∀ s ∈ Icc (0 : ℝ) 1,
      Nonempty (PathSolutionChart (fun u => γ (φ u)) H F s) := by
    intro s hs
    obtain ⟨C⟩ := path_continuation_lift_has_solution_charts hγ A (φ s) (hparam s hs)
    exact ⟨C.affineReparam hc (a := a) (c := c) (u := s) hparam⟩
  have hBchart := path_continuation_lift_has_solution_charts hγ' B
  have hstart : F 0 = B.value 0 := by
    rw [B.value_initial]
    simp [F, φ]
  have hEq := continuous_path_solution_lifts_unique hγ' H hFcont
    B.value_continuous hFchart hBchart hstart
  refine ⟨B, ?_⟩
  have hlast := hEq 1 (by norm_num)
  change A.value (φ 1) = B.value 1 at hlast
  calc
    B.value 1 = A.value (φ 1) := hlast.symm
    _ = A.value (a + c) := by congr 1; simp [φ]

/-- The finite-chain path lift is independent of its local disk choices and subdivision. -/
theorem path_continuation_lifts_unique
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (H : ℂ → E →L[ℂ] E) (y : E)
    (A B : PathContinuationLift γ H y) :
    ∀ t ∈ Icc (0 : ℝ) 1, A.value t = B.value t := by
  apply disk_chain_lifts_unique hγ H A.value_continuous B.value_continuous
    A.subdivision A.subdivision_pos A.radius A.coefficient_bound A.radius_pos
    A.coefficient_bound_nonneg A.disks A.centers A.operator_bound A.path_cover A.overlap
    A.local_formula
    B.subdivision B.subdivision_pos B.radius B.coefficient_bound B.radius_pos
    B.coefficient_bound_nonneg B.disks B.centers B.operator_bound B.path_cover B.overlap
    B.local_formula
  exact A.value_initial.trans B.value_initial.symm

end DOZZ.Proofs
