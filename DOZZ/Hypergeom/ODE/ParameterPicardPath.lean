/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterPicardDerivativeTerms
public import DOZZ.Hypergeom.ODE.PathSubdivision
public import DOZZ.Hypergeom.ODE.UniquenessEndpoints

/-! Parameter differentiability and uniform bounds propagated through finite Picard disk chains. -/

@[expose] public section

namespace DOZZ.Proofs

open Set

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The seed map obtained after taking `i` successive parameterized Picard steps along a sequence
of disk centers. -/
noncomputable def parameterizedPicardPathSeed (centers : ℕ → ℂ)
    (A : P → ℂ → E →L[ℂ] E) (y₀ : P → E) : ℕ → P → E
  | 0 => y₀
  | i + 1 => fun q =>
      ∑' n : ℕ, parameterizedPicardTerm (centers i) A
        (parameterizedPicardPathSeed centers A y₀ i) n q (centers (i + 1))

/-- The recursively propagated Fréchet derivative candidate for a Picard path seed. -/
noncomputable def parameterizedPicardPathSeedFDeriv (centers : ℕ → ℂ)
    (A : P → ℂ → E →L[ℂ] E)
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (y₀ : P → E) (Dy₀ : P → P →L[ℂ] E) : ℕ → P → P →L[ℂ] E
  | 0 => fun q => Dy₀ q
  | i + 1 => fun q =>
      ∑' n : ℕ, parameterizedPicardTermParamFDeriv (centers i) A DA
        (parameterizedPicardPathSeed centers A y₀ i)
        (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i) n q
        (centers (i + 1))

/-- A common radius and geometric majorants propagate differentiability of the seed through every
disk of a finite Picard chain. The propagated endpoint values and derivatives grow by at most a
factor two per disk, independently of the parameter in the open set. -/
theorem parameterizedPicardPathSeed_hasFDerivAt
    [CompleteSpace E]
    (centers : ℕ → ℂ) (N : ℕ) (r : ℝ) (hr : 0 < r)
    (s : Set P) (hs : IsOpen s) (hsconn : IsPreconnected s)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ i ≤ N, ∀ q, DifferentiableOn ℂ (A q) (Metric.ball (centers i) r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ i ≤ N, ∀ q, ContinuousOn (DA q) (Metric.ball (centers i) r))
    (y₀ : P → E) (Dy₀ : P → P →L[ℂ] E)
    (M L Y D : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hMr : M * r ≤ (1 / 2 : ℝ))
    (hcontract : r * (M * D + L * Y) ≤ D * (1 / 2 : ℝ))
    (hAderiv : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      ‖A q w‖ ≤ M)
    (hDA_bound : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      ‖DA q w‖ ≤ L)
    (hclose : ∀ i < N, centers (i + 1) ∈ Metric.ball (centers i) r)
    (hyderiv : ∀ q ∈ s, HasFDerivAt y₀ (Dy₀ q) q)
    (hy_bound : ∀ q ∈ s, ‖y₀ q‖ ≤ Y)
    (hDy_bound : ∀ q ∈ s, ‖Dy₀ q‖ ≤ D)
    (q₀ : P) (hq₀ : q₀ ∈ s) :
    ∀ q ∈ s,
      HasFDerivAt (parameterizedPicardPathSeed centers A y₀ N)
        (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ N q) q ∧
      ‖parameterizedPicardPathSeed centers A y₀ N q‖ ≤ Y * 2 ^ N ∧
      ‖parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ N q‖ ≤ D * 2 ^ N := by
  let ρ : ℝ := 1 / 2
  have hρ : 0 ≤ ρ := by norm_num [ρ]
  have hρlt : ρ < 1 := by norm_num [ρ]
  have hprop : ∀ i, i ≤ N → ∀ q ∈ s,
      HasFDerivAt (parameterizedPicardPathSeed centers A y₀ i)
        (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i q) q ∧
      ‖parameterizedPicardPathSeed centers A y₀ i q‖ ≤ Y * 2 ^ i ∧
      ‖parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i q‖ ≤ D * 2 ^ i := by
    intro i
    induction i with
    | zero =>
        intro hi q hq
        have hdiff := hyderiv q hq
        have hy := hy_bound q hq
        have hdy := hDy_bound q hq
        simpa [parameterizedPicardPathSeed, parameterizedPicardPathSeedFDeriv]
          using And.intro hdiff (And.intro hy hdy)
    | succ i ih =>
        intro hi q hq
        have hiN : i ≤ N := Nat.le_of_succ_le hi
        have hiNlt : i < N := Nat.lt_of_succ_le hi
        have hstepclose := hclose i hiNlt
        let Yi : ℝ := Y * 2 ^ i
        let Di : ℝ := D * 2 ^ i
        have hYi : 0 ≤ Yi := by dsimp [Yi]; positivity
        have hDi : 0 ≤ Di := by dsimp [Di]; positivity
        have hcontractI : r * (M * Di + L * Yi) ≤ Di * ρ := by
          dsimp [Yi, Di]
          calc
            r * (M * (D * 2 ^ i) + L * (Y * 2 ^ i)) =
                (r * (M * D + L * Y)) * 2 ^ i := by ring
            _ ≤ (D * ρ) * 2 ^ i :=
              mul_le_mul_of_nonneg_right hcontract (pow_nonneg (by norm_num) i)
            _ = (D * 2 ^ i) * ρ := by ring
        have hyderivI : ∀ q' ∈ s,
            HasFDerivAt (parameterizedPicardPathSeed centers A y₀ i)
              (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i q') q' := by
          intro q' hq'
          exact (ih hiN q' hq').1
        have hyboundI : ∀ q' ∈ s,
            ‖parameterizedPicardPathSeed centers A y₀ i q'‖ ≤ Yi := by
          intro q' hq'
          exact (ih hiN q' hq').2.1
        have hDyboundI : ∀ q' ∈ s,
            ‖parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i q'‖ ≤ Di := by
          intro q' hq'
          exact (ih hiN q' hq').2.2
        have hderiv := parameterizedPicardSeries_hasFDerivAt_of_geometric_bounds
          (centers i) r hr s hs hsconn A (hA i hiN) DA (hDA i hiN)
          (parameterizedPicardPathSeed centers A y₀ i)
          (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i)
          M L Yi Di ρ hM hL hYi hDi hρ hρlt hMr hcontractI
          (hAderiv i hiN) (hA_bound i hiN) (hDA_bound i hiN)
          hyderivI hyboundI hDyboundI hq₀ hq hstepclose
        have hsumBounds := parameterizedPicardSeries_value_and_fderiv_norm_le_of_geometric_bounds
          (centers i) r hr s A (hA i hiN) DA
          (parameterizedPicardPathSeed centers A y₀ i)
          (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ i)
          M L Yi Di ρ hM hL hYi hDi hρ hρlt hMr hcontractI
          (hA_bound i hiN) (hDA_bound i hiN) hyboundI hDyboundI
          q hq (centers (i + 1)) hstepclose
        have hvalueNext :
            ‖parameterizedPicardPathSeed centers A y₀ (i + 1) q‖ ≤
              Y * 2 ^ (i + 1) := by
          have h := hsumBounds.1
          have hrewrite :
              ‖parameterizedPicardPathSeed centers A y₀ (i + 1) q‖ ≤
                Y * (2 ^ i * (1 - ρ)⁻¹) := by
            simpa [parameterizedPicardPathSeed, Yi, mul_assoc, mul_left_comm,
              mul_comm] using h
          have hfactor : (1 - ρ)⁻¹ = 2 := by norm_num [ρ]
          calc
            ‖parameterizedPicardPathSeed centers A y₀ (i + 1) q‖ ≤
                Y * (2 ^ i * (1 - ρ)⁻¹) := hrewrite
            _ = Y * (2 * 2 ^ i) := by rw [hfactor]; ring
            _ = Y * 2 ^ (i + 1) := by rw [pow_succ]; ring
        have hderivNext :
            ‖parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ (i + 1) q‖ ≤
              D * 2 ^ (i + 1) := by
          have h := hsumBounds.2
          have hrewrite :
              ‖parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ (i + 1) q‖ ≤
                D * (2 ^ i * (1 - ρ)⁻¹) := by
            simpa [parameterizedPicardPathSeedFDeriv, Yi, Di, mul_assoc, mul_left_comm,
              mul_comm] using h
          have hfactor : (1 - ρ)⁻¹ = 2 := by norm_num [ρ]
          calc
            ‖parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ (i + 1) q‖ ≤
                D * (2 ^ i * (1 - ρ)⁻¹) := hrewrite
            _ = D * (2 * 2 ^ i) := by rw [hfactor]; ring
            _ = D * 2 ^ (i + 1) := by rw [pow_succ]; ring
        have hderivNext' := hderiv
        simpa [parameterizedPicardPathSeed, parameterizedPicardPathSeedFDeriv] using
          And.intro hderivNext' (And.intro hvalueNext hderivNext)
  intro q hq
  exact hprop N le_rfl q hq

/-- Along a continuous path with common local coefficient and derivative bounds, a parameterized
Picard chain exists on one equal finite mesh and its terminal seed is differentiable in the
parameters with explicit bounds. -/
theorem exists_parameterizedPicardPathSeed_hasFDerivAt
    [CompleteSpace E]
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (s : Set P) (hs : IsOpen s) (hsconn : IsPreconnected s)
    (r : ℝ) (hr : 0 < r)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q,
      DifferentiableOn ℂ (A q) (Metric.ball (γ t) r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q,
      ContinuousOn (DA q) (Metric.ball (γ t) r))
    (M L Y D : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hMr : M * r ≤ (1 / 2 : ℝ))
    (hcontract : r * (M * D + L * Y) ≤ D * (1 / 2 : ℝ))
    (hAderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ s, ∀ w ∈ Metric.ball (γ t) r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ s, ∀ w ∈ Metric.ball (γ t) r,
      ‖A q w‖ ≤ M)
    (hDA_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ s, ∀ w ∈ Metric.ball (γ t) r,
      ‖DA q w‖ ≤ L)
    (y₀ : P → E) (Dy₀ : P → P →L[ℂ] E)
    (hyderiv : ∀ q ∈ s, HasFDerivAt y₀ (Dy₀ q) q)
    (hy_bound : ∀ q ∈ s, ‖y₀ q‖ ≤ Y)
    (hDy_bound : ∀ q ∈ s, ‖Dy₀ q‖ ≤ D)
    (q₀ : P) (hq₀ : q₀ ∈ s) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i < N, γ (((i + 1 : ℕ) : ℝ) / (N : ℝ)) ∈
        Metric.ball (γ ((i : ℝ) / (N : ℝ))) r) ∧
      ∀ q ∈ s,
        HasFDerivAt
          (parameterizedPicardPathSeed
            (fun i => γ ((i : ℝ) / (N : ℝ))) A y₀ N)
          (parameterizedPicardPathSeedFDeriv
            (fun i => γ ((i : ℝ) / (N : ℝ))) A DA y₀ Dy₀ N q) q ∧
        ‖parameterizedPicardPathSeed
          (fun i => γ ((i : ℝ) / (N : ℝ))) A y₀ N q‖ ≤ Y * 2 ^ N ∧
        ‖parameterizedPicardPathSeedFDeriv
          (fun i => γ ((i : ℝ) / (N : ℝ))) A DA y₀ Dy₀ N q‖ ≤ D * 2 ^ N := by
  obtain ⟨N, hN, hpartition⟩ := exists_path_subdivision hγ (by linarith : 0 < r / 2)
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htime : ∀ i : ℕ, i ≤ N → (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    constructor
    · positivity
    · apply (div_le_one hNreal).2
      exact_mod_cast hi
  have hcentersclose : ∀ i < N,
      γ (((i + 1 : ℕ) : ℝ) / (N : ℝ)) ∈
        Metric.ball (γ ((i : ℝ) / (N : ℝ))) r := by
    intro i hi
    apply Metric.mem_ball.mpr
    have hdist := (hpartition i hi).1
    rw [dist_comm]
    exact hdist.trans (by linarith)
  let centers : ℕ → ℂ := fun i => γ ((i : ℝ) / (N : ℝ))
  have hAcenters : ∀ i ≤ N, ∀ q,
      DifferentiableOn ℂ (A q) (Metric.ball (centers i) r) := by
    intro i hi q
    simpa [centers] using hA _ (htime i hi) q
  have hDAcenters : ∀ i ≤ N, ∀ q,
      ContinuousOn (DA q) (Metric.ball (centers i) r) := by
    intro i hi q
    simpa [centers] using hDA _ (htime i hi) q
  have hAderivCenters : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q := by
    intro i hi q hq w hw
    exact hAderiv _ (htime i hi) q hq w (by simpa [centers] using hw)
  have hAboundCenters : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      ‖A q w‖ ≤ M := by
    intro i hi q hq w hw
    exact hA_bound _ (htime i hi) q hq w (by simpa [centers] using hw)
  have hDAboundCenters : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      ‖DA q w‖ ≤ L := by
    intro i hi q hq w hw
    exact hDA_bound _ (htime i hi) q hq w (by simpa [centers] using hw)
  have hresult := parameterizedPicardPathSeed_hasFDerivAt
    centers N r hr s hs hsconn A hAcenters DA hDAcenters y₀ Dy₀ M L Y D
    hM hL hY hD hMr hcontract hAderivCenters hAboundCenters hDAboundCenters
    hcentersclose hyderiv hy_bound hDy_bound q₀ hq₀
  refine ⟨N, hN, ?_, ?_⟩
  · simpa [centers] using hcentersclose
  · simpa [centers] using hresult

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
/-- If a parameterized family already solves the linear system on every disk of a Picard chain,
local uniqueness identifies the recursively propagated Picard endpoint with that family's value. -/
lemma parameterizedPicardPathSeed_eq_solution
    [CompleteSpace E]
    (centers : ℕ → ℂ) (N : ℕ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (s : Set P)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ i ≤ N, ∀ q, DifferentiableOn ℂ (A q) (Metric.ball (centers i) r))
    (hA_bound : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      ‖A q w‖ ≤ M)
    (y₀ : P → E) (F : P → ℂ → E)
    (hFderiv : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      HasDerivAt (F q) (A q w (F q w)) w)
    (hstart : ∀ q ∈ s, y₀ q = F q (centers 0))
    (hclose : ∀ i < N, centers (i + 1) ∈ Metric.ball (centers i) r) :
    ∀ q ∈ s,
      parameterizedPicardPathSeed centers A y₀ N q = F q (centers N) := by
  have hstate : ∀ i, i ≤ N → ∀ q ∈ s,
      parameterizedPicardPathSeed centers A y₀ i q = F q (centers i) := by
    intro i
    induction i with
    | zero =>
        intro hi q hq
        exact hstart q hq
    | succ i ih =>
        intro hi q hq
        have hiN : i ≤ N := Nat.le_of_succ_le hi
        have hiNlt : i < N := Nat.lt_of_succ_le hi
        have hprevious := ih hiN q hq
        have hnext := hclose i hiNlt
        let solution : ℂ → E := holomorphicPicardSolution (centers i) r (A q)
          (hA i hiN q) (parameterizedPicardPathSeed centers A y₀ i q)
        have hsolutionCenter : solution (centers i) =
            parameterizedPicardPathSeed centers A y₀ i q := by
          exact holomorphicPicardSolution_apply_center (centers i) r (A q)
            (hA i hiN q) (parameterizedPicardPathSeed centers A y₀ i q)
        have hsolutionDeriv : ∀ w ∈ Metric.ball (centers i) r,
            HasDerivAt solution ((A q w) (solution w)) w := by
          intro w hw
          exact holomorphicPicardSolution_hasDerivAt (centers i) r M (A q)
            (hA i hiN q) (parameterizedPicardPathSeed centers A y₀ i q)
            hM (hA_bound i hiN q hq) hw
        have hunique := holomorphic_linear_system_solution_unique_of_eq_at
          (centers i) r M (A q) hM (hA_bound i hiN q hq)
          hsolutionDeriv (hFderiv i hiN q hq)
          (Metric.mem_ball_self hr) hnext
          (hsolutionCenter.trans hprevious)
        have hsumEq :
            (∑' n : ℕ, parameterizedPicardTerm (centers i) A
              (parameterizedPicardPathSeed centers A y₀ i) n q (centers (i + 1))) =
              solution (centers (i + 1)) := by
          unfold solution holomorphicPicardSolution
          apply tsum_congr
          intro n
          exact parameterizedPicardTerm_eq_holomorphicPicardTerm
            (centers i) r A (fun j => hA i hiN j)
            (parameterizedPicardPathSeed centers A y₀ i) n q
            (centers (i + 1)) hnext
        change (∑' n : ℕ, parameterizedPicardTerm (centers i) A
            (parameterizedPicardPathSeed centers A y₀ i) n q (centers (i + 1))) = _
        rw [hsumEq]
        exact hunique
  intro q hq
  exact hstate N le_rfl q hq

end DOZZ.Proofs
