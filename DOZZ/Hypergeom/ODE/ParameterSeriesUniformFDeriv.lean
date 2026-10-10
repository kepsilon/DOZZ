/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesDerivativeBounds
import Mathlib.Analysis.Normed.Module.Connected

/-! A local uniform bound for the parameter derivative of the ordinary Gauss series. -/

@[expose] public section

namespace DOZZ.Proofs

/-- At a fixed point strictly inside the unit disk, the parameter derivative of the ordinary Gauss
value is bounded on some neighborhood of every denominator-pole-free parameter tuple. The bound
comes from the compact-uniform summable majorant for the derivatives of the series terms. -/
theorem exists_local_uniform_ordinaryHypergeometric_fderiv_bound
    (p : ℂ × ℂ × ℂ) (z : ℂ)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ q ∈ Metric.ball p r,
        ‖fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
          ordinaryHypergeometric v.1 v.2.1 v.2.2 z) q‖ ≤ M := by
  have hp : p ∈ gaussParameterPoleFreeDomain := hc
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp gaussParameterPoleFreeDomain_isOpen p hp
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrε : r < ε := by dsimp [r]; linarith
  let K : Set (ℂ × ℂ × ℂ) := Metric.closedBall p r
  have hKcompact : IsCompact K := isCompact_closedBall p r
  have hKpole : ∀ q ∈ K, ∀ k : ℕ, q.2.2 ≠ -(k : ℂ) := by
    intro q hq k
    exact hball (Metric.closedBall_subset_ball hrε hq) k
  obtain ⟨u, hu, huBound⟩ :=
    exists_summable_uniform_gaussParameterSeriesTerm_fderiv_bound_of_isCompact
      hKcompact hKpole z hz
  have hpK : p ∈ K := Metric.mem_closedBall_self (le_of_lt hr)
  have hsum0 := gaussParameterSeriesTerm_summable p z hc hz
  have htermsDiff : ∀ n : ℕ, ∀ q ∈ Metric.ball p r,
      HasFDerivAt (fun v => gaussParameterSeriesTerm v z n)
        (fderiv ℂ (fun v => gaussParameterSeriesTerm v z n) q) q := by
    intro n q hq
    exact (gaussParameterSeriesTerm_differentiableAt q z n
      (hKpole q (Metric.ball_subset_closedBall hq))).hasFDerivAt
  have htermsBound : ∀ n : ℕ, ∀ q ∈ Metric.ball p r,
      ‖fderiv ℂ (fun v => gaussParameterSeriesTerm v z n) q‖ ≤ u n := by
    intro n q hq
    exact huBound n q (Metric.ball_subset_closedBall hq)
  have hsumEq :
      (fun q : ℂ × ℂ × ℂ => ordinaryHypergeometric q.1 q.2.1 q.2.2 z) =
        fun q => ∑' n : ℕ, gaussParameterSeriesTerm q z n := by
    funext q
    exact gaussParameterSeriesTerm_sum q.1 q.2.1 q.2.2 z
  let M : ℝ := ∑' n : ℕ, u n
  have hM : 0 ≤ M := by
    exact tsum_nonneg (fun n => le_trans (norm_nonneg _) (huBound n p hpK))
  refine ⟨r, M, hr, hM, ?_⟩
  intro q hq
  have hqK : q ∈ K := Metric.ball_subset_closedBall hq
  have hsumDeriv := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball htermsDiff htermsBound
    (Metric.mem_ball_self hr) hsum0 hq
  have hderivFormula :
      fderiv ℂ (fun v : ℂ × ℂ × ℂ => ∑' n : ℕ, gaussParameterSeriesTerm v z n) q =
        ∑' n : ℕ, fderiv ℂ (fun v => gaussParameterSeriesTerm v z n) q :=
    hsumDeriv.fderiv
  have hderivNormSummable :
      Summable (fun n : ℕ => ‖fderiv ℂ (fun v => gaussParameterSeriesTerm v z n) q‖) :=
    hu.of_norm_bounded fun n => by simpa using htermsBound n q hq
  calc
    ‖fderiv ℂ (fun v : ℂ × ℂ × ℂ => ordinaryHypergeometric v.1 v.2.1 v.2.2 z) q‖ =
        ‖∑' n : ℕ, fderiv ℂ (fun v => gaussParameterSeriesTerm v z n) q‖ := by
          rw [hsumEq, hderivFormula]
    _ ≤ ∑' n : ℕ, ‖fderiv ℂ (fun v => gaussParameterSeriesTerm v z n) q‖ :=
      norm_tsum_le_tsum_norm hderivNormSummable
    _ ≤ M := by
      dsimp [M]
      exact hderivNormSummable.tsum_le_tsum (fun n => htermsBound n q hq) hu

end DOZZ.Proofs
