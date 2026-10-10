/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.ConditionedKernelShiftedStart

/-!
# Pathwise comparison of common-uniform conditioned kernel grids

The explicit one-step quantile inequalities propagate by induction along any shared sequence of
uniform levels. This is the finite-grid order estimate needed before constructing a measurable
uniform-driven chain and passing to continuous paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DOZZ.Proofs

/-- The generalized-inverse quantile of the positive conditioned transition kernel. -/
noncomputable def conditionedTransitionQuantile (ν t x u : ℝ) : ℝ :=
  cdfGeneralizedQuantile
    (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u

/-- Increasing a positive start raises the common-uniform transition quantile. -/
theorem conditionedTransitionQuantile_start_mono
    {ν t x x' u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile ν t x' u ≤ conditionedTransitionQuantile ν t x u := by
  exact conditionedPositiveTransitionQuantile_start_le hν ht hx' hxx' hu hu1

/-- Increasing the start by `d` raises the common-uniform transition quantile by at most `d`,
including the BES(3) zero-drift endpoint. -/
theorem conditionedTransitionQuantile_start_add
    {ν t x x' u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile ν t x u ≤
      conditionedTransitionQuantile ν t x' u + (x - x') := by
  by_cases hνzero : ν = 0
  · subst ν
    simpa [conditionedTransitionQuantile] using
      conditionedPositiveTransitionQuantile_start_add_zero ht hx' hxx' hu hu1
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    simpa [conditionedTransitionQuantile] using
      conditionedPositiveTransitionQuantile_start_add hνpos ht hx' hxx' hu hu1

/-- Increasing the drift raises the common-uniform transition quantile. -/
theorem conditionedTransitionQuantile_drift_mono
    {a b t x u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile a t x u ≤ conditionedTransitionQuantile b t x u := by
  exact conditionedPositiveTransitionQuantile_drift_le ha hab ht hx hu hu1

/-- Increasing the drift from `a` to `b` raises the common-uniform transition quantile by at most
`(b-a)t`, including `a=0`. -/
theorem conditionedTransitionQuantile_drift_add
    {a b t x u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile b t x u ≤
      conditionedTransitionQuantile a t x u + (b - a) * t := by
  by_cases hazero : a = 0
  · subst a
    by_cases hbzero : b = 0
    · subst b
      simp [conditionedTransitionQuantile]
    · have hbpos : 0 < b := lt_of_le_of_ne (by positivity) (Ne.symm hbzero)
      simpa [conditionedTransitionQuantile] using
        conditionedPositiveTransitionQuantile_drift_add_zero hbpos ht hx hu hu1
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
    simpa [conditionedTransitionQuantile] using
      conditionedPositiveTransitionQuantile_drift_add hapos hab ht hx hu hu1

/-- A deterministic common-uniform chain of positive conditioned transition quantiles. -/
noncomputable def conditionedKernelQuantileChain
    (ν dt x₀ : ℝ) (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => conditionedTransitionQuantile ν dt
      (conditionedKernelQuantileChain ν dt x₀ u n) (u n)

/-- A chain started in the positive half-line stays there for every common-uniform sequence with
levels in `(0,1)`. -/
theorem conditionedKernelQuantileChain_positive
    (ν dt x₀ : ℝ) (u : ℕ → ℝ)
    (hν : 0 ≤ ν) (hdt : 0 < dt) (hx₀ : 0 < x₀)
    (hu : ∀ n, 0 < u n ∧ u n < 1) :
    ∀ n, 0 < conditionedKernelQuantileChain ν dt x₀ u n := by
  intro n
  induction n with
  | zero => simpa [conditionedKernelQuantileChain] using hx₀
  | succ n ih =>
      simpa [conditionedKernelQuantileChain, conditionedTransitionQuantile] using
        conditionedPositiveTransitionQuantile_pos hν hdt ih (hu n).1 (hu n).2

/-- Two chains driven by the same uniform levels preserve the start order, and the upper chain's
excess is bounded by the initial gap plus elapsed time times the drift gap. Positivity of every
intermediate state follows from strict positivity of the transition quantiles. -/
theorem conditionedKernelQuantileChain_parameter_order
    (a b dt xa xb : ℝ) (u : ℕ → ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hdt : 0 < dt)
    (hxa : 0 < xa) (hxb : 0 < xb) (hstart : xa ≤ xb)
    (hu : ∀ n, 0 < u n ∧ u n < 1) :
    ∀ n : ℕ,
      conditionedKernelQuantileChain a dt xa u n ≤
        conditionedKernelQuantileChain b dt xb u n ∧
      conditionedKernelQuantileChain b dt xb u n ≤
        conditionedKernelQuantileChain a dt xa u n + (xb - xa) +
          (b - a) * (n : ℝ) * dt := by
  have hxaPos := conditionedKernelQuantileChain_positive a dt xa u ha hdt hxa hu
  have hxbPos := conditionedKernelQuantileChain_positive b dt xb u
    (le_trans ha hab) hdt hxb hu
  intro n
  induction n with
  | zero =>
      constructor
      · simpa [conditionedKernelQuantileChain] using hstart
      · simp [conditionedKernelQuantileChain]
  | succ n ih =>
      let xₐ := conditionedKernelQuantileChain a dt xa u n
      let xᵦ := conditionedKernelQuantileChain b dt xb u n
      have hu0 := hu n
      have hlowStart := conditionedTransitionQuantile_start_mono ha hdt
        (hxaPos n) ih.1 hu0.1 hu0.2
      have hlowDrift := conditionedTransitionQuantile_drift_mono ha hab hdt
        (hxbPos n) hu0.1 hu0.2
      have hupperStart := conditionedTransitionQuantile_start_add (ν := b)
        (by exact ha.trans hab) hdt (hxaPos n) ih.1 hu0.1 hu0.2
      have hupperDrift := conditionedTransitionQuantile_drift_add ha hab hdt
        (hxaPos n) hu0.1 hu0.2
      have hgap : xᵦ - xₐ ≤ (xb - xa) + (b - a) * (n : ℝ) * dt := by
        dsimp [xₐ, xᵦ] at ih ⊢
        linarith [ih.2]
      constructor
      · calc
          conditionedKernelQuantileChain a dt xa u (n + 1) =
              conditionedTransitionQuantile a dt xₐ (u n) := by
                simp [conditionedKernelQuantileChain, xₐ]
          _ ≤ conditionedTransitionQuantile a dt xᵦ (u n) := hlowStart
          _ ≤ conditionedTransitionQuantile b dt xᵦ (u n) := hlowDrift
          _ = conditionedKernelQuantileChain b dt xb u (n + 1) := by
                simp [conditionedKernelQuantileChain, xᵦ]
      · calc
          conditionedKernelQuantileChain b dt xb u (n + 1) =
              conditionedTransitionQuantile b dt xᵦ (u n) := by
                simp [conditionedKernelQuantileChain, xᵦ]
          _ ≤ conditionedTransitionQuantile b dt xₐ (u n) + (xᵦ - xₐ) := hupperStart
          _ ≤ (conditionedTransitionQuantile a dt xₐ (u n) + (b - a) * dt) +
                ((xb - xa) + (b - a) * (n : ℝ) * dt) := by
                  exact add_le_add hupperDrift hgap
          _ = conditionedKernelQuantileChain a dt xa u (n + 1) + (xb - xa) +
                (b - a) * ((n + 1 : ℕ) : ℝ) * dt := by
                  simp [conditionedKernelQuantileChain, xₐ]
                  ring_nf

/-- Common-uniform transition quantiles along a nonuniform deterministic time grid. The time-step
sequence is required to be positive at every index. -/
noncomputable def conditionedKernelQuantileWalk
    (ν x₀ : ℝ) (dt u : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => conditionedTransitionQuantile ν (dt n)
      (conditionedKernelQuantileWalk ν x₀ dt u n) (u n)

/-- A nonuniform quantile walk remains strictly positive when started positively and driven by
uniform levels in `(0,1)`. -/
theorem conditionedKernelQuantileWalk_positive
    (ν x₀ : ℝ) (dt u : ℕ → ℝ)
    (hν : 0 ≤ ν) (hx₀ : 0 < x₀)
    (hdt : ∀ n, 0 < dt n) (hu : ∀ n, 0 < u n ∧ u n < 1) :
    ∀ n, 0 < conditionedKernelQuantileWalk ν x₀ dt u n := by
  intro n
  induction n with
  | zero => simpa [conditionedKernelQuantileWalk] using hx₀
  | succ n ih =>
      simpa [conditionedKernelQuantileWalk, conditionedTransitionQuantile] using
        conditionedPositiveTransitionQuantile_pos hν (hdt n) ih (hu n).1 (hu n).2

/-- The common-uniform order estimate on any finite positive time grid. The upper walk's excess
is bounded by the initial gap plus drift difference times the sum of the elapsed grid steps. -/
theorem conditionedKernelQuantileWalk_parameter_order
    (a b xa xb : ℝ) (dt u : ℕ → ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hxa : 0 < xa) (hxb : 0 < xb)
    (hstart : xa ≤ xb) (hdt : ∀ n, 0 < dt n)
    (hu : ∀ n, 0 < u n ∧ u n < 1) :
    ∀ n : ℕ,
      conditionedKernelQuantileWalk a xa dt u n ≤
        conditionedKernelQuantileWalk b xb dt u n ∧
      conditionedKernelQuantileWalk b xb dt u n ≤
        conditionedKernelQuantileWalk a xa dt u n + (xb - xa) +
          (b - a) * (∑ k ∈ Finset.range n, dt k) := by
  have hxaPos := conditionedKernelQuantileWalk_positive a xa dt u ha hxa hdt hu
  have hxbPos := conditionedKernelQuantileWalk_positive b xb dt u
    (le_trans ha hab) hxb hdt hu
  intro n
  induction n with
  | zero =>
      constructor
      · simpa [conditionedKernelQuantileWalk] using hstart
      · simp [conditionedKernelQuantileWalk]
  | succ n ih =>
      let xₐ := conditionedKernelQuantileWalk a xa dt u n
      let xᵦ := conditionedKernelQuantileWalk b xb dt u n
      have hu0 := hu n
      have hstep := hdt n
      have hlowStart := conditionedTransitionQuantile_start_mono ha hstep
        (hxaPos n) ih.1 hu0.1 hu0.2
      have hlowDrift := conditionedTransitionQuantile_drift_mono ha hab hstep
        (hxbPos n) hu0.1 hu0.2
      have hupperStart := conditionedTransitionQuantile_start_add (ν := b)
        (ha.trans hab) hstep (hxaPos n) ih.1 hu0.1 hu0.2
      have hupperDrift := conditionedTransitionQuantile_drift_add ha hab hstep
        (hxaPos n) hu0.1 hu0.2
      have hgap : xᵦ - xₐ ≤ (xb - xa) +
          (b - a) * (∑ k ∈ Finset.range n, dt k) := by
        dsimp [xₐ, xᵦ] at ih ⊢
        linarith [ih.2]
      constructor
      · calc
          conditionedKernelQuantileWalk a xa dt u (n + 1) =
              conditionedTransitionQuantile a (dt n) xₐ (u n) := by
                simp [conditionedKernelQuantileWalk, xₐ]
          _ ≤ conditionedTransitionQuantile a (dt n) xᵦ (u n) := hlowStart
          _ ≤ conditionedTransitionQuantile b (dt n) xᵦ (u n) := hlowDrift
          _ = conditionedKernelQuantileWalk b xb dt u (n + 1) := by
                simp [conditionedKernelQuantileWalk, xᵦ]
      · calc
          conditionedKernelQuantileWalk b xb dt u (n + 1) =
              conditionedTransitionQuantile b (dt n) xᵦ (u n) := by
                simp [conditionedKernelQuantileWalk, xᵦ]
          _ ≤ conditionedTransitionQuantile b (dt n) xₐ (u n) + (xᵦ - xₐ) :=
                hupperStart
          _ ≤ (conditionedTransitionQuantile a (dt n) xₐ (u n) +
                (b - a) * dt n) +
                ((xb - xa) + (b - a) * (∑ k ∈ Finset.range n, dt k)) :=
                add_le_add hupperDrift hgap
          _ = conditionedKernelQuantileWalk a xa dt u (n + 1) + (xb - xa) +
                (b - a) * (∑ k ∈ Finset.range (n + 1), dt k) := by
                  simp [conditionedKernelQuantileWalk, xₐ, Finset.sum_range_succ]
                  ring_nf

end DOZZ.Proofs

end
