/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureHistoryMarkov
public import DOZZ.Brownian.LastExitRationalCondExp
public import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Full-history conditional expectation for rational future avoidance

The full rational future is already disintegrated by the deterministic-time endpoint kernel.
This file records the avoidance event as a decreasing sequence of finite rational cylinders and
passes its conditional expectations to the all-rational event in `L¹`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace DOZZ.Proofs

/-- A rational future-coordinate constraint, vacuous at nonpositive relative times. -/
def conditionedPositiveFutureAvoidanceCoordinate (t c : ℝ≥0) (q : ℚ) : Set BrownianPath :=
  if _hq : 0 < (q : ℝ) then
    {p | c < conditionedPositiveFutureRationalEvals t p q}
  else Set.univ

/-- Avoidance on the first `n` entries of the fixed enumeration of rational offsets. -/
def conditionedPositiveFutureAvoidanceGrid (t c : ℝ≥0) (n : ℕ) : Set BrownianPath :=
  ⋂ k : Fin n, conditionedPositiveFutureAvoidanceCoordinate t c
    (lastExitRationalEnumeration k.val)

/-- Strict avoidance on every positive rational future offset. -/
def conditionedPositiveFutureRationalAvoidance (t c : ℝ≥0) : Set BrownianPath :=
  ⋂ q : ℚ, conditionedPositiveFutureAvoidanceCoordinate t c q

theorem measurableSet_conditionedPositiveFutureAvoidanceCoordinate
    (t c : ℝ≥0) (q : ℚ) :
    MeasurableSet (conditionedPositiveFutureAvoidanceCoordinate t c q) := by
  by_cases hq : 0 < (q : ℝ)
  · simp only [conditionedPositiveFutureAvoidanceCoordinate, hq]
    exact measurableSet_lt measurable_const
      ((measurable_pi_apply q).comp (measurable_conditionedPositiveFutureRationalEvals t))
  · simp [conditionedPositiveFutureAvoidanceCoordinate, hq]

theorem measurableSet_conditionedPositiveFutureAvoidanceGrid
    (t c : ℝ≥0) (n : ℕ) :
    MeasurableSet (conditionedPositiveFutureAvoidanceGrid t c n) := by
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_conditionedPositiveFutureAvoidanceCoordinate t c
    (lastExitRationalEnumeration k.val)

theorem conditionedPositiveFutureAvoidanceGrid_antitone (t c : ℝ≥0) :
    Antitone (conditionedPositiveFutureAvoidanceGrid t c) := by
  intro n m hnm
  change (⋂ k : Fin m, conditionedPositiveFutureAvoidanceCoordinate t c
      (lastExitRationalEnumeration k.val)) ⊆
    ⋂ k : Fin n, conditionedPositiveFutureAvoidanceCoordinate t c
      (lastExitRationalEnumeration k.val)
  intro p hp
  simp only [Set.mem_iInter] at hp ⊢
  intro k
  exact hp ⟨k.val, by omega⟩

theorem conditionedPositiveFutureRationalAvoidance_eq_iInter_grid
    (t c : ℝ≥0) :
    conditionedPositiveFutureRationalAvoidance t c =
      ⋂ n : ℕ, conditionedPositiveFutureAvoidanceGrid t c n := by
  ext p
  constructor
  · intro hp
    simp only [conditionedPositiveFutureRationalAvoidance, Set.mem_iInter] at hp
    simp only [conditionedPositiveFutureAvoidanceGrid, Set.mem_iInter]
    intro n k
    exact hp (lastExitRationalEnumeration k.val)
  · intro hp
    simp only [conditionedPositiveFutureRationalAvoidance, Set.mem_iInter]
    intro q
    obtain ⟨k, hkq⟩ := lastExitRationalEnumeration_surjective q
    subst q
    simp only [conditionedPositiveFutureAvoidanceGrid, Set.mem_iInter] at hp
    let hk : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    have hgrid := hp (k + 1) hk
    simpa [hk] using hgrid


/-- Sequence-space version of the rational future avoidance event, used in endpoint-kernel
integrals. -/
def conditionedPositiveFutureAvoidanceSequence (c : ℝ≥0) : Set (ℚ → ℝ) :=
  {y | ∀ q : ℚ, 0 < (q : ℝ) → c < y q}

/-- The full-history conditional expectation of a rational-future test restricted to strict
rational avoidance is the endpoint-kernel integral. This applies to arbitrary strongly measurable
future tests, not only cylinders. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (c : ℝ≥0)
    (G : (ℚ → ℝ) → ℝ) (hG : StronglyMeasurable G)
    (hGint : Integrable (fun p => G (conditionedPositiveFutureRationalEvals t p)) P) :
    P[fun p => (conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun p => G (conditionedPositiveFutureRationalEvals t p)) p |
        conditionedPositiveNaturalFiltration t] =ᵐ[P]
      fun p => ∫ y, (conditionedPositiveFutureAvoidanceSequence c).indicator G y ∂
        conditionedPositiveEndpointFutureKernel t P (conditionedPositiveHistory t p) := by
  let A : Set (ℚ → ℝ) := conditionedPositiveFutureAvoidanceSequence c
  have hA : MeasurableSet A := by
    have hrepr : ({y : ℚ → ℝ | ∀ q : ℚ, 0 < (q : ℝ) → (c : ℝ) < y q} : Set (ℚ → ℝ)) =
        ⋂ q : ℚ, {y : ℚ → ℝ | 0 < (q : ℝ) → (c : ℝ) < y q} := by
      ext y
      simp
    change MeasurableSet
      ({y : ℚ → ℝ | ∀ q : ℚ, 0 < (q : ℝ) → (c : ℝ) < y q} : Set (ℚ → ℝ))
    rw [hrepr]
    apply MeasurableSet.iInter
    intro q
    have hset : {y : ℚ → ℝ | 0 < (q : ℝ) → (c : ℝ) < y q} =
        if hq : 0 < (q : ℝ) then {y : ℚ → ℝ | (c : ℝ) < y q} else Set.univ := by
      by_cases hq : 0 < (q : ℝ) <;> simp [hq]
    rw [hset]
    split_ifs with hq
    · exact measurableSet_lt measurable_const (measurable_pi_apply q)
    · exact MeasurableSet.univ
  have hpre : conditionedPositiveFutureRationalAvoidance t c =
      (conditionedPositiveFutureRationalEvals t) ⁻¹' A := by
    ext p
    simp only [conditionedPositiveFutureRationalAvoidance, Set.mem_iInter,
      conditionedPositiveFutureAvoidanceCoordinate, Set.mem_preimage, A,
      ]
    constructor
    · intro h q hq
      have := h q
      simp only [hq, dite_true] at this
      exact this
    · intro h q
      by_cases hq : 0 < (q : ℝ)
      · simpa [hq] using h q hq
      · simp [hq]
  have hSeqG : StronglyMeasurable (A.indicator G) := hG.indicator hA
  have hPathG : Integrable (fun p => (A.indicator G)
      (conditionedPositiveFutureRationalEvals t p)) P := by
    exact hGint.indicator (hA.preimage (measurable_conditionedPositiveFutureRationalEvals t))
  have hcond := conditionedPositiveHistory_condExp_rationalFuture hP t ht
    (A.indicator G) hSeqG hPathG
  have hpath : (conditionedPositiveFutureRationalAvoidance t c).indicator
      (fun p => G (conditionedPositiveFutureRationalEvals t p)) =
      fun p => A.indicator G (conditionedPositiveFutureRationalEvals t p) := by
    funext p
    have hmem : p ∈ conditionedPositiveFutureRationalAvoidance t c ↔
        conditionedPositiveFutureRationalEvals t p ∈ A := by
      rw [hpre]
      rfl
    by_cases hp : p ∈ conditionedPositiveFutureRationalAvoidance t c
    · have hp' : conditionedPositiveFutureRationalEvals t p ∈ A := hmem.mp hp
      simp [hp, hp']
    · have hp' : conditionedPositiveFutureRationalEvals t p ∉ A := fun h => hp (hmem.mpr h)
      simp [hp, hp']
  rw [hpath]
  filter_upwards [hcond] with p hp
  simpa [conditionedPositiveEndpointFutureKernel,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
    conditionedPositiveHistory_current, A, conditionedPositiveFutureAvoidanceSequence] using hp

end DOZZ.Proofs

end
