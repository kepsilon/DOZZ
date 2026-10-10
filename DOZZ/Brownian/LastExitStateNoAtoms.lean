/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitReferenceKernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Atomlessness of deterministic entrance states

At each positive deterministic time, the positive-coordinate entrance state has a density.
In particular, the endpoint is almost surely not equal to any fixed barrier. This removes the
single endpoint case between the above-barrier avoidance identity and its zero lower-state branch.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A positive-coordinate entrance state has no atom at any prescribed real value. -/
theorem ae_conditionedPositiveStateAt_ne
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (a : ℝ) :
    ∀ᵐ p ∂P, conditionedPositiveStateAt t p ≠ a := by
  let times : Fin 1 → ℝ≥0 := fun _ => t
  let X : BrownianPath → Fin 1 → ℝ := fun p _ => -(p t)
  let f : (Fin 1 → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal
    (max 0 (conditionedPositiveFDDDensity ν [t] [z 0]))
  have htimes : ∀ i, 0 < (times i : ℝ) := fun _ => ht
  have hmono : StrictMono times := by
    intro i j hij
    fin_cases i
    fin_cases j
    exact False.elim (by simp at hij)
  have hfdd := negativeConditionedLaw_positiveFDD hP 1 (by norm_num)
    times htimes hmono
  have hfd : P.map X =
      (volume : Measure (Fin 1 → ℝ)).withDensity f := by
    simpa [X, times, f] using hfdd
  have hcoord : Measurable (fun z : Fin 1 → ℝ => z 0) := measurable_pi_apply 0
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval t).neg
  have hstate : P.map (conditionedPositiveStateAt t) =
      ((volume : Measure (Fin 1 → ℝ)).withDensity f).map
        (fun z : Fin 1 → ℝ => z 0) := by
    calc
      P.map (conditionedPositiveStateAt t) = (P.map X).map
          (fun z : Fin 1 → ℝ => z 0) := by
        rw [Measure.map_map hcoord hX]
        congr 1
      _ = _ := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map
        (fun z : Fin 1 → ℝ => z 0)) hfd
  have hcoordSet :
      (fun z : Fin 1 → ℝ => z 0) ⁻¹' ({a} : Set ℝ) =
        {z : Fin 1 → ℝ | z 0 = a} := by
    ext z
    simp
  have hnull : (volume : Measure (Fin 1 → ℝ))
      {z : Fin 1 → ℝ | z 0 = a} = 0 := by
    have hpi : ({z : Fin 1 → ℝ | z 0 = a} : Set (Fin 1 → ℝ)) =
        Set.pi Set.univ (fun _ : Fin 1 => ({a} : Set ℝ)) := by
      ext z
      simp
    rw [hpi, volume_pi_pi]
    simp
  have hset : MeasurableSet ({z : Fin 1 → ℝ | z 0 = a}) :=
    (measurableSet_singleton a).preimage (measurable_pi_apply 0)
  have hdensityNull : ((volume : Measure (Fin 1 → ℝ)).withDensity f)
      {z : Fin 1 → ℝ | z 0 = a} = 0 := by
    rw [withDensity_apply f hset]
    have hrestrict : (volume : Measure (Fin 1 → ℝ)).restrict
        {z : Fin 1 → ℝ | z 0 = a} = 0 := Measure.restrict_eq_zero.mpr hnull
    change (∫⁻ z, f z ∂((volume : Measure (Fin 1 → ℝ)).restrict
      {z : Fin 1 → ℝ | z 0 = a})) = 0
    rw [hrestrict]
    simp
  have hstateNull : (P.map (conditionedPositiveStateAt t)) {a} = 0 := by
    rw [hstate, Measure.map_apply hcoord (measurableSet_singleton a), hcoordSet]
    exact hdensityNull
  have hpre : (conditionedPositiveStateAt t) ⁻¹' ({a} : Set ℝ) =
      {p : BrownianPath | conditionedPositiveStateAt t p = a} := by
    ext p
    simp
  have hzero : P {p : BrownianPath | conditionedPositiveStateAt t p = a} = 0 := by
    rw [← hpre, ← Measure.map_apply (measurable_conditionedPositiveStateAt t)
      (measurableSet_singleton a)]
    exact hstateNull
  rw [measure_eq_zero_iff_ae_notMem] at hzero
  filter_upwards [hzero] with p hp
  exact hp

end DOZZ.Proofs

end
