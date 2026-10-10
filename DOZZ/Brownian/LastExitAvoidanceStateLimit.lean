/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitEntranceTail
public import DOZZ.Brownian.LastExitAvoidanceLimit

/-!
# Mean convergence of the deterministic-time avoidance factor

The entrance state escapes every fixed lower interval, and the avoidance factor tends to one as
its state grows. This file combines those two facts at the level of the conditioned path law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Topology

namespace DOZZ.Proofs

private theorem lastExitAvoidanceFactor_nonneg_le_one
    {ν c y : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    0 ≤ lastExitAvoidanceFactor ν c y ∧ lastExitAvoidanceFactor ν c y ≤ 1 := by
  by_cases hcy : c < y
  · have hy : 0 < y := lt_trans hc hcy
    have hyc : 0 < y - c := sub_pos.mpr hcy
    have hnumExp : Real.exp (-2 * ν * (y - c)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      nlinarith
    have hdenExp : Real.exp (-2 * ν * y) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      nlinarith
    have hnum : 0 < 1 - Real.exp (-2 * ν * (y - c)) := by linarith
    have hden : 0 < 1 - Real.exp (-2 * ν * y) := by linarith
    have harg : -2 * ν * y ≤ -2 * ν * (y - c) := by
      have hstep : 0 < 2 * ν * c := by positivity
      nlinarith
    have hratio : 1 - Real.exp (-2 * ν * (y - c)) ≤
        1 - Real.exp (-2 * ν * y) := by
      have hexp := Real.exp_le_exp.mpr harg
      linarith
    have hfactor : lastExitAvoidanceFactor ν c y =
        (1 - Real.exp (-2 * ν * (y - c))) /
          (1 - Real.exp (-2 * ν * y)) := by
      simp [lastExitAvoidanceFactor, conditionedH, hν.ne', hcy]
    rw [hfactor]
    exact ⟨(div_nonneg hnum.le hden.le), (div_le_one hden).2 hratio⟩
  · simp [lastExitAvoidanceFactor, hcy]

private theorem measurable_lastExitAvoidanceFactor
    (ν c : ℝ) : Measurable (lastExitAvoidanceFactor ν c) := by
  unfold lastExitAvoidanceFactor
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · have hH : Measurable (fun y : ℝ => conditionedH ν y) := by
      by_cases hzero : ν = 0
      · simp [conditionedH, hzero]
        fun_prop
      · simp [conditionedH, hzero]
        fun_prop
    exact (hH.comp (measurable_id.sub measurable_const)).div hH
  · exact measurable_const

/-- The expected avoidance probability at time `t` converges to one for a positive-drift
conditioned entrance path. -/
theorem tendsto_integral_lastExitAvoidanceFactor_atTop
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 =>
      ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) atTop (𝓝 1) := by
  let : IsProbabilityMeasure P := hP.2.1
  have hfactorlim := lastExitAvoidanceFactor_tendsto_one_atTop (ν := ν) (c := c) hν
  have hstate := conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop
    hP hν
  have hmeasFactor : Measurable (lastExitAvoidanceFactor ν c) :=
    measurable_lastExitAvoidanceFactor ν c
  have hfactorBound (x : ℝ) :
      0 ≤ lastExitAvoidanceFactor ν c x ∧ lastExitAvoidanceFactor ν c x ≤ 1 :=
    lastExitAvoidanceFactor_nonneg_le_one hν hc
  have hX (t : ℝ≥0) : Measurable (fun p : BrownianPath => -(p t)) :=
    (ContinuousMap.measurable_eval t).neg
  have hInt (t : ℝ≥0) : Integrable
      (fun p : BrownianPath => lastExitAvoidanceFactor ν c (-(p t))) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((hmeasFactor.comp (hX t)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖lastExitAvoidanceFactor ν c (-(p t))‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfactorBound (-(p t))).1]
    simpa using (hfactorBound (-(p t))).2
  have hIntegralBound (t : ℝ≥0) :
      0 ≤ (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) ∧
      (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) ≤ 1 := by
    constructor
    · exact integral_nonneg (fun p => (hfactorBound (-(p t))).1)
    · calc
        _ ≤ ∫ _ : BrownianPath, (1 : ℝ) ∂P :=
          integral_mono (hInt t) (integrable_const 1)
            (fun p => (hfactorBound (-(p t))).2)
        _ = 1 := by simp
  have hsmall (M : ℝ) (hM : 0 < M) :
      Tendsto (fun t : ℝ≥0 => P.real {p | -(p t) ≤ M}) atTop (𝓝 0) :=
    conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop hP hν M hM
  have hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ≥0 in atTop,
      1 - ε ≤ ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P := by
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hlarge : ∀ᶠ y : ℝ in atTop,
        1 - δ < lastExitAvoidanceFactor ν c y :=
      hfactorlim.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨M₀, hM₀⟩ := (eventually_atTop.1 hlarge)
    let M : ℝ := max M₀ (max c 1)
    have hM : 0 < M := by dsimp [M]; positivity
    have hsmallM := hsmall M hM
    filter_upwards [hsmallM.eventually (Iio_mem_nhds hδ)] with t ht
    have hA : MeasurableSet {p : BrownianPath | -(p t) ≤ M} :=
      measurableSet_le (hX t) measurable_const
    let f : BrownianPath → ℝ := fun p => 1 - lastExitAvoidanceFactor ν c (-(p t))
    let g : BrownianPath → ℝ := fun p =>
      ({p : BrownianPath | -(p t) ≤ M}).indicator (fun _ => (1 : ℝ)) p + δ
    have hf : Integrable f P := by
      have hconst : Integrable (fun _ : BrownianPath => (1 : ℝ)) P := integrable_const 1
      have hsub := hconst.sub (hInt t)
      exact hsub.congr (Filter.Eventually.of_forall fun p => by simp [f])
    have hg : Integrable g P := by
      exact ((integrable_const (1 : ℝ)).indicator hA).add (integrable_const δ)
    have hfg : f ≤ g := by
      intro p
      by_cases hp : -(p t) ≤ M
      · have hnonneg := (hfactorBound (-(p t))).1
        simp [f, g, hp]
        linarith
      · have hgt : M < -(p t) := lt_of_not_ge hp
        have hyM : M₀ ≤ -(p t) := le_trans (le_max_left _ _) hgt.le
        have hlarg := hM₀ (-(p t)) hyM
        have hlt : 1 - lastExitAvoidanceFactor ν c (-(p t)) < δ := by linarith
        simp [f, g, hp]
        linarith
    have hbound : ∫ p, f p ∂P ≤ P.real {p | -(p t) ≤ M} + δ := by
      calc
        _ ≤ ∫ p, g p ∂P := integral_mono hf hg hfg
        _ = (∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
            (fun _ => (1 : ℝ))) p ∂P) + ∫ p, (δ : ℝ) ∂P := by
              rw [integral_add ((integrable_const (1 : ℝ)).indicator hA)
                (integrable_const δ)]
        _ = P.real {p | -(p t) ≤ M} + δ := by
          have hInd :
              (∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
                (fun _ => (1 : ℝ))) p ∂P) = P.real {p | -(p t) ≤ M} := by
            calc
              _ = ∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
                  (1 : BrownianPath → ℝ)) p ∂P := by
                    congr 1
              _ = P.real {p | -(p t) ≤ M} := integral_indicator_one hA
          rw [hInd]
          simp
    have htotal : ∫ p, f p ∂P =
        1 - ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P := by
      calc
        _ = ∫ p, (1 - lastExitAvoidanceFactor ν c (-(p t))) ∂P := rfl
        _ = (∫ _ : BrownianPath, (1 : ℝ) ∂P) -
            ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P :=
          integral_sub (integrable_const 1) (hInt t)
        _ = _ := by simp
    rw [htotal] at hbound
    dsimp [δ] at hbound ht hδ
    nlinarith [ht, hbound]
  have htop : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ≥0 in atTop,
      (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) < 1 + ε := by
    intro ε hε
    exact Filter.Eventually.of_forall fun t => by
      linarith [(hIntegralBound t).2]
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < (1 - a) / 2 := by linarith
    filter_upwards [hLower ((1 - a) / 2) hε] with t ht
    nlinarith [ht]
  · intro a ha
    have hε : 0 < a - 1 := by linarith
    filter_upwards [htop (a - 1) hε] with t ht
    linarith

end DOZZ.Proofs

end
