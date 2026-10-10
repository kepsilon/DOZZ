/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.LastExitAfterAbove
public import DOZZ.Brownian.Reflection.LastCut
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
/-! The retained reflection mass increases with the Williams maximum cutoff. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A continuous path which later descends below the deeper level must visit it after the
last visit to the shallower level. -/
theorem reflected_lastExit_le_of_future_below (p : BrownianPath) (H m : ℝ)
    (hHm : H ≤ m) (hH : p (negativeLastExitTime p H) = -H)
    (hb : BddAbove {u : ℝ≥0 | p u = -m})
    (hf : ∃ t : ℝ≥0, negativeLastExitTime p H ≤ t ∧ p t ≤ -m) :
    negativeLastExitTime p H ≤ negativeLastExitTime p m := by
  obtain ⟨t, ht, hp⟩ := hf
  have hlevel : -m ∈ Icc (p t) (p (negativeLastExitTime p H)) :=
    ⟨hp, by rw [hH]; exact neg_le_neg hHm⟩
  obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc' ht p.continuous.continuousOn hlevel
  exact hu.1.trans (le_csSup hb hpu)

/-- For the actual conditioned path law, the last exit is monotone in each fixed positive
pair of levels. No assertion at an uncountable intersection of null events is needed. -/
theorem reflected_conditioned_lastExit_mono_ae
    {ν : ℝ} {Qν B : Measure BrownianPath} [SFinite B]
    (hQν : IsNegativeConditionedBrownianLaw ν Qν)
    (hB : IsBrownianReal (fun t p => p t) B) (hν : 0 < ν)
    (H m : ℝ≥0) (hH : 0 < (H : ℝ)) (hHm : H ≤ m) :
    ∀ᵐ p ∂Qν, negativeLastExitTime p H ≤ negativeLastExitTime p m := by
  have hm : 0 < (m : ℝ) := lt_of_lt_of_le hH (by exact_mod_cast hHm)
  filter_upwards [ae_negativeConditionedLevelHitSet_nonempty_bddAbove hQν hB hν H hH,
    ae_negativeConditionedLevelHitSet_nonempty_bddAbove hQν hB hν m hm,
    ae_negativeConditionedPath_above_after_lastExit hQν hB hν m hm] with p hpH hpm hpafter
  have he := negativeLastExitTime_mem_of_nonempty_bddAbove p H hpH.1 hpH.2
  apply reflected_lastExit_le_of_future_below p H m (by exact_mod_cast hHm) he hpm.2
  let t := max (negativeLastExitTime p H) (negativeLastExitTime p m) + 1
  refine ⟨t, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le)
  · have hlt : negativeLastExitTime p m < t :=
      lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ zero_lt_one)
    have hh := hpafter t hlt
    linarith only [hh]

/-- Increasing the last-exit cutoff retains a larger half-line mass. -/
theorem reflected_cutMass_mono_of_lastExit {Ω : Type*} (γ H m : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω)
    (hL : negativeLastExitTime (B ω).2 H ≤ negativeLastExitTime (B ω).2 m) :
    twoSidedReflectionCutMass γ H B Z ω ≤ twoSidedReflectionCutMass γ m B Z ω := by
  unfold twoSidedReflectionCutMass
  apply lintegral_mono
  intro s
  have hcoe : (negativeLastExitTime (B ω).2 H : ℝ) ≤ negativeLastExitTime (B ω).2 m :=
    by exact_mod_cast hL
  beta_reduce
  split_ifs with hHs hms
  · exact le_rfl
  · exfalso
    exact hms (by linarith only [hHs, hcoe])
  · exact zero_le
  · exact le_rfl

/-- The actual two-sided conditioned carrier supplies both bounds for the retained mass at
every fixed maximum exceeding the positive buffer. -/
theorem reflected_reflection_cut_squeeze_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν)
    (B₀ : Measure BrownianPath) [SFinite B₀]
    (hB₀ : IsBrownianReal (fun t p => p t) B₀) (hν : 0 < ν)
    (H m : ℝ≥0) (hH : 0 < (H : ℝ)) (hHm : H ≤ m) :
    ∀ᵐ ω ∂P, twoSidedReflectionCutMass γ H B Z ω ≤
      twoSidedReflectionCutMass γ m B Z ω ∧
      twoSidedReflectionCutMass γ m B Z ω ≤ twoSidedReflectionMass γ B Z ω := by
  have hmono := reflected_conditioned_lastExit_mono_ae hB.2.1.2 hB₀ hν H m hH hHm
  filter_upwards [ae_of_ae_map hB.2.1.1 hmono] with ω hω
  exact ⟨reflected_cutMass_mono_of_lastExit γ H m B Z ω hω,
    twoSidedReflectionCutMass_le_mass γ m B Z ω⟩

/-- The variable Williams maximum can be integrated without taking an uncountable
intersection of the fixed-level full-measure events. -/
theorem reflected_conditioned_random_lastExit_squeeze
    (μ : Measure ℝ≥0) [SFinite μ]
    {ν : ℝ} {Qν B : Measure BrownianPath} [SFinite B]
    (hQν : IsNegativeConditionedBrownianLaw ν Qν)
    (hB : IsBrownianReal (fun t p => p t) B) (hν : 0 < ν)
    (H : ℝ≥0) (hH : 0 < (H : ℝ)) :
    ∀ᵐ z : ℝ≥0 × BrownianPath ∂μ.prod Qν, H ≤ z.1 →
      negativeLastExitTime z.2 H ≤ negativeLastExitTime z.2 z.1 := by
  let _ : IsProbabilityMeasure Qν := hQν.2.1
  have hleft : Measurable (fun z : ℝ≥0 × BrownianPath => negativeLastExitTime z.2 H) :=
    measurable_negativeLastExitTime_joint.comp (measurable_const.prodMk measurable_snd)
  have hright : Measurable (fun z : ℝ≥0 × BrownianPath => negativeLastExitTime z.2 z.1) :=
    measurable_negativeLastExitTime_joint.comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hs : MeasurableSet {z : ℝ≥0 × BrownianPath | H ≤ z.1 →
      negativeLastExitTime z.2 H ≤ negativeLastExitTime z.2 z.1} := by
    have hh := (measurableSet_le (measurable_const (a := H)) (measurable_fst : Measurable
      (fun z : ℝ≥0 × BrownianPath => z.1))).compl.union (measurableSet_le hleft hright)
    convert hh using 1
    ext z
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, imp_iff_not_or]
  rw [Measure.ae_prod_iff_ae_ae hs]
  apply ae_of_all μ
  intro m
  by_cases hm : H ≤ m
  · exact (reflected_conditioned_lastExit_mono_ae hQν hB hν H m hH hm).mono
      fun _ h _ => h
  · exact ae_of_all Qν fun _ h => (hm h).elim

end DOZZ.Proofs
