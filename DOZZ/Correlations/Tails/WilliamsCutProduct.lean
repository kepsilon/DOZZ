/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsCutMonotonicity
public import DOZZ.Correlations.Tails.WilliamsMaximumTail

/-! Last-cut ordering when the cut level is the independent Williams maximum. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem williams_maximum_pos_ae (ν : ℝ) :
    ∀ᵐ m ∂brownianMaximumReferenceLaw ν, 0 < m := by
  rw [ae_iff]
  simp only [not_lt]
  change brownianMaximumReferenceLaw ν (Iic 0) = 0
  rw [brownianMaximumReferenceLaw, withDensity_apply _ measurableSet_Iic]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Iic] with m hm
  change ENNReal.ofReal (if 0 < m then 2*ν*Real.exp (-2*ν*m) else 0) = 0
  rw [ite_eq_right (not_lt.mpr hm), ENNReal.ofReal_zero]

/-- Fixed-level ordering passes through Fubini to the random maximum. This avoids
requiring a common probability-one event for an uncountable family of cut levels. -/
theorem williams_last_exit_mono_prod_ae (ν c : ℝ) (hν : 0 < ν)
    (P : Measure BrownianPath) (hP : IsNegativeConditionedBrownianLaw ν P) :
    ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P,
      c ≤ q.1 → negativeLastExitTime q.2 c ≤ negativeLastExitTime q.2 q.1 := by
  let : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
    isProbabilityMeasure_brownianMaximumReferenceLaw hν
  let : IsProbabilityMeasure P := hP.2.1
  have hset : MeasurableSet {q : ℝ × BrownianPath |
      c ≤ q.1 → negativeLastExitTime q.2 c ≤ negativeLastExitTime q.2 q.1} := by
    apply MeasurableSet.imp (measurableSet_le measurable_const measurable_fst)
    exact measurableSet_le (measurable_negativeLastExitTime_joint.comp
      (measurable_const.prodMk measurable_snd)) measurable_negativeLastExitTime_joint
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  filter_upwards [williams_maximum_pos_ae ν] with m hm
  by_cases hc : c ≤ m
  · exact (conditioned_last_exit_mono_ae ν c m hν hm hc P hP).mono
      (fun _ h => fun _ => h)
  · exact ae_of_all _ fun _ h => False.elim (hc h)


end DOZZ.Proofs
