/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsMaximumTail
public import Mathlib.MeasureTheory.Integral.Prod

/-! Exact conditioning on the independent Pareto factor in the one-insertion tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set

namespace DOZZ.Proofs

theorem williams_scaled_pareto_tail (ν γ x a : ℝ)
    (hν : 0 < ν) (hγ : 0 < γ) (hx : 0 < x) :
    ((brownianMaximumReferenceLaw ν) {m | x < a*Real.exp (γ*m)}).toReal =
      if a ≤ 0 then 0 else if a ≤ x then (a/x)^(2*ν/γ) else 1 := by
  by_cases ha0 : a ≤ 0
  · have he : {m : ℝ | x < a*Real.exp (γ*m)} = ∅ := by
      ext m
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_lt.mpr ((mul_nonpos_of_nonpos_of_nonneg ha0 (Real.exp_nonneg _)).trans hx.le)
    rw [he, measure_empty, ENNReal.toReal_zero, ite_eq_left ha0]
  · have ha : 0 < a := lt_of_not_ge ha0
    have hy : 0 < x/a := div_pos hx ha
    have he : {m : ℝ | x < a*Real.exp (γ*m)} = Ioi (Real.log (x/a)/γ) := by
      ext m
      simp only [mem_ofPred_eq, mem_Ioi, div_lt_iff₀ hγ]
      rw [mul_comm m γ, Real.log_lt_iff_lt_exp hy, div_lt_iff₀ ha, mul_comm a]
    rw [he, williams_maximum_tail ν hν, ite_eq_right ha0]
    by_cases hax : a ≤ x
    · have hu : 0 ≤ Real.log (x/a)/γ :=
        div_nonneg (Real.log_nonneg ((one_le_div ha).mpr hax)) hγ.le
      rw [ite_eq_left hu, ite_eq_left hax, Real.rpow_def_of_pos (div_pos ha hx),
        Real.log_div hx.ne' ha.ne', Real.log_div ha.ne' hx.ne']
      congr 1
      ring
    · have hu : Real.log (x/a)/γ < 0 := div_neg_of_neg_of_pos
        (Real.log_neg hy ((div_lt_one ha).mpr (lt_of_not_ge hax))) hγ
      rw [ite_eq_right (not_le.mpr hu), ite_eq_right hax]

/-- Conditioning is an exact probability identity before imposing moment assumptions. -/
theorem williams_pareto_product_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (ν γ x : ℝ)
    (hν : 0 < ν) (hγ : 0 < γ) (hx : 0 < x) :
    (((brownianMaximumReferenceLaw ν).prod P) {q : ℝ × Ω | x < A q.2*Real.exp (γ*q.1)}).toReal =
      ∫ ω, (if A ω ≤ 0 then 0 else if A ω ≤ x then (A ω/x)^(2*ν/γ) else 1) ∂P := by
  let μ := brownianMaximumReferenceLaw ν
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  have hs : MeasurableSet {q : ℝ × Ω | x < A q.2*Real.exp (γ*q.1)} :=
    measurableSet_lt measurable_const ((hA.comp measurable_snd).mul
      (measurable_fst.const_mul γ).exp)
  have hm := measurable_measure_prodMk_right (μ := μ) hs
  rw [Measure.prod_apply_symm hs, ← integral_toReal hm.aemeasurable
    (ae_of_all _ fun _ => measure_lt_top μ _)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => williams_scaled_pareto_tail ν γ x (A ω) hν hγ hx


end DOZZ.Proofs
