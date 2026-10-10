/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Moment bounds for the literal extended-real remainder events. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem ennreal_power_tail_le_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : Ω → ℝ≥0∞) (hE : AEMeasurable E P) (r h : ℝ)
    (hr : 0 < r) (hh : 0 < h) (C : ℝ≥0∞) (hC : C < ⊤)
    (hm : (∫⁻ ω, E ω^r ∂P) ≤ C) :
    (P {ω | ENNReal.ofReal h < E ω}).toReal ≤ C.toReal*h^(-r) := by
  have hsub : {ω | ENNReal.ofReal h < E ω} ⊆
      {ω | ENNReal.ofReal (h^r) ≤ E ω^r} := by
    intro ω hω
    rw [← ENNReal.ofReal_rpow_of_pos hh]
    exact ENNReal.rpow_le_rpow hω.le hr.le
  have hp : ENNReal.ofReal (h^r) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hh r)).ne'
  have hb0 := meas_ge_le_lintegral_div (hE.pow_const r) hp ENNReal.ofReal_ne_top
  change P {ω | ENNReal.ofReal (h^r) ≤ E ω^r} ≤ (∫⁻ ω, E ω^r ∂P)/ENNReal.ofReal (h^r) at hb0
  have hb := (measure_mono (μ := P) hsub).trans hb0
  have hquot : (∫⁻ ω, E ω^r ∂P)/ENNReal.ofReal (h^r) ≤ C/ENNReal.ofReal (h^r) :=
    ENNReal.div_le_div_right hm _
  have ht := ENNReal.toReal_mono
    (ENNReal.div_ne_top hC.ne hp) (hb.trans hquot)
  rw [ENNReal.toReal_div,ENNReal.toReal_ofReal (Real.rpow_nonneg hh.le _)] at ht
  have he : C.toReal/(h^r) = C.toReal*h^(-r) := by
    rw [Real.rpow_neg hh.le,div_eq_mul_inv]
  exact ht.trans_eq he


end DOZZ.Proofs
