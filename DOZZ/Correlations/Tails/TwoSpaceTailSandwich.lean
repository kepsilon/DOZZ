/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ENNRealTailPerturbation

/-! Transport a localized law while bounding the two remainders on their own probability spaces. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem two_space_localization_tail_sandwich
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsFiniteMeasure P] [IsFiniteMeasure P']
    (A L E : Ω → ℝ≥0∞) (B L' E' : Ω' → ℝ≥0∞)
    (hL : AEMeasurable L P) (hL' : AEMeasurable L' P') (hLaw : P.map L = P'.map L')
    (hSource : ∀ᵐ ω ∂P, L ω ≤ A ω ∧ A ω ≤ L ω+E ω)
    (hCopy : ∀ᵐ ω ∂P', L' ω ≤ B ω+E' ω ∧ B ω ≤ L' ω+E' ω)
    (x h : ℝ) (hh : 0 ≤ h) (hhx : 2*h ≤ x) :
    (P' {ω | ENNReal.ofReal (x+h) < B ω}).toReal-
      (P' {ω | ENNReal.ofReal h < E' ω}).toReal ≤
        (P {ω | ENNReal.ofReal x < A ω}).toReal ∧
    (P {ω | ENNReal.ofReal x < A ω}).toReal ≤
      (P' {ω | ENNReal.ofReal (x-2*h) < B ω}).toReal+
        (P {ω | ENNReal.ofReal h < E ω}).toReal+
        (P' {ω | ENNReal.ofReal h < E' ω}).toReal := by
  have hT (y : ℝ) : P {ω | ENNReal.ofReal y < L ω} =
      P' {ω | ENNReal.ofReal y < L' ω} := by
    have h := congrArg (fun μ : Measure ℝ≥0∞ => μ (Ioi (ENNReal.ofReal y))) hLaw
    rw [Measure.map_apply_of_aemeasurable hL measurableSet_Ioi,
      Measure.map_apply_of_aemeasurable hL' measurableSet_Ioi] at h
    exact h
  constructor
  · have hb := ennreal_tail_domination P' B L' E'
      (hCopy.mono fun _ h => h.2) (x+h) h hh (by linarith only [hh,hhx])
    rw [add_sub_cancel_right,← hT x] at hb
    have hm : P {ω | ENNReal.ofReal x < L ω} ≤ P {ω | ENNReal.ofReal x < A ω} :=
      measure_mono_ae (hSource.mono fun ω hω hlt => hlt.trans_le hω.1)
    have ht := ENNReal.toReal_mono (by finiteness) hm
    linarith only [hb,ht]
  · have ha := ennreal_tail_domination P A L E
      (hSource.mono fun _ h => h.2) x h hh (by linarith only [hh,hhx])
    have hb := ennreal_tail_domination P' L' B E'
      (hCopy.mono fun _ h => h.1) (x-h) h hh (by linarith only [hhx])
    rw [hT (x-h)] at ha
    have heq : x-h-h = x-2*h := by ring
    rw [heq] at hb
    linarith only [ha,hb]


end DOZZ.Proofs
