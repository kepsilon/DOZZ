/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.PositiveMomentStrip

/-! The definition `DOZZ.realUpperTail`. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Finite probability upper tail, the literal object of [KRV, Lemma 10.4]. -/
noncomputable def realUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (_hY : AEMeasurable Y P) (t : ℝ) : ℝ := (P {ω | t < Y ω}).toReal

end DOZZ
