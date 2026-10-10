/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.ComplexPolydisc

/-! The definition `DOZZ.positiveMomentStrip`. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Positive-real-part moment strip of [KRV, Lemma 10.4]. -/
def positiveMomentStrip (b : ℝ) : Set ℂ := {s | 0 < s.re ∧ s.re < b}

end DOZZ
