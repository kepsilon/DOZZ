/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.TwoTailRational

/-! The definition `DOZZ.horizontalStrip`. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Horizontal strip, for germ continuation in the final quotient argument and in
`meromorphicOn_strip_constant_of_dense_periods`; see [KRV, §10.6 and §11]. -/
def horizontalStrip (h : ℝ) : Set ℂ := {z | |z.im| < h}

end DOZZ
