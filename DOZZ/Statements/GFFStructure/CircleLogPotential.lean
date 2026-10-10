/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The definition `DOZZ.circleLogPotential`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Literal closed circle potential on its domain `d ≥ 0`, `a, b > 0` (see [KRV, (hatGformula)] and
[KRV, (circleav)]). The series also covers `u = 1`. -/
noncomputable def circleLogPotential (d₀ : ℝ≥0)
    (a₀ b₀ : {r : ℝ // 0 < r}) : ℝ :=
  let d : ℝ := d₀
  let a : ℝ := a₀
  let b : ℝ := b₀
  if d = 0 then Real.log (max a b)
  else if d + a ≤ b then Real.log b
  else if b ≤ |d - a| then Real.log (max d a)
  else
    let θ := Real.arccos ((b ^ 2 - d ^ 2 - a ^ 2) / (2 * d * a))
    let c := max d a
    let u := min d a / c
    Real.log b + θ / Real.pi * Real.log (c / b) +
      (1 / Real.pi) * ∑' k : ℕ,
        (-1 : ℝ) ^ k * u ^ (k + 1) * Real.sin ((k + 1 : ℕ) * θ) /
          ((k + 1 : ℕ) : ℝ) ^ 2

end DOZZ
