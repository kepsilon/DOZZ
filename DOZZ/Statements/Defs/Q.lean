/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.DiscreteSubset

/-! The definition `DOZZ.Q`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `Q = 2/γ + γ/2` ([KRV, (valueQ)]). -/
noncomputable def Q (γ : ℝ) : ℝ := 2 / γ + γ / 2

end DOZZ
