/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def

/-! The definition `DOZZ.complexPolydisc`. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Literal finite-coordinate polydisc. -/
def complexPolydisc {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ) : Set (Fin N → ℂ) :=
  {z | ∀ i, ‖z i - a i‖ < R i}

end DOZZ
