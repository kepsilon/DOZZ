/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Distr
public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.NormPlus
public import DOZZ.Statements.Defs.Q
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.Statements.Brownian.BrownianPath
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.ReflectionExponent
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.Statements.Brownian.ReflectionR
public import Mathlib.Analysis.Analytic.Basic

/-! The definition `DOZZ.nPointSExp`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The charge sum in the N-insertion zero-mode exponent. -/
noncomputable def nPointSExp {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) : ℝ :=
  ((∑ i : Fin N, α i) - 2 * Q γ) / γ

end DOZZ
