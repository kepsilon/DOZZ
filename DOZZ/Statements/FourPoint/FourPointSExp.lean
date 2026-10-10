/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.Statements.GMC.GmcRootedMeasure
public import DOZZ.Statements.Defs.ConformalWeight
public import DOZZ.Statements.Defs.LFun
public import DOZZ.Statements.Brownian.BrownianPath
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
public import DOZZ.Statements.Hypergeom.GaussCutPlane
public import DOZZ.Statements.Hypergeom.GaussFMinus
public import DOZZ.Statements.Hypergeom.GaussFPlus
public import DOZZ.Statements.Hypergeom.IsRealGaussSolution
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant

/-! The definition `DOZZ.fourPointSExp`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The zero-mode exponent for the four-point function `T`, [KRV, (Tdefi0)]. -/
noncomputable def fourPointSExp (γ α₀ α₁ α₂ α₃ : ℝ) : ℝ :=
  (α₀ + α₁ + α₂ + α₃ - 2 * Q γ) / γ

end DOZZ
