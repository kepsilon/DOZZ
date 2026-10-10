/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.NPointSExp
public import DOZZ.Statements.Correlations.ExtendedSeibergN
public import DOZZ.Statements.Correlations.NPointCoulombPrefactor
public import DOZZ.Statements.Correlations.UnitVolumeNPointCorrelation
public import DOZZ.Statements.Correlations.OneInsertionMomentCeiling
public import DOZZ.Statements.Correlations.OneInsertionErrorCeiling
public import DOZZ.Statements.Correlations.TwoInsertionPointLoss
public import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
public import DOZZ.Statements.FourPoint.DualCrossingMultiplier
public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.Statements.Defs.ReflectionDOZZ
public import DOZZ.Statements.Defs.ConformalWeight
public import DOZZ.Statements.Defs.LFun
public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Statements.Brownian.BrownianPath
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.ReflectionExponent
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.Statements.Complex.HorizontalStrip
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Topology.DiscreteSubset

/-! The definition `DOZZ.MobiusChart`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Finite Möbius charts, with their coefficients kept explicit. -/
structure MobiusChart where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  determinant_ne : a * d - b * c ≠ 0

end DOZZ
