/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.GaussSystem
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Parameter regularity of the Gauss system coefficient family. -/

@[expose] public section

namespace DOZZ.Proofs

/-- At fixed `z`, the first-order Gauss operator is an entire function of `(a,b,c)`. -/
theorem gaussSystemOperator_differentiable_params (z : ℂ) :
    Differentiable ℂ
      (fun p : ℂ × ℂ × ℂ => gaussSystemOperator p.1 p.2.1 p.2.2 z) := by
  dsimp [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]
  fun_prop

/-- The Gauss system operator is smooth in its three complex parameters at fixed `z`. -/
theorem gaussSystemOperator_contDiff_params (z : ℂ) :
    ContDiff ℂ ⊤
      (fun p : ℂ × ℂ × ℂ => gaussSystemOperator p.1 p.2.1 p.2.2 z) := by
  dsimp [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]
  fun_prop





end DOZZ.Proofs
