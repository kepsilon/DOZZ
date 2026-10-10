/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.ODE.SlitPlaneGluing

/-! The statement `DOZZ.gauss_hypergeometric_exists`,
proved by `DOZZ.Proofs.gauss_hypergeometric_exists`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Existence of the principal continuation of the Gauss hypergeometric function [KRV, (Fpmdef)]. No
arbitrary choice-defined Gauss function is exported; the witnesses are used only through their
characterization. -/
theorem gauss_hypergeometric_exists :
    ∃ H : ℂ → ℂ → ℂ → ℂ → ℂ, IsGaussHypergeometricFamily H := by exact DOZZ.Proofs.gauss_hypergeometric_exists

end DOZZ
