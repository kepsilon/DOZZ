/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.Uniqueness

/-! The statement `DOZZ.IsGaussHypergeometric.eqOn`,
proved by `DOZZ.Proofs.IsGaussHypergeometric.eqOn`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Uniqueness of the principal continuation on the slit plane [KRV, (Fpmdef)]; deliberately not
global equality of total functions whose off-slit values are unspecified. -/
theorem IsGaussHypergeometric.eqOn {a b c : ℂ} {F G : ℂ → ℂ}
    (hF : IsGaussHypergeometric a b c F) (hG : IsGaussHypergeometric a b c G) :
    EqOn F G gaussSlitPlane := by exact DOZZ.Proofs.IsGaussHypergeometric.eqOn hF hG

end DOZZ
