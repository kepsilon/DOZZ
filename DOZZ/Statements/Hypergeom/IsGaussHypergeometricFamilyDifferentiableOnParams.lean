/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
import DOZZ.Hypergeom.ODE.ParameterDifferentiabilityPath

/-! The statement `DOZZ.IsGaussHypergeometricFamily.differentiableOn_params`,
proved by `DOZZ.Proofs.IsGaussHypergeometricFamily.differentiableOn_params`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Joint parameter holomorphy of the characterized continuation [KRV, (Fpmdef)] away from
denominator poles. -/
theorem IsGaussHypergeometricFamily.differentiableOn_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) {z : ℂ} (hz : z ∈ gaussSlitPlane) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2 z)
      {p | ∀ n : ℕ, p.2.2 ≠ -(n : ℂ)} := by exact DOZZ.Proofs.IsGaussHypergeometricFamily.differentiableOn_params hH hz

end DOZZ
