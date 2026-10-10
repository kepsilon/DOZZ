/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterC
import DOZZ.Hypergeom.Planar.Beta

/-! The statement `DOZZ.beta_negative_power_integral`,
proved by `DOZZ.Proofs.beta_negative_power_integral`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The integral of [KRV, Lemma 12.6] as a genuine signed Lebesgue integral, with its integrability
proved rather than hypothesized. -/
theorem beta_negative_power_integral (p a : ℝ) (hp : 0 < p) (ha : 1 < a) (ha₂ : a < 2) :
    IntegrableOn (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) (Ioi 0) volume ∧
      (∫ v : ℝ in Ioi 0, ((1 + v) ^ (-p) - 1) * v ^ (-a)) =
        Real.Gamma (1 - a) * Real.Gamma (p + a - 1) / Real.Gamma p := by exact DOZZ.Proofs.beta_negative_power_integral p a hp ha ha₂

end DOZZ
