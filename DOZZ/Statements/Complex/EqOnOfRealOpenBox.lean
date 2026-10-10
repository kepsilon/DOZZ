/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.ComplexPolydisc
import DOZZ.Complex.Identity

/-! The statement `DOZZ.eqOn_of_real_open_box`, proved by `DOZZ.Proofs.eqOn_of_real_open_box`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Identity from a nonempty real open box in an open connected complex domain. -/
theorem eqOn_of_real_open_box {N : ℕ} (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (hconn : IsPreconnected U) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (lo hi : Fin N → ℝ) (hbox : ∀ i, lo i < hi i)
    (hinside : ∀ x : Fin N → ℝ, (∀ i, lo i < x i ∧ x i < hi i) →
      (fun i => (x i : ℂ)) ∈ U)
    (heq : ∀ x : Fin N → ℝ, (∀ i, lo i < x i ∧ x i < hi i) →
      f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) : EqOn f g U := by exact DOZZ.Proofs.eqOn_of_real_open_box U hU hconn f g hf hg lo hi hbox hinside heq

end DOZZ
