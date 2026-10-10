/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.ComplexPolydisc
import DOZZ.Complex.Weierstrass

/-! The statement `DOZZ.differentiableOn_of_tendstoLocallyUniformlyOn_fin`,
proved by `DOZZ.Proofs.differentiableOn_of_tendstoLocallyUniformlyOn_fin`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Several-variable Weierstrass, including first-derivative convergence (see [KRV, §6]). The
pinned Mathlib theorem has source `ℂ`, whereas this source is `ℂ^N`. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn_fin {N : ℕ}
    (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (F : ℕ → (Fin N → ℂ) → ℂ) (f : (Fin N → ℂ) → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) atTop U := by exact DOZZ.Proofs.differentiableOn_of_tendstoLocallyUniformlyOn_fin U hU F f hF hlim

end DOZZ
