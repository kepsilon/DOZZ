/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.HorizontalStrip
import DOZZ.Complex.Basic

/-! The statement `DOZZ.meromorphicOn_strip_constant_of_dense_periods`,
proved by `DOZZ.Proofs.meromorphicOn_strip_constant_of_dense_periods`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Two incommensurable positive real periods force constant meromorphic germs (see
[KRV, §10.6 and §11]). This expresses absence of poles without imposing arbitrary values at
isolated points of a totalized representative. -/
theorem meromorphicOn_strip_constant_of_dense_periods
    (h : ℝ) (hh : 0 < h) (f : ℂ → ℂ) (hf : MeromorphicOn f (horizontalStrip h))
    (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hirr : ∀ q : ℚ, T₁ / T₂ ≠ (q : ℝ))
    (hp₁ : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (T₁ : ℂ))) =ᶠ[𝓝[≠] z] f)
    (hp₂ : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (T₂ : ℂ))) =ᶠ[𝓝[≠] z] f) :
    ∃! c : ℂ, ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] (fun _ => c) := by exact DOZZ.Proofs.meromorphicOn_strip_constant_of_dense_periods h hh f hf T₁ T₂ hT₁ hT₂ hirr hp₁ hp₂

end DOZZ
