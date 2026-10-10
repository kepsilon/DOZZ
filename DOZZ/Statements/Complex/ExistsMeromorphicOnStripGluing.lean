/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.HorizontalStrip
import DOZZ.Complex.Basic

/-! The statement `DOZZ.exists_meromorphicOn_strip_gluing`,
proved by `DOZZ.Proofs.exists_meromorphicOn_strip_gluing`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Gluing compatible meromorphic pieces, unique as punctured germs (see [KRV, §11]).
Compatibility is required at every point of every overlap, not merely one component. -/
theorem exists_meromorphicOn_strip_gluing {ι : Type*}
    (h : ℝ) (hh : 0 < h) (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = horizontalStrip h) (f : ι → ℂ → ℂ)
    (hf : ∀ i, MeromorphicOn (f i) (U i))
    (hcompat : ∀ i j z, z ∈ U i → z ∈ U j → f i =ᶠ[𝓝[≠] z] f j) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (horizontalStrip h) ∧
      (∀ i z, z ∈ U i → F =ᶠ[𝓝[≠] z] f i) ∧
      (∀ G : ℂ → ℂ, MeromorphicOn G (horizontalStrip h) →
        (∀ i z, z ∈ U i → G =ᶠ[𝓝[≠] z] f i) →
        ∀ z ∈ horizontalStrip h, F =ᶠ[𝓝[≠] z] G) := by exact DOZZ.Proofs.exists_meromorphicOn_strip_gluing h hh U hU hcover f hf hcompat

end DOZZ
