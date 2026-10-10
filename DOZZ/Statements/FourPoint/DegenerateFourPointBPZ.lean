/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.BPZ.DegenerateFourPointBPZ

/-! The statement `DOZZ.degenerateFourPoint_BPZ`,
proved by `DOZZ.Proofs.degenerateFourPoint_BPZ`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- For either degenerate insertion, the literal reduced function `T` satisfies the Wirtinger form
of the Gauss equation with the parameters of [KRV, (defabcfirst)]. The two values of `χ` are kept in
the same statement; the Seiberg sum is the one for `(-χ, α₁, α₂, α₃)`. -/
theorem degenerateFourPoint_BPZ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsRealGaussSolution
      (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃)
      (gaussParameterC γ χ α₁)
      (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z) := by exact DOZZ.Proofs.degenerateFourPoint_BPZ P X M γ μ χ α₁ α₂ α₃ hγ hγ₂ hμ hχ hα₁ hα₂ hα₃ hs hX hM

end DOZZ
