/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.PoleSubtracted.Holomorphy

/-! The statement `DOZZ.poleSubtractedObservable_holomorphic`,
proved by `DOZZ.Proofs.poleSubtractedObservable_holomorphic`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- After subtracting the two local masses, the real observable of [KRV, Lemma 10.3] extends
holomorphically to a neighborhood of the entire interval of that lemma. The last conjunct records
the compact-uniform Cauchy decay of the limit-chaos analytic approximants; the corrected Markov
threshold (erratum K4, see docs/ERRATA-AND-DEVIATIONS.md) is part of this assertion. -/
theorem poleSubtractedObservable_holomorphic
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ η δ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hM : IsGMCOf P X γ M) (hWindow : TwoPoleWindow γ η δ) :
    ∃ V : Set ℂ, IsOpen V ∧
      (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V) ∧
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F V ∧
        (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ →
          F (x : ℂ) =
            (poleSubtractedObservable P M γ η x : ℂ)) ∧
        (∀ n : ℕ, DifferentiableOn ℂ
          (poleSubtractedCutoff P Xc M γ η n) V) ∧
        TendstoLocallyUniformlyOn (poleSubtractedCutoff P Xc M γ η) F atTop V ∧
          ∀ K : Set ℂ, IsCompact K → K ⊆ V →
            ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
              ∀ n : ℕ, ∀ z ∈ K,
                ‖poleSubtractedCutoff P Xc M γ η (n + 1) z -
                    poleSubtractedCutoff P Xc M γ η n z‖ ≤
                  C * Real.exp (-κ * n) := by exact DOZZ.Proofs.poleSubtractedObservable_holomorphic P X M γ η δ hγ hγ2 hX Xc hXc hM hWindow

end DOZZ
