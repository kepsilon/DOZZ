/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsSourceLateralProjection

/-! The definition `DOZZ.IsLateralGMCOf`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Source carrier: the lateral projection along the circle-average radial path.
The moment, stationarity, and symmetry fields are
consequences of this polar projection; they do not by themselves characterize a lateral GMC law. -/
def IsLateralGMCOf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) : Prop :=
  0 < γ ∧ γ < 2 ∧ IsProbabilityMeasure P ∧ AEMeasurable Z P ∧
    (∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Set.Icc a b) < ⊤) ∧
      (∀ t : ℝ,
        P.map (fun ω => (Z ω).map (fun s => s + t)) = P.map Z) ∧
      P.map (fun ω => (Z ω).map (fun s => -s)) = P.map Z ∧
        (∀ a b : ℝ, a < b →
          ∫⁻ ω, Z ω (Set.Ioc a b) ∂P = ENNReal.ofReal (2 * Real.pi * (b - a))) ∧
        ∃ X : Ω → Distr, ∃ M : Ω → Measure ℂ,
          IsSourceLateralProjection P X γ M Z

end DOZZ
