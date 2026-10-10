/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourPointSExp

/-! The definition `DOZZ.fourPointT`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The reduced four-point correlation `T`, literally as in [KRV, (Tdefi0)]. -/
noncomputable def fourPointT {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ : ℝ)
    (α₀ α₁ α₂ α₃ : ℝ) (z : ℂ) : ℝ :=
  2 * μ ^ (-fourPointSExp γ α₀ α₁ α₂ α₃) / γ *
    Real.Gamma (fourPointSExp γ α₀ α₁ α₂ α₃) *
      (∫⁻ ω, ENNReal.rpow
        (coulombMass γ (M ω) ![α₀, α₁, α₂] ![z, 0, 1] α₃)
        (-fourPointSExp γ α₀ α₁ α₂ α₃) ∂P).toReal

end DOZZ
