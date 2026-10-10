/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootedMass

/-! The definition `DOZZ.gammaHalfRootedCoefficient`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The exact coefficient `A` in the one-rooted Taylor asymptotic of [KRV, Lemma 9.2]. -/
noncomputable def gammaHalfRootedCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) : ℝ :=
  (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
    (∫⁻ ω, ENNReal.rpow (gammaHalfRootedMass γ α₁ α₂ α₃ M ω)
      (-p - 1) ∂P).toReal

end DOZZ
