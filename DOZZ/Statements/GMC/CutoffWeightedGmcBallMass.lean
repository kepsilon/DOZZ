/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance

/-! The definition `DOZZ.cutoffWeightedGmcBallMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Cutoff weighted GMC mass with the distance singularity regularized at scale `δ`. See
[KRV, §7.2]. -/
noncomputable def cutoffWeightedGmcBallMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ α : ℝ) (z : ℂ)
    (R δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball z R,
    ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ∂
      regularizedGMC P Xc γ (Real.log (1 / δ)) ω

end DOZZ
