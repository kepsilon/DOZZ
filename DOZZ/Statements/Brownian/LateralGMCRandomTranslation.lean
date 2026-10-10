/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianStoppedEvents
import DOZZ.Brownian.LateralTranslation

/-! The statement `DOZZ.lateralGMC_random_translation`,
proved by `DOZZ.Proofs.lateralGMC_random_translation`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A measurable radial random path's translation preserves the lateral-measure law and
independence. -/
theorem lateralGMC_random_translation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (D : Ω → BrownianPath) (hD : AEMeasurable D P)
    (hInd : IndepFun D Z P) (T : BrownianPath → ℝ) (hT : Measurable T) :
    AEMeasurable (fun ω => (Z ω).map (fun s => s + T (D ω))) P ∧
      P.map (fun ω => (Z ω).map (fun s => s + T (D ω))) = P.map Z ∧
      IndepFun D (fun ω => (Z ω).map (fun s => s + T (D ω))) P := by exact DOZZ.Proofs.lateralGMC_random_translation P γ Z hZ D hD hInd T hT

end DOZZ
