/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Lateral.ReflectionJointLaw

/-! The statement `DOZZ.equatorGFF_lateral_GMC_decomposition`,
proved by `DOZZ.Proofs.equatorGFF_lateral_GMC_decomposition`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The equator field and its GMC admit the two-sided radial/lateral decomposition. The lateral
projection is defined by `lateralProjectedGMC`, so this theorem supplies the independence,
stationarity, and intensity interface from the `IsGMCOf` carrier. See [KRV, §3.1]. -/
theorem equatorGFF_lateral_GMC_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ A : Ω → TwoSidedPath,
      (∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
        ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) ∧
      AEMeasurable A P ∧ (∀ᵐ ω ∂P, A ω 0 = 0) ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
        IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
          (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
        AEMeasurable (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IndepFun (fun ω => A ω) (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IsLateralGMCOf P γ (fun ω =>
          lateralProjectedGMC γ (A ω) (M ω)) := by exact DOZZ.Proofs.equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ2 hX hM

end DOZZ
