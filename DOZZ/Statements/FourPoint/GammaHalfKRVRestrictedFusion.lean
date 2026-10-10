/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import DOZZ.FourPoint.Fusion.KRVRestrictedFusion

/-! The statement `DOZZ.gammaHalf_KRV_restricted_fusion`,
proved by `DOZZ.Proofs.gammaHalf_KRV_restricted_fusion`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The restricted `γ/2` collision asymptotic of [KRV-local, Lemma 4.5]. The four-point
normalization of [KRV-local] is twice that of [KRV]; this statement uses only the reduced `T` of
[KRV]. -/
theorem gammaHalf_KRV_restricted_fusion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγsq : γ ^ 2 < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 + 1 / γ < α₁) (hαhi : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let κ := γ * (Q γ - α₁)
    ∃ r : ℂ → ℝ,
      (∀ z, fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              (‖z‖ ^ κ : ℝ) + r z) ∧
        Tendsto (fun z => r z / ‖z‖ ^ κ)
          (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by exact DOZZ.Proofs.gammaHalf_KRV_restricted_fusion P X M γ μ α₁ α₂ α₃ hγ hγsq hμ hαlo hαhi hα₂ hα₃ hs hX hM

end DOZZ
