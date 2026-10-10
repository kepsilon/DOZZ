/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootOnlyConvergence
public import DOZZ.FourPoint.Fusion.RootedLowerBound
import DOZZ.GMC.SharpMoments.MomentConvergence

/-! # Convergence of the inverse moments of the moving rooted mass -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- All inverse orders are uniformly bounded, including a larger order for Vitali. -/
theorem fusionRootOnlyMass_inverse_moment_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ y z : ℂ, ‖z‖ ≤ 1 →
      (∫⁻ ω, fusionRootOnlyMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := fusion_rootedMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ s hs
  refine ⟨C, hC, ?_⟩
  intro y z hz
  have he : (∫⁻ ω, fusionRootOnlyMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P) =
      ∫⁻ ω, coulombMass γ (gmcRootedMeasure γ (y * z) (M ω))
        ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ^ s ∂P := by
    apply lintegral_congr_ae
    filter_upwards [fusionRootOnlyMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z]
      with ω hω
    rw [hω]
  rw [he]
  apply hbound
  intro j
  fin_cases j
  · norm_num
  · norm_num
  · norm_num


end DOZZ.Proofs
