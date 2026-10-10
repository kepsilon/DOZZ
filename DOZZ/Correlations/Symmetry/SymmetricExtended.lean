/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionMomentSwap
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Extended-domain permutation symmetry, with affine re-pinning and correlated Gaussian tilt
for the first--second swap, and the inversion law `DOZZ.equatorGFF_GMC_inversion_law` for the
first--third swap. -/
theorem unitVolumeStructureConstant_symmetric_extended
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₂ α₁ α₃ ∧
      unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₁ α₃ α₂ ∧
      unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₃ α₂ α₁ := by
  rcases hα with ⟨_, _, _, _⟩
  have h12 := unitVolumeStructureConstant_swap12 P X M γ α₁ α₂ α₃ hγ hγ2 hX hM
  have h13 := unitVolumeStructureConstant_swap13 P X M γ α₁ α₂ α₃ hγ hγ2 hX hM
  refine ⟨h12, ?_, h13⟩
  exact h13.trans ((unitVolumeStructureConstant_swap12 P X M γ α₃ α₂ α₁ hγ hγ2 hX hM).trans
    (unitVolumeStructureConstant_swap13 P X M γ α₂ α₃ α₁ hγ hγ2 hX hM))

end DOZZ.Proofs
