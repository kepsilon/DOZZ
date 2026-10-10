/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.RhoCoulomb
public import DOZZ.GMC.SharpMoments.SeibergMoment
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- The three-root DKRV moment on the full extended Seiberg domain. -/
theorem equatorGFF_extendedSeiberg_rho_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    0 < (∫⁻ ω,
      ENNReal.rpow (rho γ (M ω) α₁ α₂ α₃)
        (-sExp γ α₁ α₂ α₃) ∂P) ∧
      (∫⁻ ω,
        ENNReal.rpow (rho γ (M ω) α₁ α₂ α₃)
          (-sExp γ α₁ α₂ α₃) ∂P) < ⊤ := by
  obtain ⟨hz, ha, hai, _he, hb, hi, hii⟩ :=
    extendedSeiberg3_coulomb_parameters γ α₁ α₂ α₃ hα
  rw [rho_moment_eq_coulomb_moment P X hX γ hγ hγ2 M hM α₁ α₂ α₃]
  exact equatorGFF_extendedSeiberg_moment P X hX γ hγ hγ2 M hM
    ![0, 1] hz ![α₁, α₂] α₃ ha hai hb hi hii
end DOZZ.Proofs
