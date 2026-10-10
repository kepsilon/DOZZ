/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Roots.UnitVolumeConditional
public import DOZZ.ShiftEquations.Assembly.ResidualFactor

/-! # Unconditional DOZZ roots from the calibrated first-case residual identity

The proof of `DOZZ.unitVolume_residual_factor_eq_one` uses the first-case dual shift. The full
dual-strip statement `DOZZ.structureConstant_dual_shift_strip` is not used, and neither of the
statement modules of `DOZZ.dozz_main` and `DOZZ.dozz_unitVolume` is imported.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

theorem dozz_unitVolume (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto
      (fun a : ℝ × ℝ × ℝ =>
        ((μ : ℂ) ^ (sExp γ a.1 a.2.1 a.2.2 : ℂ) / Complex.Gamma (sExp γ a.1 a.2.1 a.2.2)) *
          dozzFormula γ μ U a.1 a.2.1 a.2.2)
      (𝓝[{a | ExtendedSeiberg3 γ a.1 a.2.1 a.2.2 ∧
              ∀ n : ℕ, sExp γ a.1 a.2.1 a.2.2 ≠ -(n : ℝ)}] (α₁, α₂, α₃))
      (𝓝 (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ)) := by
  exact dozz_unitVolume_of_residual_factor γ μ hγ hγ2 hμ α₁ α₂ α₃ hα U hU P X M hX hM
    DOZZ.Proofs.unitVolume_residual_factor_eq_one


theorem dozz_main (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃ := by
  exact dozz_main_of_residual_factor γ μ hγ hγ2 hμ α₁ α₂ α₃ hα hs U hU P X M hX hM
    DOZZ.Proofs.unitVolume_residual_factor_eq_one


end DOZZ.Proofs
