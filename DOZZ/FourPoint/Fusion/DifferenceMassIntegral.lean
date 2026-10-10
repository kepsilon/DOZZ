/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceKernel
public import DOZZ.FourPoint.TwoRootedDomination
/-! # Finite masses as signed real spatial integrals -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs
/-- Finite Coulomb masses give integrability and the real integral of the displayed kernel. -/
theorem fusion_gammaHalfKernel_integral (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (μ : Measure ℂ)
    (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hf : coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ≠ ⊤) :
    Integrable (gammaHalfKernel γ α₁ α₂ α₃ z) μ ∧
      (∫ x, gammaHalfKernel γ α₁ α₂ α₃ z x ∂μ) =
        (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).toReal := by
  have hm : Measurable (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)) := by
    have hp : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    exact ENNReal.measurable_ofReal.comp
      ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp (f := fun x : ℂ => (z, x)) hp)
  rw [fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z μ hz h0 h1] at hf ⊢
  have he : (fun x => (ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)).toReal) =
      gammaHalfKernel γ α₁ α₂ α₃ z := by
    funext x
    exact ENNReal.toReal_ofReal (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x)
  constructor
  · simpa only [he] using integrable_toReal_of_lintegral_ne_top hm.aemeasurable hf
  · simpa only [he] using integral_toReal hm.aemeasurable
      (ae_of_all μ fun _ => ENNReal.ofReal_lt_top)
/-- The signed kernel difference integrates to the difference of the two finite masses. -/
theorem fusion_difference_mass_integral (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (μ : Measure ℂ)
    (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hfz : coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ≠ ⊤)
    (hf0 : coulombMass γ μ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ≠ ⊤) :
    Integrable (fusionDifferenceKernel γ α₁ α₂ α₃ z) μ ∧
      (∫ x, fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂μ) =
        (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).toReal -
        (coulombMass γ μ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃).toReal := by
  obtain ⟨hiz, hez⟩ := fusion_gammaHalfKernel_integral γ α₁ α₂ α₃ z μ hz h0 h1 hfz
  obtain ⟨hi0, he0⟩ := fusion_gammaHalfKernel_integral γ α₁ α₂ α₃ 0 μ h0 h0 h1 hf0
  exact ⟨hiz.sub hi0, by simp only [fusionDifferenceKernel, integral_sub hiz hi0, hez, he0]⟩
end DOZZ.Proofs
