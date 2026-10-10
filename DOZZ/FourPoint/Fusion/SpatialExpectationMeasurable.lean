/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MeasurableIntegralFamily
public import DOZZ.FourPoint.Fusion.MovingMass
import Mathlib.MeasureTheory.Integral.Prod
import DOZZ.GMC.Annulus.BallCover
import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # Jointly measurable unrooted spatial expectations -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The literal signed spatial expectation is measurable in the moving point. The singular
values at the deterministic insertions disappear using the atomlessness theorem
`gmc_singleton_mass_eq_zero_ae`. -/
theorem fusion_gammaHalf_spatial_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (H : ℂ × ℂ → ℂ) (hH : Measurable H) :
    Measurable (fun z : ℂ => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
        (∫ x, H (z, x) ∂M ω) ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hfN, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  let I := fun q : ℂ × Ω => ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ q.1 x) ∂N q.2
  have hIm : Measurable I := by
    apply measurable_lintegral_finite_family (fun q : ℂ × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hfN q.2)
      (fun q : (ℂ × Ω) × ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ q.1.1 q.2))
    have hp : Measurable (fun q : (ℂ × Ω) × ℂ => (q.1.1, q.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp
      ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp hp)
  have hHm : Measurable (fun q : ℂ × Ω => ∫ x, H (q.1, x) ∂N q.2) := by
    apply fusion_measurable_integral_finite_family (fun q : ℂ × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hfN q.2)
      (fun q : (ℂ × Ω) × ℂ => H (q.1.1, q.2))
    have hp : Measurable (fun q : (ℂ × Ω) × ℂ => (q.1.1, q.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    simpa only [Function.comp_def] using hH.comp hp
  have hFn : Measurable (fun z : ℂ => ∫ ω, ((I (z, ω) ^ s).toReal : ℂ) *
      (∫ x, H (z, x) ∂N ω) ∂P) :=
    (((Complex.measurable_ofReal.comp (hIm.pow_const s).ennreal_toReal).mul hHm).stronglyMeasurable.integral_prod_right').measurable
  have heq : (fun z : ℂ => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
        (∫ x, H (z, x) ∂M ω) ∂P) =
      (fun z : ℂ => ∫ ω, ((I (z, ω) ^ s).toReal : ℂ) *
        (∫ x, H (z, x) ∂N ω) ∂P) := by
    funext z
    apply integral_congr_ae
    filter_upwards [he, gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hω hωz hω0 hω1
    dsimp only [I]
    rw [fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z (M ω) hωz hω0 hω1, hω]
  rw [heq]
  exact hFn

end DOZZ.Proofs
