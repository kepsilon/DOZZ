/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InverseInterpolationFubini
public import DOZZ.FourPoint.Fusion.DifferenceMassIntegral
public import DOZZ.FourPoint.Fusion.MassSegment
public import DOZZ.FourPoint.Fusion.MassPositiveFinite
/-! # Signed interpolation of the actual GMC inverse expectations -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- The two finite GMC inverse expectations differ by the signed segment integral. -/
theorem fusion_mass_expectation_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (p : ℝ) (hp : 0 ≤ p) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p) ∂P).toReal -
      (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal =
      -p * ∫ t in Icc (0 : ℝ) 1, ∫ ω,
        (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
          (∫ x, fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P := by
  let _ : IsProbabilityMeasure P := hX.1
  let a := fun ω => coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃
  let b := fun ω => coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃
  have ha := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃
  have hb := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃
  have hap := fusion_zeroMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃
  have hbp := fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4
  obtain ⟨C, _, hbound⟩ := coulomb_inverse_moment_uniform_roots P X hX γ hγ hγ2 M hM ![-γ / 2, α₁, α₂] α₃ p hp
  have hav : ∀ j : Fin 3, ‖(![0, 0, 1] : Fin 3 → ℂ) j‖ ≤ 1 := by intro j; fin_cases j <;> simp
  have hbv : ∀ j : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) j‖ ≤ 1 := by
    intro j; fin_cases j
    · change ‖z‖ ≤ 1; linarith
    · simp
    · simp
  have hat : (∫⁻ ω, a ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound _ hav)
  have hbt : (∫⁻ ω, b ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound _ hbv)
  have hai : Integrable (fun ω => (a ω).toReal ^ (-p)) P := by
    simpa only [ENNReal.toReal_rpow] using integrable_toReal_of_lintegral_ne_top (ha.pow_const _) hat
  have hbi : Integrable (fun ω => (b ω).toReal ^ (-p)) P := by
    simpa only [ENNReal.toReal_rpow] using integrable_toReal_of_lintegral_ne_top (hb.pow_const _) hbt
  have hpos : ∀ᵐ ω ∂P, 0 < (a ω).toReal ∧ 0 < (b ω).toReal := by
    filter_upwards [hap, hbp] with ω haω hbω
    exact ⟨ENNReal.toReal_pos haω.1 haω.2, ENNReal.toReal_pos hbω.1 hbω.2⟩
  have hi := fusion_inverse_expectation_interpolation P (fun ω => (a ω).toReal) (fun ω => (b ω).toReal) p
    ha.ennreal_toReal.aestronglyMeasurable hb.ennreal_toReal.aestronglyMeasurable hpos hai hbi
  have hea : (∫ ω, (a ω).toReal ^ (-p) ∂P) = (∫⁻ ω, a ω ^ (-p) ∂P).toReal := by
    simpa only [ENNReal.toReal_rpow] using integral_toReal (ha.pow_const _) (ae_lt_top' (ha.pow_const _) hat)
  have heb : (∫ ω, (b ω).toReal ^ (-p) ∂P) = (∫⁻ ω, b ω ^ (-p) ∂P).toReal := by
    simpa only [ENNReal.toReal_rpow] using integral_toReal (hb.pow_const _) (ae_lt_top' (hb.pow_const _) hbt)
  rw [hea, heb] at hi
  rw [hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hap, hbp,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω haω hbω hωz hω0 hω1
  have hd := (fusion_difference_mass_integral γ α₁ α₂ α₃ z (M ω) hωz hω0 hω1 hbω.2 haω.2).2
  have he : (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω)).toReal =
      t * (b ω).toReal + (1 - t) * (a ω).toReal := by
    rw [fusionUnrootedSegment, ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbω.2)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top haω.2)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)]
    rfl
  rw [← ENNReal.toReal_rpow, he, hd]
  change -p * ((b ω).toReal - (a ω).toReal) * _ = -p * (_ * ((b ω).toReal - (a ω).toReal))
  ring
end DOZZ.Proofs
