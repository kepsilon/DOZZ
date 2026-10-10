/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CommonThreshold
public import DOZZ.Correlations.Analytic.NestedWeightedMass
public import DOZZ.Correlations.Analytic.RetainedUniformLower
public import DOZZ.Correlations.Analytic.CoulombMassPositiveFinite
public import DOZZ.Correlations.Analytic.RetainedMassMoments

/-! The common-envelope threshold estimate for the actual nested Coulomb masses. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual nested Coulomb mass-power increment has the common-envelope threshold bound.
The lower envelope is one charge-independent disk mass, and the upper envelope is the full
Coulomb mass. -/
theorem coulomb_nested_increment_threshold
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (hz : Function.Injective z) (αinf A : ℝ)
    (hα : ∀ i, |α i| ≤ A) (hinf : |αinf| ≤ A)
    (ha : ∀ i, α i < Q γ) (hiinf : αinf < Q γ)
    (O₀ O₁ : Set ℂ) (h₀ : MeasurableSet O₀) (h₁ : MeasurableSet O₁) (hsub : O₀ ⊆ O₁)
    (R : ℝ) (hR : 1 ≤ R) (hzR : ∀ i, 2 * ‖z i‖ ≤ R)
    (hO : Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8) ⊆ O₀)
    (lo hi : ℝ) (p : ℂ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hlop : lo ≤ p.re - 1) (hphi : p.re ≤ hi)
    (u m q : ℝ) (hu : 0 < u) (hm : 0 < m) (hq : 1 < q) :
    let c := ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
      ENNReal.ofReal ((R + 2) ^ (-(γ * A)))
    let H := fun ω => ENNReal.ofReal
      ((c * M ω (Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8))).toReal ^ lo +
        (coulombMass γ (M ω) α z αinf).toReal ^ hi)
    (∫⁻ ω, ENNReal.ofReal
      ‖((∫⁻ x in O₁, coulombWeight γ α z αinf x ∂M ω).toReal : ℂ) ^ p -
        ((∫⁻ x in O₀, coulombWeight γ α z αinf x ∂M ω).toReal : ℂ) ^ p‖ ∂P) ≤
      ENNReal.ofReal u * ENNReal.ofReal (2 * ‖p‖) * (∫⁻ ω, H ω ∂P) +
      ((ENNReal.ofReal 2) ^ q * (∫⁻ ω, H ω ^ q ∂P)) ^ (1 / q) *
        ((∫⁻ ω, (ENNReal.ofReal
          (∫⁻ x in O₁ \ O₀, coulombWeight γ α z αinf x ∂M ω).toReal) ^ m ∂P) /
          (ENNReal.ofReal u) ^ m) ^ (1 / (q / (q - 1))) := by
  dsimp only
  let c := ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
    ENNReal.ofReal ((R + 2) ^ (-(γ * A)))
  let B := Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8)
  let L (ω : Ω) := (c * M ω B).toReal
  let Z (ω : Ω) := (∫⁻ x in O₀, coulombWeight γ α z αinf x ∂M ω).toReal
  let Y (ω : Ω) := (∫⁻ x in O₁ \ O₀, coulombWeight γ α z αinf x ∂M ω).toReal
  let U (ω : Ω) := (coulombMass γ (M ω) α z αinf).toReal
  have hc : c ≠ 0 := mul_ne_zero
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hc' : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hB := open_mass_pos_finite_ae P X hX γ hγ hγ2 M hM B
    Metric.isOpen_ball Metric.isBounded_ball (Metric.nonempty_ball.mpr (by norm_num))
  have hfull := coulomb_mass_pos_finite_ae P X hX γ hγ hγ2 M hM z hz α αinf ha hiinf
  have hLm : AEMeasurable L P := by
    have hb := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B
      Metric.isOpen_ball.measurableSet
    simpa only [L, Function.comp_def, Pi.mul_def] using
      ENNReal.measurable_toReal.comp_aemeasurable (aemeasurable_const.mul hb)
  have hUm : AEMeasurable U P := by
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf)
  have hYm : AEMeasurable Y P := by
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
        (measurable_coulombWeight γ α z αinf) _ (h₁.diff h₀))
  have hH : AEMeasurable (fun ω => ENNReal.ofReal (L ω ^ lo + U ω ^ hi)) P := by
    have ht := (hLm.pow_const lo).add (hUm.pow_const hi)
    simpa only [Function.comp_def, Pi.add_def] using
      ENNReal.measurable_ofReal.comp_aemeasurable ht
  have hLp : ∀ᵐ ω ∂P, 0 < L ω := by
    filter_upwards [hB] with ω hω
    exact ENNReal.toReal_pos (mul_ne_zero hc hω.1) (ENNReal.mul_ne_top hc' hω.2)
  have hLZ : ∀ᵐ ω ∂P, L ω ≤ Z ω := by
    filter_upwards [hfull] with ω hω
    have hf : (∫⁻ x in O₀, coulombWeight γ α z αinf x ∂M ω) ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (setLIntegral_le_lintegral _ _)
      simpa only [← coulombMass_eq_lintegral_coulombWeight] using hω.2
    exact ENNReal.toReal_mono hf
      (retained_uniform_disk_lower (M ω) γ hγ A α z αinf hα hinf O₀ R hR hzR hO)
  have hreal : ∀ᵐ ω ∂P, Z ω + Y ω =
      (∫⁻ x in O₁, coulombWeight γ α z αinf x ∂M ω).toReal ∧ Z ω + Y ω ≤ U ω := by
    filter_upwards [hfull] with ω hω
    have hf : (∫⁻ x, coulombWeight γ α z αinf x ∂M ω) ≠ ⊤ := by
      simpa only [← coulombMass_eq_lintegral_coulombWeight] using hω.2
    have he := nested_weighted_mass_real (M ω) (coulombWeight γ α z αinf)
      O₀ O₁ h₀ h₁ hsub hf
    exact ⟨he.1, he.1.le.trans (by simpa only [← coulombMass_eq_lintegral_coulombWeight] using he.2)⟩
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ‖((Z ω + Y ω : ℝ) : ℂ) ^ p - (Z ω : ℂ) ^ p‖ ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hreal] with ω hω
      rw [hω.1]
    _ ≤ _ := cpow_common_threshold P L Z Y U lo hi p hYm hH hLp hLZ
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (hreal.mono (fun _ h => h.2)) hlo hhi hlop hphi u hu m q hm hq

end DOZZ.Proofs
