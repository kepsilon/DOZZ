/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.GMC.Moments.InversionLaw
import DOZZ.GMC.Construction.GMCIntensityAdapter

/-!
# Coulomb moments under inversion

The inversion `y ↦ 1/y` preserves the law of the equator chaos
(`DOZZ.equatorGFF_GMC_inversion_law`). It maps the Coulomb weight with finite nonzero roots `zₖ` and
no charge at infinity to the weight with roots `1/zₖ`, up to the constant `∏ₖ |zₖ|^{γαₖ}`, away from
the roots and the origin. The chaos is almost surely atomless at every point (its intensity has a
density), so the Coulomb masses agree almost surely and every real power moment transforms by the
corresponding power of that constant.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- A positive finite factor commutes with every real power. -/
theorem inversionMoment_mul_rpow {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (t : ℝ≥0∞)
    (q : ℝ) : (c * t) ^ q = c ^ q * t ^ q := by
  by_cases ht : t = 0
  · subst ht
    rcases lt_trichotomy q 0 with hq | hq | hq
    · rw [mul_zero, ENNReal.zero_rpow_of_neg hq, ENNReal.mul_top]
      exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hct).ne'
    · subst hq; simp
    · rw [mul_zero, ENNReal.zero_rpow_of_pos hq, mul_zero]
  · exact ENNReal.mul_rpow_of_ne_zero hc0 ht q

/-- The equator chaos is almost surely atomless at every point. -/
theorem gmc_atomless_of_isGMCOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (x : ℂ) : ∀ᵐ ω ∂P, M ω {x} = 0 := by
  have hint := equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM {x} (measurableSet_singleton x)
  have href : gmcReferenceMeasure {x} = 0 := by
    unfold gmcReferenceMeasure
    exact withDensity_absolutelyContinuous _ _ (measure_singleton x)
  rw [href] at hint
  have hmeas : AEMeasurable (fun ω => M ω {x}) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM {x} (measurableSet_singleton x)
  exact (lintegral_eq_zero_iff' hmeas).1 hint

/-- The Coulomb weight with no charge at infinity. -/
theorem coulombWeight_inv {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : ∀ k, z k ≠ 0) {y : ℂ} (hy : y ≠ 0) (hyz : ∀ k, y ≠ z k) :
    (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus y⁻¹ / ‖y⁻¹ - (z k)⁻¹‖)) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus y⁻¹)) (γ * 0) =
      (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (γ * α k)) *
        ((∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus y / ‖y - z k‖)) (γ * α k)) *
          ENNReal.rpow (ENNReal.ofReal (normPlus y)) (γ * 0)) := by
  simp only [ENNReal.rpow_eq_pow, mul_zero, ENNReal.rpow_zero, mul_one]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hzn : 0 < ‖z k‖ := norm_pos_iff.mpr (hz k)
  have hdiff : 0 < ‖y - z k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hyz k))
  have hplus : normPlus y⁻¹ = normPlus y / ‖y‖ := by
    unfold normPlus
    rw [norm_inv, ← max_div_div_right hyn.le, div_self hyn.ne', one_div, max_comm]
  have hsub : ‖y⁻¹ - (z k)⁻¹‖ = ‖y - z k‖ / (‖y‖ * ‖z k‖) := by
    rw [inv_sub_inv hy (hz k), norm_div, norm_mul, norm_sub_rev]
  have hratio : normPlus y⁻¹ / ‖y⁻¹ - (z k)⁻¹‖ = ‖z k‖ * (normPlus y / ‖y - z k‖) := by
    rw [hplus, hsub]
    field_simp
  rw [hratio, ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top _

/-- The Coulomb weight is measurable. -/
theorem measurable_inversionMoment_weight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (w : Fin N → ℂ)
    (αinf : ℝ) :
    Measurable fun x : ℂ =>
      (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - w k‖)) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) := by
  have hplus : Measurable normPlus := by
    unfold normPlus
    exact measurable_const.max measurable_norm
  simp only [ENNReal.rpow_eq_pow]
  refine Finset.measurable_prod _ (fun k _ => ?_) |>.mul ?_
  · exact (ENNReal.measurable_ofReal.comp (hplus.div
      (measurable_id.sub_const (w k)).norm)).pow_const _
  · exact (ENNReal.measurable_ofReal.comp hplus).pow_const _

/-- **Coulomb moments under inversion.** With finite nonzero roots and no charge at infinity, every
real power moment of the Coulomb mass at the inverted roots is the moment at the original roots
times the corresponding power of `∏ₖ |zₖ|^{γαₖ}`. -/
theorem coulombMass_inv_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (hz : ∀ k, z k ≠ 0)
    (q : ℝ) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun k => (z k)⁻¹) 0) q ∂P =
      ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (γ * α k)) q *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z 0) q ∂P := by
  set c : ℝ≥0∞ := ∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (γ * α k) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro k _
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hz k)))
      ENNReal.ofReal_ne_top).ne'
  have hct : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.prod_ne_top fun k _ => ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hz k))).ne' ENNReal.ofReal_ne_top
  have hF := measurable_inversionMoment_weight γ α (fun k => (z k)⁻¹) 0
  have hH : Measurable fun μ : Measure ℂ =>
      ENNReal.rpow (∫⁻ x, (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - (z k)⁻¹‖))
        (γ * α k)) * ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * 0) ∂μ) q :=
    (Measure.measurable_lintegral hF).pow_const q
  have hlaw := equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM _ hH
  -- almost surely no atom at the origin or at any root
  have hatoms : ∀ᵐ ω ∂P, M ω {0} = 0 ∧ ∀ k, M ω {z k} = 0 := by
    have h0 := gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0
    have hk : ∀ᵐ ω ∂P, ∀ k, M ω {z k} = 0 :=
      ae_all_iff.2 fun k => gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM (z k)
    filter_upwards [h0, hk] with ω h1 h2 using ⟨h1, h2⟩
  have hinner : ∀ᵐ ω ∂P,
      (∫⁻ x, (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - (z k)⁻¹‖)) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * 0) ∂(M ω).map (fun x => x⁻¹)) =
        c * coulombMass γ (M ω) α z 0 := by
    filter_upwards [hatoms] with ω hω
    rw [lintegral_map hF measurable_inv, coulombMass, ← lintegral_const_mul' _ _ hct]
    apply lintegral_congr_ae
    have hnull : (M ω) ({0} ∪ ⋃ k, {z k}) = 0 :=
      measure_union_null hω.1 (measure_iUnion_null hω.2)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, not_or, not_exists] at hy
    exact coulombWeight_inv γ α z hz hy.1 fun k h => hy.2 k h
  calc
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun k => (z k)⁻¹) 0) q ∂P
        = ∫⁻ ω, ENNReal.rpow (∫⁻ x, (∏ k, ENNReal.rpow (ENNReal.ofReal
            (normPlus x / ‖x - (z k)⁻¹‖)) (γ * α k)) *
              ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * 0) ∂M ω) q ∂P := by
      congr 1
    _ = ∫⁻ ω, ENNReal.rpow (c * coulombMass γ (M ω) α z 0) q ∂P := by
      rw [← hlaw]
      apply lintegral_congr_ae
      filter_upwards [hinner] with ω hω
      rw [hω]
    _ = ∫⁻ ω, ENNReal.rpow c q * ENNReal.rpow (coulombMass γ (M ω) α z 0) q ∂P := by
      congr 1
      funext ω
      exact inversionMoment_mul_rpow hc0 hct _ q
    _ = ENNReal.rpow c q * ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z 0) q ∂P :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hct)

end DOZZ.Proofs

end
