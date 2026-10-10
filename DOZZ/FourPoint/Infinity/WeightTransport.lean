/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.GMC.EquatorGFFGMCInversionLaw
public import DOZZ.GMC.Moments.InfinityChart
public import DOZZ.ShiftEquations.Mobius.InversionMoment
@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The finite three-point chart weight, with its identically-one infinity factor removed. -/
noncomputable def infinityFiniteWeight (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (normPlus x / ‖x‖)) ^ (γ * α₁) *
    (ENNReal.ofReal (normPlus x / ‖x - 1‖)) ^ (γ * α₂) *
    (ENNReal.ofReal (normPlus x / ‖x - z‖)) ^ (γ * α₃)

/-- The inverted chart has roots `v, 1` and the first charge at infinity. -/
noncomputable def infinityChartWeight (γ α₁ α₂ α₃ : ℝ) (v x : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (normPlus x / ‖x - v‖)) ^ (γ * α₃) *
    (ENNReal.ofReal (normPlus x / ‖x - 1‖)) ^ (γ * α₂) *
    (ENNReal.ofReal (normPlus x)) ^ (γ * α₁)

theorem infinityFiniteWeight_measurable (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    Measurable (infinityFiniteWeight γ α₁ α₂ α₃ z) := by
  unfold infinityFiniteWeight normPlus
  fun_prop

/-- Exact inversion of the finite weight, outside the three chart poles. -/
theorem infinityFiniteWeight_inv (γ α₁ α₂ α₃ : ℝ) (z y : ℂ)
    (hz : z ≠ 0) (hy : y ≠ 0) (hy1 : y ≠ 1) (hyz : y ≠ z⁻¹) :
    infinityFiniteWeight γ α₁ α₂ α₃ z y⁻¹ =
      (ENNReal.ofReal ‖z‖) ^ (-(γ * α₃)) * infinityChartWeight γ α₁ α₂ α₃ z⁻¹ y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : 0 < ‖y - z⁻¹‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
  have h0 : normPlus y⁻¹ / ‖y⁻¹‖ = normPlus y := by
    rw [normPlus_inv_identity hy, norm_inv]
    field_simp
  have h1 : normPlus y⁻¹ / ‖y⁻¹ - 1‖ = normPlus y / ‖y - 1‖ := by
    rw [inversion_root_weight_base (z := 1) hy (by simpa only [one_mul] using sub_ne_zero.mpr hy1.symm), one_mul, norm_sub_rev]
  have hdiff : ‖1 - z * y‖ = ‖z‖ * ‖y - z⁻¹‖ := by
    rw [show 1 - z * y = -z * (y - z⁻¹) by field_simp [hz]; ring,
      norm_mul, norm_neg]
  have hzbase : normPlus y⁻¹ / ‖y⁻¹ - z‖ =
      ‖z‖⁻¹ * (normPlus y / ‖y - z⁻¹‖) := by
    rw [normPlus_inv_identity hy, inversion_distance hy, hdiff]
    field_simp
  have hpow : (ENNReal.ofReal (‖z‖⁻¹ * (normPlus y / ‖y - z⁻¹‖))) ^ (γ * α₃) =
      (ENNReal.ofReal ‖z‖) ^ (-(γ * α₃)) *
        (ENNReal.ofReal (normPlus y / ‖y - z⁻¹‖)) ^ (γ * α₃) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hzn.le),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.ofReal_inv_of_pos hzn, ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  rw [infinityFiniteWeight, h0, h1, hzbase, hpow, infinityChartWeight]
  ac_rfl

/-- Integrating the inversion identity requires only atomlessness at the chart poles. -/
theorem infinity_coulombMass_map_inv (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (hz : z ≠ 0)
    (m : Measure ℂ) (h0 : m {0} = 0) (h1 : m {1} = 0) (hv : m {z⁻¹} = 0) :
    coulombMass γ (m.map (fun x : ℂ => x⁻¹)) ![α₁, α₂, α₃] ![0, 1, z] 0 =
      (ENNReal.ofReal ‖z‖) ^ (-(γ * α₃)) *
        coulombMass γ m ![α₃, α₂] ![z⁻¹, 1] α₁ := by
  have hfinite : coulombMass γ (m.map (fun x : ℂ => x⁻¹)) ![α₁, α₂, α₃] ![0, 1, z] 0 =
      ∫⁻ x, infinityFiniteWeight γ α₁ α₂ α₃ z x ∂m.map (fun x : ℂ => x⁻¹) := by
    simp [coulombMass, Fin.prod_univ_three, infinityFiniteWeight]
  have hchart : coulombMass γ m ![α₃, α₂] ![z⁻¹, 1] α₁ =
      ∫⁻ x, infinityChartWeight γ α₁ α₂ α₃ z⁻¹ x ∂m := by
    simp [coulombMass, Fin.prod_univ_two, infinityChartWeight]
  rw [hfinite, hchart, lintegral_map (infinityFiniteWeight_measurable γ α₁ α₂ α₃ z)
    measurable_inv, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hz)).ne'
        ENNReal.ofReal_ne_top)]
  apply lintegral_congr_ae
  have hnull : m ({0} ∪ {1} ∪ {z⁻¹}) = 0 := measure_union_null (measure_union_null h0 h1) hv
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  simp only [mem_union, mem_singleton_iff, not_or] at hy
  exact infinityFiniteWeight_inv γ α₁ α₂ α₃ z y hz hy.1.1 hy.1.2 hy.2

/-- The inversion law `equatorGFF_GMC_inversion_law` transports the actual moment, including its
scalar factor. -/
theorem infinity_finite_moment_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (z : ℂ) (hz : z ≠ 0) (p : ℝ) :
    ∫⁻ ω, (coulombMass γ (M ω) ![α₁, α₂, α₃] ![0, 1, z] 0) ^ p ∂P =
      (ENNReal.ofReal ‖z‖) ^ (-(γ * α₃) * p) *
        ∫⁻ ω, (coulombMass γ (M ω) ![α₃, α₂] ![z⁻¹, 1] α₁) ^ p ∂P := by
  let c : ℝ≥0∞ := (ENNReal.ofReal ‖z‖) ^ (-(γ * α₃))
  have hc0 : c ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hz)) ENNReal.ofReal_ne_top).ne'
  have hct : c ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hz)).ne' ENNReal.ofReal_ne_top
  have hH : Measurable (fun m : Measure ℂ =>
      (coulombMass γ m ![α₁, α₂, α₃] ![0, 1, z] 0) ^ p) := by
    apply Measurable.pow_const
    apply Measure.measurable_lintegral
    exact measurable_inversionMoment_weight γ ![α₁, α₂, α₃] ![0, 1, z] 0
  rw [← equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM _ hH]
  have he : (∫⁻ ω,
      (coulombMass γ ((M ω).map (fun x : ℂ => x⁻¹)) ![α₁, α₂, α₃] ![0, 1, z] 0) ^ p ∂P) =
      ∫⁻ ω, c ^ p * (coulombMass γ (M ω) ![α₃, α₂] ![z⁻¹, 1] α₁) ^ p ∂P := by
    apply lintegral_congr_ae
    filter_upwards [gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0,
      gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 1,
      gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM z⁻¹] with ω h0 h1 hv
    rw [infinity_coulombMass_map_inv γ α₁ α₂ α₃ z hz (M ω) h0 h1 hv]
    exact inversionMoment_mul_rpow hc0 hct _ p
  rw [he, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hct)]
  dsimp only [c]
  rw [ENNReal.rpow_mul]

end DOZZ.Proofs
