/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCWeightedBoxMassVarying
public import DOZZ.GMC.Construction.GMCUniqueAe
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! Convergence of weighted cutoff total masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem weightedTotal_eq_integral
    (μ : Measure ℂ) (hμ : IsFiniteMeasure μ)
    (w : BoundedContinuousFunction ℂ ℝ) (hw : ∀ z, 0 ≤ w z) :
    ((μ.withDensity (fun z => ENNReal.ofReal (w z))) Set.univ).toReal =
      ∫ z, w z ∂μ := by
  let W : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (w z)
  have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hWbound : ∀ z, W z ≤ ENNReal.ofReal ‖w‖ := by
    intro z
    apply ENNReal.ofReal_le_ofReal
    calc
      w z = |w z| := (abs_of_nonneg (hw z)).symm
      _ = ‖w z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖w‖ := w.norm_coe_le_norm z
  have hWint : ∫⁻ z, W z ∂μ ≠ ∞ := by
    apply ne_of_lt
    calc
      ∫⁻ z, W z ∂μ ≤ ∫⁻ z, ENNReal.ofReal ‖w‖ ∂μ := lintegral_mono hWbound
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ μ hμ Set.univ))
  have hWfinite : IsFiniteMeasure (μ.withDensity W) := isFiniteMeasure_withDensity hWint
  have hconst : ∫ z, (1 : BoundedContinuousFunction ℂ ℝ) z ∂μ.withDensity W =
      ((μ.withDensity W) Set.univ).toReal := by
    let _ : IsFiniteMeasure (μ.withDensity W) := hWfinite
    rw [← Measure.real_def]
    simp [integral_const]
  have hInt := integral_withDensity_eq_integral_toReal_smul hW hWlt (1 : BoundedContinuousFunction ℂ ℝ)
  have hInt' : ∫ z, (1 : BoundedContinuousFunction ℂ ℝ) z ∂μ.withDensity W =
      ∫ z, w z ∂μ := by
    rw [hInt]
    apply integral_congr_ae
    filter_upwards [] with z
    simp [W, ENNReal.toReal_ofReal (hw z), smul_eq_mul]
  calc
    ((μ.withDensity W) Set.univ).toReal =
        ∫ z, (1 : BoundedContinuousFunction ℂ ℝ) z ∂μ.withDensity W := hconst.symm
    _ = ∫ z, w z ∂μ := hInt'
where
  hWlt : ∀ᵐ z ∂μ, ENNReal.ofReal (w z) < ∞ := ae_of_all _ (fun z => ENNReal.ofReal_lt_top)

/-- A fixed nonnegative bounded-continuous weight gives convergence of the weighted total
cutoff mass for every `IsGMCOf` limit. -/
theorem regularizedGMC_withDensity_univ_mass_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (w : BoundedContinuousFunction ℂ ℝ) (hw : ∀ z, 0 ≤ w z) :
    TendstoInMeasure P
      (fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (w z))) Set.univ).toReal) atTop
      (fun ω => ((M ω).withDensity
        (fun z => ENNReal.ofReal (w z)) Set.univ).toReal) := by
  obtain ⟨Yc, hYc, hYlim⟩ := hM.2
  have hTest : TendstoInMeasure P
      (fun r ω => ∫ z, w z ∂regularizedGMC P Xc γ r ω) atTop
      (fun ω => ∫ z, w z ∂M ω) := by
    have hcut (r : ℝ) :
        (fun ω => ∫ z, w z ∂regularizedGMC P Xc γ r ω) =ᵐ[P]
          fun ω => ∫ z, w z ∂regularizedGMC P Yc γ r ω := by
      filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX Xc Yc hXc hYc γ r]
        with ω hω
      rw [hω]
    exact TendstoInMeasure.congr (fun r => (hcut r).symm)
      (Filter.Eventually.of_forall fun _ => rfl) (hYlim w)
  have hleft (r : ℝ) :
      (fun ω => (((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (w z))) Set.univ).toReal) =ᵐ[P]
        fun ω => ∫ z, w z ∂regularizedGMC P Xc γ r ω := by
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
    exact weightedTotal_eq_integral (regularizedGMC P Xc γ r ω) hω w hw
  have hright :
      (fun ω => ((M ω).withDensity (fun z => ENNReal.ofReal (w z)) Set.univ).toReal) =ᵐ[P]
        fun ω => ∫ z, w z ∂M ω := by
    exact ae_of_all P (fun ω => weightedTotal_eq_integral (M ω) (hM.1 ω) w hw)
  exact TendstoInMeasure.congr (fun r => (hleft r).symm) hright.symm hTest

end DOZZ.Proofs
