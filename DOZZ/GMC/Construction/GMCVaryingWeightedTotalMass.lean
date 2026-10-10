/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCWeightedTotalMass

/-! Uniformly varying weights give close cutoff total masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem weightedTotal_eq_integral_local
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
  have hWlt : ∀ᵐ z ∂μ, W z < ∞ := ae_of_all _ (fun z => ENNReal.ofReal_lt_top)
  have hInt := integral_withDensity_eq_integral_toReal_smul hW hWlt
    (1 : BoundedContinuousFunction ℂ ℝ)
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

/-- The total masses obtained from a uniformly convergent family of nonnegative BCF weights
become close in probability at the same GMC cutoff. -/
theorem regularizedGMC_varyingWithDensity_univ_mass_diff_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop) :
    TendstoInMeasure P
      (fun r ω =>
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)
      atTop (fun _ => 0) := by
  let μ : ℝ → Ω → Measure ℂ := fun r ω => regularizedGMC P Xc γ r ω
  let diff : ℝ → ℂ → ℝ := fun r z => |u r z - v z|
  let gap : ℝ → Ω → ℝ≥0∞ := fun r ω =>
    ∫⁻ z, ENNReal.ofReal (diff r z) ∂μ r ω
  let refMass : ℝ≥0∞ := gmcReferenceMeasure Set.univ
  have hμMeas (r : ℝ) : Measurable (μ r) :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  have hdiffMeas (r : ℝ) : Measurable (fun z : ℂ => ENNReal.ofReal (diff r z)) := by
    exact ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp ((u r).continuous.measurable.sub v.continuous.measurable))
  have hgapMeas (r : ℝ) : Measurable (gap r) :=
    (Measure.measurable_lintegral (hdiffMeas r)).comp (hμMeas r)
  have hdiffBound (r : ℝ) (z : ℂ) : diff r z ≤ ‖u r - v‖ := by
    dsimp [diff]
    calc
      |u r z - v z| = ‖(u r - v) z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u r - v‖ := (u r - v).norm_coe_le_norm z
  have hnorm : Tendsto (fun r : ℝ => ‖u r - v‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have huni := (Metric.tendstoUniformly_iff.mp hconv) (ε / 2) (by linarith)
    filter_upwards [huni] with r hr
    have hle : ‖u r - v‖ ≤ ε / 2 := by
      apply (BoundedContinuousFunction.norm_le (by linarith)).2
      intro z
      have hz := hr z
      rw [Real.norm_eq_abs]
      have hz' : |u r z - v z| < ε / 2 := by
        simpa [Real.dist_eq, abs_sub_comm] using hz
      exact le_of_lt hz'
    have hstrict : ε / 2 < ε := by linarith
    have hle' : ‖u r - v‖ < ε := lt_of_le_of_lt hle hstrict
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hle'
  have hgapExpectation (r : ℝ) :
      ∫⁻ ω, gap r ω ∂P = ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure := by
    dsimp [gap, diff, μ]
    exact regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
      (fun z => ENNReal.ofReal |u r z - v z|) (hdiffMeas r)
  have hgapBound (r : ℝ) :
      ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure ≤
        ENNReal.ofReal ‖u r - v‖ * refMass := by
    calc
      ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure ≤
          ∫⁻ z, ENNReal.ofReal ‖u r - v‖ ∂gmcReferenceMeasure := by
            apply lintegral_mono
            intro z
            exact ENNReal.ofReal_le_ofReal (hdiffBound r z)
      _ = ENNReal.ofReal ‖u r - v‖ * refMass := by rw [lintegral_const]
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let den : ℝ≥0∞ := ENNReal.ofReal ε
  have hden0 : den ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hdenTop : den ≠ ∞ := ENNReal.ofReal_ne_top
  have hrefTop : refMass ≠ ∞ := by simpa [refMass] using gmcReferenceMeasure_univ_ne_top
  have hprobT : Tendsto (fun r : ℝ =>
      (ENNReal.ofReal ‖u r - v‖ * refMass) / den) atTop (𝓝 0) := by
    have hOf : Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖) atTop
        (𝓝 (ENNReal.ofReal 0)) := (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
    have hmul' := ((ENNReal.continuous_mul_const hrefTop).tendsto
      (ENNReal.ofReal 0)).comp hOf
    change Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass) atTop
      (𝓝 (ENNReal.ofReal 0 * refMass)) at hmul'
    have hmul : Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass)
        atTop (𝓝 0) := by simpa using hmul'
    have hdiv := (ENNReal.continuous_div_const den hden0).tendsto 0
    have hdiv' := hdiv.comp hmul
    change Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass / den) atTop
      (𝓝 (0 / den)) at hdiv'
    simpa [zero_div] using hdiv'
  have hεevent (r : ℝ) : P {ω | ε ≤ |(
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)|} ≤
      (ENNReal.ofReal ‖u r - v‖ * refMass) / den := by
    have hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (μ r ω) := by
      have hmass : ∫⁻ ω, (μ r ω) Set.univ ∂P = gmcReferenceMeasure Set.univ := by
        dsimp [μ]
        simpa using regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
          (fun _ : ℂ => (1 : ℝ≥0∞)) measurable_const
      have htotalMeas : Measurable (fun ω => (μ r ω) Set.univ) :=
        (Measure.measurable_coe MeasurableSet.univ).comp (hμMeas r)
      have href : gmcReferenceMeasure Set.univ ≠ ∞ := gmcReferenceMeasure_univ_ne_top
      filter_upwards [ae_lt_top htotalMeas (by rw [hmass]; exact href)] with ω hω
      exact ⟨hω⟩
    have hsub : ∀ᵐ ω ∂P,
        ε ≤ |(((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
            (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal| →
          ENNReal.ofReal ε ≤ gap r ω := by
      filter_upwards [hfinite] with ω hμfin hω
      have hmassU := weightedTotal_eq_integral_local (μ r ω) hμfin (u r) (hu r)
      have hmassV := weightedTotal_eq_integral_local (μ r ω) hμfin v hv
      have hmemU : MemLp (u r) 1 (μ r ω) :=
        @MemLp.of_bound ℂ ℝ _ 1 (μ r ω) _ hμfin (u r)
          (u r).continuous.measurable.aestronglyMeasurable ‖u r‖
          (ae_of_all _ fun z => (u r).norm_coe_le_norm z)
      have hmemV : MemLp v 1 (μ r ω) :=
        @MemLp.of_bound ℂ ℝ _ 1 (μ r ω) _ hμfin v
          v.continuous.measurable.aestronglyMeasurable ‖v‖
          (ae_of_all _ fun z => v.norm_coe_le_norm z)
      have hdist := dist_integral_le_lintegral_edist
        (hmemU.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
        (hmemV.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
      have hmassEq :
          (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
            (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal =
          ∫ z, u r z ∂μ r ω - ∫ z, v z ∂μ r ω := by rw [hmassU, hmassV]
      rw [hmassEq] at hω
      have hgapEdist : ∫⁻ z, edist (u r z) (v z) ∂μ r ω = gap r ω := by
        apply lintegral_congr
        intro z
        simp [diff, edist_dist, Real.dist_eq]
      have hgapTop : gap r ω ≠ ∞ := by
        apply ne_of_lt
        calc
          gap r ω ≤ ∫⁻ z, ENNReal.ofReal ‖u r - v‖ ∂μ r ω := by
            apply lintegral_mono
            intro z
            exact ENNReal.ofReal_le_ofReal (hdiffBound r z)
          _ < ∞ := by
            rw [lintegral_const]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ (μ r ω) hμfin Set.univ))
      have hdist2 : dist (∫ z, u r z ∂μ r ω) (∫ z, v z ∂μ r ω) ≤
          (gap r ω).toReal := by
        calc
          dist (∫ z, u r z ∂μ r ω) (∫ z, v z ∂μ r ω) ≤
              (∫⁻ z, edist (u r z) (v z) ∂μ r ω).toReal := hdist
          _ = (gap r ω).toReal := by rw [hgapEdist]
      have hdist' : |(∫ z, u r z ∂μ r ω) - ∫ z, v z ∂μ r ω| ≤
          (gap r ω).toReal := by simpa [Real.dist_eq] using hdist2
      have hεgap : ε ≤ (gap r ω).toReal := hω.trans hdist'
      exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 hεgap
    have hmarkov : P {ω | ENNReal.ofReal ε ≤ gap r ω} ≤
        (∫⁻ ω, gap r ω ∂P) / den := by
      apply meas_ge_le_lintegral_div (hgapMeas r).aemeasurable
      · exact hden0
      · exact hdenTop
    calc
      P {ω | ε ≤ |(
          (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
          (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)|} ≤
          P {ω | ENNReal.ofReal ε ≤ gap r ω} := measure_mono_ae hsub
      _ ≤ (∫⁻ ω, gap r ω ∂P) / den := hmarkov
      _ = (∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure) / den := by
          rw [hgapExpectation]
      _ ≤ (ENNReal.ofReal ‖u r - v‖ * refMass) / den := by
          exact ENNReal.div_le_div_right (hgapBound r) den
  have hprob : Tendsto (fun r : ℝ => P {ω | ε ≤ |(
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)|})
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hprobT
    · exact Filter.Eventually.of_forall (fun r => bot_le)
    · exact Filter.Eventually.of_forall hεevent
  simpa [μ, Real.norm_eq_abs] using hprob

end DOZZ.Proofs
