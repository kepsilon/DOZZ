/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseUniform
public import DOZZ.GMC.SharpMoments.GluedFieldGaussian
public import DOZZ.GMC.SharpMoments.LaplaceProduct
public import DOZZ.GMC.FieldChaosNegativePower

/-! # The two-branch inequality and cutoff-uniform inverse moments

On the two separated subdisks `D₁, D₂` of the reference disk, the circle covariance is bounded by
the constant `invSepConst`. Kahane's Laplace comparison between the circle field on `D₁ ∪ D₂` and
the glued field (independent copies on `D₁` and `D₂` plus a common Gaussian scalar of variance
`invSepConst`) gives the two-branch inequality: the reference Laplace transform is at most the
Gaussian average of the product of the two subdisk transforms. With `InverseUniform` this proves
every inverse moment of the cutoff reference mass, uniformly in the cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The covariance bound across the two subdisks. -/
noncomputable def invSepConst : ℝ≥0 :=
  ⟨Real.log 16 + (Real.log 3 + 2 * Real.log (1 + 1 / 8)), by
    have h1 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ Real.log (1 + 1 / 8) := Real.log_nonneg (by norm_num)
    linarith⟩

theorem invSepConst_pos : 0 < invSepConst := by
  rw [← NNReal.coe_pos]
  change 0 < Real.log 16 + (Real.log 3 + 2 * Real.log (1 + 1 / 8))
  have h1 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have h2 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log (1 + 1 / 8) := Real.log_nonneg (by norm_num)
  linarith

theorem norm_le_of_mem_invSub {b x : ℂ} (hb : ‖b‖ = 1 / 16)
    (hx : x ∈ Metric.ball b (1 / 4 * (1 / 8))) : ‖x‖ ≤ 1 / 8 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have := norm_le_norm_add_norm_sub' x b
  calc ‖x‖ ≤ ‖b‖ + ‖x - b‖ := by
        have h := norm_add_le b (x - b)
        rwa [add_sub_cancel] at h
    _ ≤ 1 / 8 := by rw [hb]; linarith

theorem invSub_sep {x y : ℂ} (hx : x ∈ Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
    (hy : y ∈ Metric.ball invSubCenterRight (1 / 4 * (1 / 8))) : 1 / 16 ≤ ‖x - y‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hx hy
  have hc : ‖invSubCenterLeft - invSubCenterRight‖ = 1 / 8 := by
    rw [invSubCenterLeft, invSubCenterRight, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  have h := norm_sub_le_norm_sub_add_norm_sub invSubCenterLeft x y
  have h' := norm_sub_le_norm_sub_add_norm_sub x y invSubCenterRight
  have hxl : ‖invSubCenterLeft - x‖ = ‖x - invSubCenterLeft‖ := norm_sub_rev _ _
  have hlr := norm_sub_le_norm_sub_add_norm_sub invSubCenterLeft y invSubCenterRight
  linarith

theorem invSub_disjoint :
    Disjoint (Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
      (Metric.ball invSubCenterRight (1 / 4 * (1 / 8))) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have := invSub_sep hx hx'
  simp at this
  linarith

/-- The circle covariance between the two subdisks is at most `invSepConst`. -/
theorem circleField_covariance_le_invSepConst
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) (hr : 0 ≤ r) {x y : ℂ}
    (hx : x ∈ Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
    (hy : y ∈ Metric.ball invSubCenterRight (1 / 4 * (1 / 8))) :
    ∫ ω, Xc ω x r * Xc ω y r ∂P ≤ (invSepConst : ℝ) := by
  have h := circleField_covariance_le_log P X hX Xc hXc (1 / 8) r (by norm_num) hr x y
    (norm_le_of_mem_invSub norm_invSubCenterLeft hx)
    (norm_le_of_mem_invSub norm_invSubCenterRight hy)
  have hsep := invSub_sep hx hy
  have hmax : 1 / 16 ≤ max ‖x - y‖ (Real.exp (-r)) := le_max_of_le_left hsep
  have hlog : Real.log (1 / max ‖x - y‖ (Real.exp (-r))) ≤ Real.log 16 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by linarith)]
    linarith
  change _ ≤ Real.log 16 + (Real.log 3 + 2 * Real.log (1 + 1 / 8))
  linarith

theorem norm_lt_of_mem_invSub {b x : ℂ} (hb : ‖b‖ = 1 / 16)
    (hx : x ∈ Metric.ball b (1 / 4 * (1 / 8))) : ‖x‖ < 1 / 8 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  calc ‖x‖ ≤ ‖b‖ + ‖x - b‖ := by
        have h := norm_add_le b (x - b)
        rwa [add_sub_cancel] at h
    _ < 1 / 8 := by rw [hb]; linarith

/-- The two-branch inequality at every cutoff: Kahane's Laplace comparison with two independent
copies of the circle field on the subdisks and a common scalar of variance `invSepConst`. -/
theorem cutoffLaplace_twoBranch
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (hr : 0 ≤ r) (x : ℝ) :
    cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤
      ∫ ξ, cutoffLaplace P Xc γ r (Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
          (x + γ * ξ - γ ^ 2 * invSepConst / 2) *
        cutoffLaplace P Xc γ r (Metric.ball invSubCenterRight (1 / 4 * (1 / 8)))
          (x + γ * ξ - γ ^ 2 * invSepConst / 2) ∂gaussianReal 0 invSepConst := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  set C : ℝ≥0 := invSepConst with hCdef
  set D : Set ℂ := Metric.ball (0 : ℂ) (1 / 8) with hDdef
  set D₁ : Set ℂ := Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)) with hD₁def
  set D₂ : Set ℂ := Metric.ball invSubCenterRight (1 / 4 * (1 / 8)) with hD₂def
  set U : Set ℂ := D₁ ∪ D₂ with hUdef
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hD₁ : MeasurableSet D₁ := Metric.isOpen_ball.measurableSet
  have hD₂ : MeasurableSet D₂ := Metric.isOpen_ball.measurableSet
  have hU : MeasurableSet U := hD₁.union hD₂
  have hUD : U ⊆ D := by
    intro z hz
    rw [hDdef, Metric.mem_ball, dist_zero_right]
    rcases hz with hz | hz
    · exact norm_lt_of_mem_invSub norm_invSubCenterLeft hz
    · exact norm_lt_of_mem_invSub norm_invSubCenterRight hz
  have hfin := regularizedGMC_finite_ae P X hX Xc hXc γ r
  -- Step 1: shrinking the disk to the two subdisks increases the Laplace transform
  have hstep1 : cutoffLaplace P Xc γ r D x ≤ cutoffLaplace P Xc γ r U x := by
    unfold cutoffLaplace
    refine integral_mono_ae (integrable_cutoffLaplace_integrand P X hX Xc hXc γ r D hD _
      (Real.exp_pos x).le) (integrable_cutoffLaplace_integrand P X hX Xc hXc γ r U hU _
      (Real.exp_pos x).le) ?_
    filter_upwards [hfin] with ω hω
    apply Real.exp_le_exp.mpr
    have hmono : (regularizedGMC P Xc γ r ω U).toReal ≤ (regularizedGMC P Xc γ r ω D).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hUD)
    nlinarith [Real.exp_pos x]
  -- Step 2: Kahane's Laplace comparison with the glued field
  set Φ : Ω → ℂ → ℝ := fun ω z => Xc ω z r with hΦdef
  have hΦ : IsCenteredGaussianField P Φ := circleAverage_isCenteredGaussianField P X hX Xc hXc r
  have hΨ := gluedField_isCenteredGaussianField P Φ hΦ D₁ hD₁ C
  set PY : Measure (Ω × Ω × ℝ) := P.prod (P.prod (gaussianReal 0 C)) with hPY
  let _ : IsProbabilityMeasure (gaussianReal 0 C) := inferInstance
  let _ : IsProbabilityMeasure PY := inferInstance
  set νM : Measure ℂ := gmcReferenceMeasure.restrict U with hνM
  have hσfin : gmcReferenceMeasure U ≠ ⊤ :=
    ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
  have hνfin : IsFiniteMeasure νM := by
    rw [hνM]
    exact isFiniteMeasure_restrict.mpr hσfin
  set ν : FiniteMeasure ℂ := ⟨νM, hνfin⟩ with hνdef
  have hσpos : gmcReferenceMeasure D₁ ≠ 0 := by
    have hball : Metric.ball (0 : ℂ) (1 / 4 * (1 / 8)) ⊆ Metric.ball 0 1 :=
      Metric.ball_subset_ball (by norm_num)
    have hpos := gmc_reference_ball_intensity_pos (by norm_num : (0 : ℝ) < 1 / 4 * (1 / 8))
      (by norm_num)
    intro hzero
    -- translate positivity: reference density is `1` on the unit disk, so mass is volume
    have hres1 := gmcReferenceMeasure_restrict_unit_chart D₁ hD₁ (fun z hz =>
      (norm_le_of_mem_invSub norm_invSubCenterLeft hz).trans (by norm_num))
    have hres0 := gmcReferenceMeasure_restrict_unit_chart (Metric.ball (0 : ℂ) (1 / 4 * (1 / 8)))
      Metric.isOpen_ball.measurableSet (fun z hz => by
        rw [Metric.mem_ball, dist_zero_right] at hz; linarith)
    have hv1 : gmcReferenceMeasure D₁ = volume D₁ := by
      have := congrArg (fun μ : Measure ℂ => μ Set.univ) hres1
      simpa [Measure.restrict_apply_univ] using this
    have hv0 : gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 4 * (1 / 8))) =
        volume (Metric.ball (0 : ℂ) (1 / 4 * (1 / 8))) := by
      have := congrArg (fun μ : Measure ℂ => μ Set.univ) hres0
      simpa [Measure.restrict_apply_univ] using this
    rw [hv1, hD₁def, Measure.addHaar_ball_center] at hzero
    rw [hv0] at hpos
    exact hpos.ne' hzero
  have hν : ν ≠ 0 := by
    intro h0
    have hval : (ν : Measure ℂ) Set.univ = 0 := by rw [h0]; rfl
    change νM Set.univ = 0 at hval
    rw [hνM, Measure.restrict_apply_univ] at hval
    exact hσpos (measure_mono_null Set.subset_union_left hval)
  have hνprod : ((ν : Measure ℂ).prod (ν : Measure ℂ)) =
      (gmcReferenceMeasure.prod gmcReferenceMeasure).restrict (U ×ˢ U) := by
    change νM.prod νM = _
    rw [hνM, Measure.prod_restrict]
  have hmemU : ∀ᵐ xy ∂(ν : Measure ℂ).prod (ν : Measure ℂ), xy.1 ∈ U ∧ xy.2 ∈ U := by
    rw [hνprod]
    filter_upwards [ae_restrict_mem (hU.prod hU)] with xy hxy
    exact hxy
  have hmemU1 : ∀ᵐ z ∂(ν : Measure ℂ), z ∈ U := by
    change ∀ᵐ z ∂νM, z ∈ U
    rw [hνM]
    exact ae_restrict_mem hU
  have hcov : ∀ᵐ xy ∂(ν : Measure ℂ).prod ν,
      gaussianCovariance P (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        gaussianCovariance PY (fun ω => gluedField Φ D₁ ω xy.1)
          (fun ω => gluedField Φ D₁ ω xy.2) := by
    filter_upwards [hmemU] with xy ⟨hx, hy⟩
    have hC0 : (0 : ℝ) ≤ C := C.2
    unfold gaussianCovariance
    by_cases hx1 : xy.1 ∈ D₁ <;> by_cases hy1 : xy.2 ∈ D₁
    · rw [gluedField_covariance_of_mem_of_mem P Φ hΦ D₁ C hx1 hy1]
      linarith
    · have hy2 : xy.2 ∈ D₂ := hy.resolve_left hy1
      rw [gluedField_covariance_of_mem_of_notMem P Φ hΦ D₁ C hx1 hy1]
      exact circleField_covariance_le_invSepConst P X hX Xc hXc r hr hx1 hy2
    · have hx2 : xy.1 ∈ D₂ := hx.resolve_left hx1
      have hcomm : ∫ q, gluedField Φ D₁ q xy.1 * gluedField Φ D₁ q xy.2 ∂PY =
          ∫ q, gluedField Φ D₁ q xy.2 * gluedField Φ D₁ q xy.1 ∂PY := by
        congr 1
        funext q
        exact mul_comm _ _
      rw [hcomm, gluedField_covariance_of_mem_of_notMem P Φ hΦ D₁ C hy1 hx1]
      have h := circleField_covariance_le_invSepConst P X hX Xc hXc r hr hy1 hx2
      have hcomm' : ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P = ∫ ω, Φ ω xy.2 * Φ ω xy.1 ∂P := by
        congr 1
        funext ω
        exact mul_comm _ _
      rw [hcomm']
      exact h
    · rw [gluedField_covariance_of_notMem_of_notMem P Φ hΦ D₁ C hx1 hy1]
      linarith
  have hdiag : ∀ᵐ z ∂(ν : Measure ℂ),
      gaussianVariance P (fun ω => Φ ω z) ≤ gaussianVariance PY (fun ω => gluedField Φ D₁ ω z) := by
    filter_upwards [] with z
    have hC0 : (0 : ℝ) ≤ C := C.2
    unfold gaussianVariance gaussianCovariance
    by_cases hz : z ∈ D₁
    · rw [gluedField_covariance_of_mem_of_mem P Φ hΦ D₁ C hz hz]
      linarith
    · rw [gluedField_covariance_of_notMem_of_notMem P Φ hΦ D₁ C hz hz]
      linarith
  have hK := kahane_field_laplace_of_nonzero_finite_measure_eq P PY Φ (gluedField Φ D₁) hΦ hΨ
    ν hν (fun _ => 1) measurable_const ⟨1, fun _ => le_rfl⟩ γ (Real.exp x)
    (Real.exp_pos x).le hcov hdiag
  -- Step 3: identify the left side with the Laplace transform on `U`
  have hLeft : (∫⁻ ω, ENNReal.ofReal (Real.exp (-(Real.exp x) *
      (fieldChaosMass P Φ (ν : Measure ℂ) (fun _ => 1) γ ω).toReal)) ∂P) =
      ENNReal.ofReal (cutoffLaplace P Xc γ r U x) := by
    rw [cutoffLaplace, ofReal_integral_eq_lintegral_ofReal
      (integrable_cutoffLaplace_integrand P X hX Xc hXc γ r U hU _ (Real.exp_pos x).le)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    apply lintegral_congr
    intro ω
    rw [regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r U hU ω]
    rfl
  -- Step 4: identify the right side with the product of the subdisk transforms
  set S : ℝ → ℝ := fun ξ => Real.exp (x + γ * ξ - γ ^ 2 * C / 2) with hS
  set m₁ : Ω → ℝ := fun ω => (regularizedGMC P Xc γ r ω D₁).toReal with hm₁
  set m₂ : Ω → ℝ := fun ω => (regularizedGMC P Xc γ r ω D₂).toReal with hm₂
  have hm₁meas : Measurable m₁ := measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r D₁ hD₁
  have hm₂meas : Measurable m₂ := measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r D₂ hD₂
  have hSmeas : Measurable S := by
    rw [hS]
    fun_prop
  have hrestr₁ : νM.restrict D₁ = gmcReferenceMeasure.restrict D₁ := by
    rw [hνM, Measure.restrict_restrict hD₁, Set.inter_eq_left.mpr Set.subset_union_left]
  have hrestr₂ : νM.restrict D₁ᶜ = gmcReferenceMeasure.restrict D₂ := by
    rw [hνM, Measure.restrict_restrict hD₁.compl]
    congr 1
    ext z
    constructor
    · rintro ⟨hz1, hz2 | hz2⟩
      · exact absurd hz2 hz1
      · exact hz2
    · intro hz
      exact ⟨Set.disjoint_left.mp invSub_disjoint.symm hz, Or.inr hz⟩
  have hfinY : ∀ᵐ q ∂PY, IsFiniteMeasure (regularizedGMC P Xc γ r q.1) ∧
      IsFiniteMeasure (regularizedGMC P Xc γ r q.2.1) := by
    have h1 : ∀ᵐ q ∂PY, IsFiniteMeasure (regularizedGMC P Xc γ r q.1) :=
      (Measure.quasiMeasurePreserving_fst).ae hfin
    have h2 : ∀ᵐ q ∂PY, IsFiniteMeasure (regularizedGMC P Xc γ r q.2.1) := by
      have h2' : ∀ᵐ p ∂P.prod (gaussianReal 0 C), IsFiniteMeasure (regularizedGMC P Xc γ r p.1) :=
        (Measure.quasiMeasurePreserving_fst).ae hfin
      exact (Measure.quasiMeasurePreserving_snd).ae h2'
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1, hq2⟩
  have hRightPoint : ∀ᵐ q ∂PY,
      ENNReal.ofReal (Real.exp (-(Real.exp x) *
        (fieldChaosMass PY (gluedField Φ D₁) (ν : Measure ℂ) (fun _ => 1) γ q).toReal)) =
      ENNReal.ofReal (Real.exp (-S q.2.2 * m₁ q.1) * Real.exp (-S q.2.2 * m₂ q.2.1)) := by
    filter_upwards [hfinY] with q ⟨hq1, hq2⟩
    congr 1
    change Real.exp (-(Real.exp x) *
      (fieldChaosMass PY (gluedField Φ D₁) νM (fun _ => 1) γ q).toReal) = _
    rw [gluedField_fieldChaosMass P Φ hΦ D₁ hD₁ C νM (fun _ => 1) γ q, hrestr₁, hrestr₂,
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r D₁ hD₁,
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r D₂ hD₂,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← Real.exp_add]
    congr 1
    rw [hS, hm₁, hm₂]
    simp only
    rw [show x + γ * q.2.2 - γ ^ 2 * (C : ℝ) / 2 = x + (γ * q.2.2 - γ ^ 2 / 2 * C) by ring,
      Real.exp_add]
    ring
  have hRight : (∫⁻ q, ENNReal.ofReal (Real.exp (-(Real.exp x) *
      (fieldChaosMass PY (gluedField Φ D₁) (ν : Measure ℂ) (fun _ => 1) γ q).toReal)) ∂PY) =
      ENNReal.ofReal (∫ ξ, cutoffLaplace P Xc γ r D₁ (x + γ * ξ - γ ^ 2 * C / 2) *
        cutoffLaplace P Xc γ r D₂ (x + γ * ξ - γ ^ 2 * C / 2) ∂gaussianReal 0 C) := by
    rw [lintegral_congr_ae hRightPoint]
    have hSnn : ∀ ξ, 0 ≤ S ξ := fun ξ => (Real.exp_pos _).le
    have hprod := integral_prod_prod_exp_mul_exp P (gaussianReal 0 C) m₁ m₂ hm₁meas hm₂meas
      (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) S hSmeas hSnn
    have hint : Integrable (fun q : Ω × Ω × ℝ =>
        Real.exp (-S q.2.2 * m₁ q.1) * Real.exp (-S q.2.2 * m₂ q.2.1)) PY := by
      refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun q => ?_)
      · exact ((Real.measurable_exp.comp (((hSmeas.comp (measurable_snd.comp
          measurable_snd)).neg).mul (hm₁meas.comp measurable_fst))).mul
          (Real.measurable_exp.comp (((hSmeas.comp (measurable_snd.comp
          measurable_snd)).neg).mul (hm₂meas.comp (measurable_fst.comp
          measurable_snd))))).aestronglyMeasurable
      · rw [norm_mul]
        calc ‖Real.exp (-S q.2.2 * m₁ q.1)‖ * ‖Real.exp (-S q.2.2 * m₂ q.2.1)‖ ≤ 1 * 1 :=
              mul_le_mul (laplaceProduct_integrand_bound _ _ (hSnn _) ENNReal.toReal_nonneg)
                (laplaceProduct_integrand_bound _ _ (hSnn _) ENNReal.toReal_nonneg)
                (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
      hprod]
    rfl
  rw [hLeft, hRight] at hK
  have hRnn : 0 ≤ ∫ ξ, cutoffLaplace P Xc γ r D₁ (x + γ * ξ - γ ^ 2 * C / 2) *
      cutoffLaplace P Xc γ r D₂ (x + γ * ξ - γ ^ 2 * C / 2) ∂gaussianReal 0 C :=
    integral_nonneg fun ξ => mul_nonneg (cutoffLaplace_nonneg P Xc γ r D₁ _)
      (cutoffLaplace_nonneg P Xc γ r D₂ _)
  exact hstep1.trans ((ENNReal.ofReal_le_ofReal_iff hRnn).mp hK)

/-- Every inverse moment of the cutoff mass of the reference disk is bounded uniformly in the
cutoff. -/
theorem regularizedGMC_reference_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (q : ℝ) (hq : 0 < q) :
    ∃ K : ℝ, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ (-q) ∂P ≤ ENNReal.ofReal K :=
  regularizedGMC_reference_inverse_moment_uniform_of_twoBranch P X hX Xc hXc γ hγ hγ2
    invSepConst invSepConst_pos (fun r hr x => cutoffLaplace_twoBranch P X hX Xc hXc γ r
      (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) x) q hq

end DOZZ.Proofs
