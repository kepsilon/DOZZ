/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedCutoffCompactSlack
public import DOZZ.GMC.Moments.WeightedCutoffPositiveSubunit
public import DOZZ.GMC.Moments.WeightedCutoffSubunitScale

/-! Compact-parameter uniformity for positive-charge subunit cutoff moments. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem compact_real_nonneg_upper_bound {ι : Type*} [TopologicalSpace ι]
    {T : Set ι} (hT : IsCompact T) (f : ι → ℝ) (hf : ContinuousOn f T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ T, f t ≤ A := by
  rcases T.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨0, le_rfl, ?_⟩
    simp [hEmpty]
  · obtain ⟨t, ht, hmax⟩ := hT.exists_isMaxOn hNonempty hf
    refine ⟨max 0 (f t), le_max_left _ _, ?_⟩
    intro s hs
    exact le_trans (hmax hs) (le_max_right _ _)


/-- The all-charge subunit cutoff bound remains uniform when `γ` and the admissible `(α,p)`
parameters range over compact sets. The same constant works for every chart-contained center and
subunit radius. -/
theorem cutoffWeightedGmcBallMoment_subunit_compact_gamma_parameters_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, 0 < t.2 ∧ t.2 ≤ 1 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z : ℂ, ∀ R : ℝ, 0 < R → R ≤ 1 / 2 →
      ‖z‖ + 2 * R ≤ 1 → ∀ γ ∈ Γ, ∀ t ∈ T, ∀ δ : ℝ, 0 < δ → δ ≤ R →
        (∫⁻ ω, ENNReal.rpow
          (cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω) t.2 ∂P) ≤
          C * ENNReal.ofReal
            (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
  let U : Set (ℝ × (ℝ × ℝ)) := Γ ×ˢ T
  have hU : IsCompact U := hΓ.prod hT
  have hγpos (g : ℝ) (hg : g ∈ Γ) : 0 < g := (hΓ2 hg).1
  have hQcont : ContinuousOn (fun g : ℝ => Q g) Γ := by
    dsimp [Q]
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun g hg => (hγpos g hg).ne')
    · exact continuousOn_id.div_const 2
  let eta : ℝ × (ℝ × ℝ) → ℝ := fun u =>
    weightedCutoffMomentScaleExponent u.1 u.2.1 u.2.2
  have hQcomp : ContinuousOn (fun u : ℝ × (ℝ × ℝ) => Q u.1) U :=
    hQcont.comp continuousOn_fst (fun u hu => hu.1)
  have hetaCont : ContinuousOn eta U := by
    dsimp [eta, weightedCutoffMomentScaleExponent]
    fun_prop
  have hpositive : ∀ u ∈ U, 0 < eta u := by
    intro u hu
    have hadm := hTadm u.1 hu.1 u.2 hu.2
    exact weightedGmcMomentExponent_pos_of_sharp_range (hγpos u.1 hu.1)
      hadm.1 hadm.2.2
  obtain ⟨ε, hε, hεlower⟩ := hU.exists_forall_le' hetaCont hpositive
  let xi : ℝ × (ℝ × ℝ) → ℝ := fun u =>
    2 * u.2.2 + u.1 ^ 2 * u.2.2 / 2 - u.1 ^ 2 * u.2.2 ^ 2 / 2
  let coreCoef : ℝ × (ℝ × ℝ) → ℝ := fun u => max (2 ^ xi u) (2 ^ eta u)
  let shellCoef : ℝ × (ℝ × ℝ) → ℝ := fun u =>
    (1 / 2 : ℝ) ^ (-u.1 * u.2.1 * u.2.2) * 2 ^ xi u
  have hxiCont : Continuous xi := by
    dsimp [xi]
    fun_prop
  have hpowXiCont : Continuous (fun u : ℝ × (ℝ × ℝ) => (2 : ℝ) ^ xi u) :=
    (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp hxiCont
  have hpowEtaCont : ContinuousOn (fun u : ℝ × (ℝ × ℝ) => (2 : ℝ) ^ eta u) U :=
    (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).continuousOn.comp
      hetaCont (by intro u hu; exact Set.mem_univ _)
  have hcoreCont : ContinuousOn coreCoef U := by
    have hpair : ContinuousOn (fun u : ℝ × (ℝ × ℝ) =>
        ((2 : ℝ) ^ xi u, (2 : ℝ) ^ eta u)) U :=
      hpowXiCont.continuousOn.prodMk hpowEtaCont
    change ContinuousOn (fun u => max ((2 : ℝ) ^ xi u) ((2 : ℝ) ^ eta u)) U
    exact continuous_max.continuousOn.comp hpair (by
      intro u hu
      exact Set.mem_univ _)
  have hhalfExpCont : Continuous (fun u : ℝ × (ℝ × ℝ) =>
      -u.1 * u.2.1 * u.2.2) := by fun_prop
  have hhalfPowCont : Continuous (fun u : ℝ × (ℝ × ℝ) =>
      (1 / 2 : ℝ) ^ (-u.1 * u.2.1 * u.2.2)) :=
    (Real.continuous_const_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)).comp hhalfExpCont
  have hshellCont : Continuous shellCoef := by
    unfold shellCoef
    exact hhalfPowCont.mul hpowXiCont
  obtain ⟨A, hA, hAupper⟩ := compact_real_nonneg_upper_bound hU coreCoef hcoreCont
  obtain ⟨B, hB, hBupper⟩ :=
    compact_real_nonneg_upper_bound hU shellCoef hshellCont.continuousOn
  let q0Real : ℝ := (1 / 2 : ℝ) ^ ε
  let q0 : ℝ≥0∞ := ENNReal.ofReal q0Real
  let refBase : ℝ≥0∞ := 1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))
  let C : ℝ≥0∞ := ENNReal.ofReal A * refBase +
    ENNReal.ofReal B * refBase * (1 - q0)⁻¹
  have hq0Real : q0Real < 1 := by
    dsimp [q0Real]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hq0 : q0 < 1 := ENNReal.ofReal_lt_one.mpr (by simpa [q0] using hq0Real)
  have hden0 : 1 - q0 ≠ 0 := by
    intro h
    have hq0le : 1 ≤ q0 := tsub_eq_zero_iff_le.mp h
    exact (not_le_of_gt hq0) hq0le
  have hgeom0 : (1 - q0)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden0)
  have hRefTop : refBase < ⊤ := by
    dsimp [refBase]
    have hball : gmcReferenceMeasure (Metric.ball 0 (1 / 2)) ≤
        gmcReferenceMeasure Set.univ := measure_mono (Set.subset_univ _)
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.one_lt_top,
        lt_of_le_of_lt hball (lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top)⟩
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRefTop,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRefTop) hgeom0⟩
  have hq_bound (u : ℝ × (ℝ × ℝ)) (hu : u ∈ U) :
      ENNReal.ofReal ((1 / 2 : ℝ) ^ eta u) ≤ q0 := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (hεlower u hu)
  have hgeom_bound (u : ℝ × (ℝ × ℝ)) (hu : u ∈ U) :
      (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ eta u))⁻¹ ≤ (1 - q0)⁻¹ := by
    apply ENNReal.inv_le_inv'
    exact tsub_le_tsub_left (hq_bound u hu) 1
  refine ⟨C, hC, ?_⟩
  intro z R hR hR1 hchart g hg t ht δ hδ hδR
  let u : ℝ × (ℝ × ℝ) := (g, t)
  have hu : u ∈ U := ⟨hg, ht⟩
  have hadm := hTadm g hg t ht
  have hcoefPos (hαpos : 0 < t.1) :
      cutoffWeightedPositiveSubunitScaleConstant g t.1 t.2 ≤ C := by
    dsimp [cutoffWeightedPositiveSubunitScaleConstant, weightedCutoffMomentScaleExponent,
      xi, eta, shellCoef, coreCoef, refBase, q0, q0Real]
    have hAxi : 2 ^ xi u ≤ A := le_trans (le_max_left _ _) (hAupper u hu)
    have hcore : ENNReal.ofReal (2 ^ xi u) ≤ ENNReal.ofReal A :=
      ENNReal.ofReal_le_ofReal hAxi
    have hshell : ENNReal.ofReal
        ((1 / 2 : ℝ) ^ (-g * t.1 * t.2) * 2 ^ xi u) ≤ ENNReal.ofReal B :=
      ENNReal.ofReal_le_ofReal (hBupper u hu)
    have hgeom : (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ eta u))⁻¹ ≤ (1 - q0)⁻¹ := by
      simpa [u, eta, weightedCutoffMomentScaleExponent] using hgeom_bound u hu
    dsimp [C]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hcore (by positivity)
    · calc
        _ ≤ (ENNReal.ofReal B * refBase) *
            (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ eta u))⁻¹ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hshell (by positivity)) (by positivity)
        _ ≤ (ENNReal.ofReal B * refBase) * (1 - q0)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hcoefNeg : ENNReal.ofReal (2 ^ eta u) * refBase ≤ C := by
    have hAeta : 2 ^ eta u ≤ A := le_trans (le_max_right _ _) (hAupper u hu)
    have hcore : ENNReal.ofReal (2 ^ eta u) * refBase ≤ ENNReal.ofReal A * refBase :=
      mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hAeta) (by positivity)
    dsimp [C]
    calc
      _ ≤ ENNReal.ofReal A * refBase := hcore
      _ ≤ ENNReal.ofReal A * refBase +
          ENNReal.ofReal B * refBase * (1 - q0)⁻¹ := le_add_of_nonneg_right (by positivity)
  have hmoment :
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc g t.1 z R δ ω) t.2 ∂P) ≤
        C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent g t.1 t.2) := by
    by_cases hα : t.1 ≤ 0
    · have hneg := cutoffWeightedGmcBallMoment_nonpos_subunit_scale_formula
        P X hX Xc hXc g t.1 (hγpos g hg) (hΓ2 hg).2 hα
        z R δ t.2 hR hR1 hδ hδR hchart hadm.1 hadm.2.1
      calc
        _ ≤ ENNReal.ofReal (2 ^ eta u) * refBase *
            ENNReal.ofReal (R ^ eta u) := by
          simpa [u, eta, weightedCutoffMomentScaleExponent, refBase] using hneg
        _ ≤ C * ENNReal.ofReal (R ^ eta u) := by
          simpa [u, eta, weightedCutoffMomentScaleExponent] using
            (mul_le_mul_of_nonneg_right hcoefNeg (by positivity))
    · have hαpos : 0 < t.1 := lt_of_not_ge hα
      obtain ⟨_, hformula⟩ := cutoffWeightedGmcBallMoment_positive_subunit_scale_formula
        P X hX Xc hXc g t.1 (hγpos g hg) hαpos z R t.2 hR hR1 hchart
          hadm.1 hadm.2.1 hadm.2.2
      have hbound := hformula δ hδ hδR
      calc
        _ ≤ cutoffWeightedPositiveSubunitScaleConstant g t.1 t.2 * ENNReal.ofReal
            (R ^ weightedCutoffMomentScaleExponent g t.1 t.2) := hbound
        _ ≤ C * ENNReal.ofReal
            (R ^ weightedCutoffMomentScaleExponent g t.1 t.2) := by
          exact mul_le_mul_of_nonneg_right (hcoefPos hαpos) (by positivity)
  exact hmoment

end DOZZ.Proofs
