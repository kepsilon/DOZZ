/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffConvergence
public import DOZZ.GMC.SharpMoments.MomentConvergence

/-! # Exterior power moments of limiting chaos from cutoff bounds

A cutoff-uniform bound on the moments of the exterior power-weighted mass of the finite-cutoff
chaos passes to the limiting chaos. The exterior region is first truncated to the bounded annulus
`R ≤ ‖x‖ ≤ R + m`, where the cutoff integrals converge in probability and Fatou in probability
applies; the truncation is then removed by monotone convergence, first in space and then in
probability. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The power weight `‖x‖ ^ β`, truncated to the bounded annulus `R ≤ ‖x‖ ≤ R + m`. -/
noncomputable def limitExteriorFatou_trunc (R β : ℝ) (m : ℕ) : ℂ → ℝ≥0 :=
  {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m}.indicator fun x => (‖x‖ ^ β).toNNReal

/-- The truncation annulus is measurable. -/
theorem limitExteriorFatou_measurableSet_annulus (R : ℝ) (m : ℕ) :
    MeasurableSet {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m} :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

/-- The truncated weight is measurable. -/
theorem limitExteriorFatou_trunc_measurable (R β : ℝ) (m : ℕ) :
    Measurable (limitExteriorFatou_trunc R β m) :=
  (measurable_norm.pow_const β).real_toNNReal.indicator
    (limitExteriorFatou_measurableSet_annulus R m)

/-- The truncated weight is bounded. -/
theorem limitExteriorFatou_trunc_le (R : ℝ) {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) (x : ℂ) :
    limitExteriorFatou_trunc R β m x ≤ ((R + m) ^ β).toNNReal := by
  unfold limitExteriorFatou_trunc
  by_cases hx : x ∈ {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m}
  · rw [Set.indicator_of_mem hx]
    exact Real.toNNReal_le_toNNReal (Real.rpow_le_rpow (norm_nonneg x) hx.2 hβ)
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

/-- The truncated weight vanishes outside the closed disk of radius `R + m`. -/
theorem limitExteriorFatou_trunc_eq_zero (R β : ℝ) (m : ℕ) {x : ℂ}
    (hx : x ∉ closedBall (0 : ℂ) (R + m)) : limitExteriorFatou_trunc R β m x = 0 := by
  unfold limitExteriorFatou_trunc
  refine Set.indicator_of_notMem (fun h => hx ?_) _
  simpa [mem_closedBall_zero_iff] using h.2

/-- The truncated weight, viewed in `[0, ∞]`, is the indicator of the annulus times the weight. -/
theorem limitExteriorFatou_trunc_coe (R β : ℝ) (m : ℕ) (x : ℂ) :
    (limitExteriorFatou_trunc R β m x : ℝ≥0∞) =
      {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m}.indicator (fun x => ENNReal.ofReal (‖x‖ ^ β)) x := by
  by_cases hx : x ∈ {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m}
  · simp only [limitExteriorFatou_trunc, Set.indicator_of_mem hx]
    rfl
  · simp only [limitExteriorFatou_trunc, Set.indicator_of_notMem hx]
    simp

/-- Integrating the truncated weight is at most integrating the weight over the exterior. -/
theorem limitExteriorFatou_lintegral_trunc_le (R β : ℝ) (m : ℕ) (μ : Measure ℂ) :
    ∫⁻ x, (limitExteriorFatou_trunc R β m x : ℝ≥0∞) ∂μ ≤
      ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β) ∂μ := by
  simp only [limitExteriorFatou_trunc_coe]
  rw [lintegral_indicator (limitExteriorFatou_measurableSet_annulus R m)]
  exact lintegral_mono_set fun x hx => hx.1

/-- The truncated weights increase with the truncation level. -/
theorem limitExteriorFatou_trunc_mono (R β : ℝ) (x : ℂ) :
    Monotone fun m : ℕ => (limitExteriorFatou_trunc R β m x : ℝ≥0∞) := by
  intro m n hmn
  simp only [limitExteriorFatou_trunc_coe]
  have hle : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hsub : {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m} ⊆ {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + n} :=
    fun y hy => ⟨hy.1, hy.2.trans (by linarith)⟩
  exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) x

/-- The truncated weights increase to the exterior weight. -/
theorem limitExteriorFatou_trunc_tendsto (R β : ℝ) (x : ℂ) :
    Tendsto (fun m : ℕ => (limitExteriorFatou_trunc R β m x : ℝ≥0∞)) atTop
      (𝓝 ({x : ℂ | R ≤ ‖x‖}.indicator (fun x => ENNReal.ofReal (‖x‖ ^ β)) x)) := by
  by_cases hx : R ≤ ‖x‖
  · rw [Set.indicator_of_mem (show x ∈ {x : ℂ | R ≤ ‖x‖} from hx)]
    obtain ⟨N, hN⟩ := exists_nat_ge (‖x‖ - R)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    have hNm : (N : ℝ) ≤ m := Nat.cast_le.mpr hm
    rw [limitExteriorFatou_trunc_coe,
      Set.indicator_of_mem (show x ∈ {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m} from ⟨hx, by linarith⟩)]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℂ | R ≤ ‖x‖} from hx)]
    refine tendsto_const_nhds.congr fun m => ?_
    rw [limitExteriorFatou_trunc_coe,
      Set.indicator_of_notMem (show x ∉ {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + m} from fun h => hx h.1)]

/-- For a fixed measure, the integrals of the truncated weights increase to the exterior
integral of the weight. -/
theorem limitExteriorFatou_lintegral_trunc_tendsto (R β : ℝ) (μ : Measure ℂ) :
    Tendsto (fun m : ℕ => ∫⁻ x, (limitExteriorFatou_trunc R β m x : ℝ≥0∞) ∂μ) atTop
      (𝓝 (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β) ∂μ)) := by
  have hmeas : MeasurableSet {x : ℂ | R ≤ ‖x‖} := measurableSet_le measurable_const measurable_norm
  rw [← lintegral_indicator hmeas]
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun m => (measurable_coe_nnreal_ennreal.comp
      (limitExteriorFatou_trunc_measurable R β m)).aemeasurable)
    (Eventually.of_forall fun x => limitExteriorFatou_trunc_mono R β x)
    (Eventually.of_forall fun x => limitExteriorFatou_trunc_tendsto R β x)

/-- A bounded function has finite integral against a finite measure. -/
theorem limitExteriorFatou_lintegral_lt_top (μ : Measure ℂ) [IsFiniteMeasure μ] (f : ℂ → ℝ≥0)
    (b : ℝ≥0) (hfb : ∀ x, f x ≤ b) : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ⊤ := by
  calc ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤ ∫⁻ _, (b : ℝ≥0∞) ∂μ :=
        lintegral_mono fun x => ENNReal.coe_le_coe.2 (hfb x)
    _ = b * μ Set.univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ Set.univ)

/-- Fatou in probability for a fixed truncation: the cutoff bound passes to the limiting chaos. -/
theorem limitExteriorFatou_trunc_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (R : ℝ) {β : ℝ} (hβ : 0 ≤ β) {t : ℝ} (ht : 0 < t) (C : ℝ≥0∞)
    (hC : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β)
      ∂regularizedGMC P Xc γ r ω) ^ t ∂P ≤ C) (m : ℕ) :
    ∫⁻ ω, (∫⁻ x, (limitExteriorFatou_trunc R β m x : ℝ≥0∞) ∂M ω) ^ t ∂P ≤ C := by
  have hfm := limitExteriorFatou_trunc_measurable R β m
  have hfm' : Measurable fun x => (limitExteriorFatou_trunc R β m x : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hfm
  have hb := limitExteriorFatou_trunc_le R hβ m
  have hconv := regularizedGMC_lintegral_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc _ hfm _ hb
    (R + m) fun x hx => limitExteriorFatou_trunc_eq_zero R β m hx
  refine momentConv_lintegral_rpow_limit_le P
    (fun n ω => ∫⁻ x, (limitExteriorFatou_trunc R β m x : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω)
    (fun ω => ∫⁻ x, (limitExteriorFatou_trunc R β m x : ℝ≥0∞) ∂M ω)
    (fun n => ((Measure.measurable_lintegral hfm').comp
      (regularizedGMC_measurable P X hX Xc hXc γ n)).aemeasurable) (fun n => ?_)
    (Eventually.of_forall fun ω => ?_) hconv t C (fun n => ?_)
  · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hω
    exact (limitExteriorFatou_lintegral_lt_top (regularizedGMC P Xc γ n ω) _ _ hb).ne
  · have := hM.1 ω
    exact (limitExteriorFatou_lintegral_lt_top (M ω) _ _ hb).ne
  · exact le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (limitExteriorFatou_lintegral_trunc_le R β m _) ht.le) (hC n (Nat.cast_nonneg n))

/-- A cutoff-uniform bound on exterior power moments bounds the exterior power moment of the
limiting chaos. -/
theorem gmc_exterior_power_moment_le_of_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {R : ℝ} {β : ℝ} (hβ : 0 ≤ β) {t : ℝ} (ht : 0 < t) (C : ℝ≥0∞)
    (hC : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β)
      ∂regularizedGMC P Xc γ r ω) ^ t ∂P ≤ C) :
    ∫⁻ ω, (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β) ∂M ω) ^ t ∂P ≤ C := by
  have hlim : Tendsto (fun m : ℕ => ∫⁻ ω, (∫⁻ x, (limitExteriorFatou_trunc R β m x : ℝ≥0∞)
        ∂M ω) ^ t ∂P) atTop
      (𝓝 (∫⁻ ω, (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β) ∂M ω) ^ t ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun m => ?_)
      (Eventually.of_forall fun ω m n hmn => ?_) (Eventually.of_forall fun ω => ?_)
    · exact (gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _
        (measurable_coe_nnreal_ennreal.comp
          (limitExteriorFatou_trunc_measurable R β m))).pow_const t
    · exact ENNReal.rpow_le_rpow (lintegral_mono fun x => limitExteriorFatou_trunc_mono R β x hmn)
        ht.le
    · exact (ENNReal.continuous_rpow_const.tendsto _).comp
        (limitExteriorFatou_lintegral_trunc_tendsto R β (M ω))
  exact le_of_tendsto' hlim
    (limitExteriorFatou_trunc_moment_le P X hX γ hγ hγ2 M hM Xc hXc R hβ ht C hC)

end DOZZ.Proofs
