/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Weighted local moment finiteness on the subunit range inside the exact logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem weightedGmcBallMass_aemeasurable_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α r : ℝ) (z : ℂ) : AEMeasurable
      (fun ω : Ω => weightedGmcBallMass γ (M ω) α z r) P := by
  let f : ℂ → ℝ≥0∞ := fun x => (Metric.ball (z : ℂ) r).indicator
    (fun x => ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α)) x
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.indicator
    · fun_prop
    · exact Metric.isOpen_ball.measurableSet
  obtain ⟨N, hN, _hNfinite, hMN⟩ :=
    equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hNintegral : Measurable (fun ω => ∫⁻ x, f x ∂N ω) :=
    (Measure.measurable_lintegral hf).comp hN
  apply hNintegral.aemeasurable.congr
  filter_upwards [hMN] with ω hω
  rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  rw [hω]

/-! The rest of this module uses the a.e. measurable version supplied by the GMC predicate
`DOZZ.IsGMCOf`, so weighted moment integrals can be split without changing the chosen version. -/

private theorem ennreal_ofReal_rpow_of_pos_local {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  have hx0 : ENNReal.ofReal x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hleft : ENNReal.rpow (ENNReal.ofReal x) p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 ENNReal.ofReal_ne_top
  have hright : ENNReal.ofReal (x ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal = (ENNReal.ofReal x).toReal ^ p :=
      (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal := by
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)]

/-- Localizing a negative-power insertion to a smaller disk leaves only a bounded weight on
the remainder. -/
theorem weightedGmcBallMass_le_inner_add_total
    (μ : Measure ℂ) (γ α : ℝ) (z : ℂ) (r ρ : ℝ)
    (hγα : 0 < γ * α) (hρ : 0 < ρ) :
    weightedGmcBallMass γ μ α z r ≤ weightedGmcBallMass γ μ α z ρ +
      ENNReal.ofReal (ρ ^ (-γ * α)) * μ (Metric.ball z r) := by
  let B : Set ℂ := Metric.ball z r
  let D : Set ℂ := Metric.ball z ρ
  let density : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α)
  let inner : ℂ → ℝ≥0∞ := D.indicator density
  let outer : ℂ → ℝ≥0∞ := B.indicator (fun _ => ENNReal.ofReal (ρ ^ (-γ * α)))
  have hq : -γ * α < 0 := by linarith
  have hdensity : Measurable density := by
    dsimp [density]
    fun_prop
  have hinner : Measurable inner := by
    exact hdensity.indicator Metric.isOpen_ball.measurableSet
  have houter : Measurable outer := by
    exact measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hpoint (x : ℂ) : B.indicator density x ≤ inner x + outer x := by
    by_cases hx : x ∈ B
    · by_cases hxρ : x ∈ D
      · simp [inner, outer, hx, hxρ]
      · have hdist : ρ ≤ ‖x - z‖ := by
          have hxρ' : ¬ ‖x - z‖ < ρ := by
            simpa [D, Metric.mem_ball, dist_eq_norm] using hxρ
          exact le_of_not_gt hxρ'
        have hrad : 0 < ‖x - z‖ := lt_of_lt_of_le hρ hdist
        have hpow : ‖x - z‖ ^ (-γ * α) ≤ ρ ^ (-γ * α) :=
          Real.rpow_le_rpow_of_nonpos hρ hdist hq.le
        have hweight : density x ≤ ENNReal.ofReal (ρ ^ (-γ * α)) := by
          change ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) ≤ _
          rw [ennreal_ofReal_rpow_of_pos_local hrad]
          exact ENNReal.ofReal_le_ofReal hpow
        simpa [inner, outer, hx, hxρ] using hweight
    · simp [inner, outer, hx]
  calc
    weightedGmcBallMass γ μ α z r = ∫⁻ x, B.indicator density x ∂μ := by
      rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
    _ ≤ ∫⁻ x, inner x + outer x ∂μ := lintegral_mono hpoint
    _ = ∫⁻ x, inner x ∂μ + ∫⁻ x, outer x ∂μ := lintegral_add_left hinner _
    _ = weightedGmcBallMass γ μ α z ρ +
          ENNReal.ofReal (ρ ^ (-γ * α)) * μ (Metric.ball z r) := by
      have hinnerInt : ∫⁻ x, inner x ∂μ = weightedGmcBallMass γ μ α z ρ := by
        dsimp [inner, D]
        rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
      have houterInt : ∫⁻ x, outer x ∂μ =
          ENNReal.ofReal (ρ ^ (-γ * α)) * μ (Metric.ball z r) := by
        dsimp [outer, B]
        rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet]
      rw [hinnerInt, houterInt]

/-- Strict insertion slack gives every subunit weighted moment at every radius for centers whose
reference half-disk lies in the logarithmic chart. -/
theorem weightedGmcBallMoment_chart_finite_subunit_all_radius
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α p : ℝ) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hz : ‖z‖ + ρ < 1)
    (r : ℝ) (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    weightedGmcBallMoment P M γ α z r p < ⊤ := by
  by_cases hα : α ≤ 0
  · let c : ℝ≥0∞ := ENNReal.ofReal (r ^ (-γ * α))
    have hc : c ^ p < ⊤ := by
      apply ENNReal.rpow_lt_top_of_nonneg hp.le
      exact ENNReal.ofReal_ne_top
    have hmass : gmcMassMoment P M (Metric.ball z r) p < ⊤ := by
      have h := gmc_mass_subunit_moment_bound P X hX γ M hM
        (Metric.ball z r) hp.le hp1
      have href : gmcReferenceMeasure Set.univ < ⊤ :=
        gmcReferenceMeasure_univ_ne_top.lt_top
      exact lt_of_le_of_lt h (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, href⟩)
    have hbound : weightedGmcBallMoment P M γ α z r p ≤ c ^ p *
        gmcMassMoment P M (Metric.ball z r) p := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (c * M ω (Metric.ball z r)) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow
            (weightedGmcBallMass_le_constant_center (M ω) γ α r z hγ hα hr) hp.le
        _ = c ^ p * gmcMassMoment P M (Metric.ball z r) p := by
          have hmeas : AEMeasurable (fun ω =>
              ENNReal.rpow (M ω (Metric.ball z r)) p) P := by
            exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
                (Metric.ball z r) Metric.isOpen_ball.measurableSet)
          calc
            _ = ∫⁻ ω, c ^ p * ENNReal.rpow (M ω (Metric.ball z r)) p ∂P := by
              apply lintegral_congr
              intro ω
              exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
            _ = _ := by rw [lintegral_const_mul'' _ hmeas, gmcMassMoment]
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hc hmass)
  · have hαpos : 0 < α := lt_of_not_ge hα
    let c : ℝ≥0∞ := ENNReal.ofReal (ρ ^ (-γ * α))
    have hc : c ^ p < ⊤ := by
      apply ENNReal.rpow_lt_top_of_nonneg hp.le
      exact ENNReal.ofReal_ne_top
    have hinner : weightedGmcBallMoment P M γ α z ρ p < ⊤ := by
      exact weightedGmcBallMoment_chart_finite_subunit_all_charge
        P X hX γ hγ hγ2 M hM α p z ρ hρ
        (by linarith [norm_nonneg z, hz]) hz hp hp1 hpRange
    have hmass : gmcMassMoment P M (Metric.ball z r) p < ⊤ := by
      have h := gmc_mass_subunit_moment_bound P X hX γ M hM
        (Metric.ball z r) hp.le hp1
      have href : gmcReferenceMeasure Set.univ < ⊤ :=
        gmcReferenceMeasure_univ_ne_top.lt_top
      exact lt_of_le_of_lt h (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, href⟩)
    have hbound : weightedGmcBallMoment P M γ α z r p ≤
        weightedGmcBallMoment P M γ α z ρ p + c ^ p *
          gmcMassMoment P M (Metric.ball z r) p := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (ENNReal.rpow (weightedGmcBallMass γ (M ω) α z ρ) p +
              (c * M ω (Metric.ball z r)) ^ p) ∂P := by
          apply lintegral_mono
          intro ω
          have hlocal := weightedGmcBallMass_le_inner_add_total
            (M ω) γ α z r ρ (by positivity) hρ
          calc
            ENNReal.rpow (weightedGmcBallMass γ (M ω) α z r) p ≤
                ENNReal.rpow
                  (weightedGmcBallMass γ (M ω) α z ρ +
                    ENNReal.ofReal (ρ ^ (-γ * α)) * M ω (Metric.ball z r)) p :=
              ENNReal.rpow_le_rpow hlocal hp.le
            _ ≤ ENNReal.rpow (weightedGmcBallMass γ (M ω) α z ρ) p +
                  (c * M ω (Metric.ball z r)) ^ p := by
              rw [show c = ENNReal.ofReal (ρ ^ (-γ * α)) by rfl]
              exact ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1
        _ = weightedGmcBallMoment P M γ α z ρ p +
              c ^ p * gmcMassMoment P M (Metric.ball z r) p := by
          have hinnerMeas : AEMeasurable (fun ω =>
              ENNReal.rpow (weightedGmcBallMass γ (M ω) α z ρ) p) P :=
            ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (weightedGmcBallMass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
                α ρ z)
          have hmeas : AEMeasurable (fun ω =>
              ENNReal.rpow (M ω (Metric.ball z r)) p) P := by
            exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
                (Metric.ball z r) Metric.isOpen_ball.measurableSet)
          have houter : ∫⁻ ω, (c * M ω (Metric.ball z r)) ^ p ∂P =
              c ^ p * gmcMassMoment P M (Metric.ball z r) p := by
            calc
              _ = ∫⁻ ω, c ^ p * ENNReal.rpow (M ω (Metric.ball z r)) p ∂P := by
                apply lintegral_congr
                intro ω
                exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
              _ = _ := by rw [lintegral_const_mul'' _ hmeas, gmcMassMoment]
          calc
            _ = ∫⁻ ω, ENNReal.rpow (weightedGmcBallMass γ (M ω) α z ρ) p ∂P +
                  ∫⁻ ω, (c * M ω (Metric.ball z r)) ^ p ∂P :=
              lintegral_add_left' hinnerMeas _
            _ = _ := by rw [weightedGmcBallMoment, houter]
    exact lt_of_le_of_lt hbound (ENNReal.add_lt_top.mpr
      ⟨hinner, ENNReal.mul_lt_top hc hmass⟩)

end DOZZ.Proofs
