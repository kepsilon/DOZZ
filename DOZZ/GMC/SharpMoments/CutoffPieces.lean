/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CoulombCutoffDefs
public import DOZZ.GMC.SharpMoments.SeibergMomentBound
public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass

/-! # Decomposition of cutoff Coulomb masses into root, bulk and exterior pieces

Given pointwise bounds of a weight near the roots (by the softened singularity), on a bounded set
away from the roots, and far out (by a power), the integral of the weight against the cutoff
chaos is bounded by cutoff weighted masses at the roots, the cutoff mass of a disk, and the
exterior power integral; positive moments are bounded accordingly. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Cutoff chaos has no atom at the origin. -/
theorem regularizedGMC_singleton_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) (x : ℂ) : regularizedGMC P Xc γ r ω {x} = 0 := by
  rw [regularizedGMC]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton x)

/-- Every point lies near a root, in the bulk, or in the exterior. -/
theorem weight_le_pieces {N : ℕ} (G : ℂ → ℝ≥0∞) (z : Fin N → ℂ) (ρs R0 : ℝ) (x : ℂ) :
    G x ≤ ∑ k, (Metric.ball (z k) ρs).indicator G x +
      {y : ℂ | ‖y‖ ≤ R0 ∧ ∀ k, ρs ≤ ‖y - z k‖}.indicator G x +
      {y : ℂ | R0 ≤ ‖y‖}.indicator G x := by
  by_cases hE : R0 ≤ ‖x‖
  · rw [Set.indicator_of_mem (show x ∈ {y : ℂ | R0 ≤ ‖y‖} from hE)]
    exact le_add_left le_rfl
  by_cases hroot : ∃ k, ‖x - z k‖ < ρs
  · obtain ⟨k, hk⟩ := hroot
    have hxk : x ∈ Metric.ball (z k) ρs := by rwa [Metric.mem_ball, dist_eq_norm]
    refine le_trans ?_ (le_add_right (le_add_right le_rfl))
    calc G x = (Metric.ball (z k) ρs).indicator G x := (Set.indicator_of_mem hxk G).symm
      _ ≤ ∑ j, (Metric.ball (z j) ρs).indicator G x :=
        Finset.single_le_sum (f := fun j => (Metric.ball (z j) ρs).indicator G x)
          (fun _ _ => zero_le) (Finset.mem_univ k)
  · push Not at hroot hE
    have hK : x ∈ {y : ℂ | ‖y‖ ≤ R0 ∧ ∀ k, ρs ≤ ‖y - z k‖} := ⟨hE.le, hroot⟩
    rw [Set.indicator_of_mem hK]
    exact le_trans (le_add_left le_rfl) (le_add_right le_rfl)

/-- The integral of a weight with root, bulk and exterior bounds against the cutoff chaos. -/
theorem cutoff_weight_integral_le_pieces
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) {N : ℕ}
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) (r : ℝ) (ω : Ω) (G : ℂ → ℝ≥0∞)
    (hG : Measurable G) {ρs R0 CR CB CE : ℝ} (hρs1 : ρs ≤ 1)
    (hroot : ∀ k x, x ∈ Metric.ball (z k) ρs → x ≠ 0 →
      G x ≤ ENNReal.ofReal CR * ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)))
    (hbulk : ∀ x, ‖x‖ ≤ R0 → (∀ k, ρs ≤ ‖x - z k‖) → x ≠ 0 → G x ≤ ENNReal.ofReal CB)
    (hext : ∀ x, R0 ≤ ‖x‖ →
      G x ≤ ENNReal.ofReal CE * ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0)) :
    ∫⁻ x, G x ∂regularizedGMC P Xc γ r ω ≤
      ∑ k, ENNReal.ofReal CR *
          cutoffWeightedGmcBallMass P Xc γ (α k) (z k) 1 (Real.exp (-r)) ω +
        ENNReal.ofReal CB * regularizedGMC P Xc γ r ω (Metric.closedBall 0 R0) +
        ENNReal.ofReal CE * ∫⁻ x in {x : ℂ | R0 ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0)
          ∂regularizedGMC P Xc γ r ω := by
  set μ : Measure ℂ := regularizedGMC P Xc γ r ω with hμ
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hne : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact regularizedGMC_singleton_eq_zero P Xc γ r ω 0
  set K : Set ℂ := {y : ℂ | ‖y‖ ≤ R0 ∧ ∀ k, ρs ≤ ‖y - z k‖} with hK
  set E : Set ℂ := {y : ℂ | R0 ≤ ‖y‖} with hE
  have hKm : MeasurableSet K := measurableSet_coulombBulk z ρs R0
  have hEm : MeasurableSet E := measurableSet_le measurable_const measurable_norm
  have hBm : ∀ k, MeasurableSet (Metric.ball (z k) ρs) := fun k => Metric.isOpen_ball.measurableSet
  have hS : Measurable fun x => ∑ k, (Metric.ball (z k) ρs).indicator G x :=
    Finset.measurable_fun_sum _ fun k _ => hG.indicator (hBm k)
  have hSK : Measurable fun x => ∑ k, (Metric.ball (z k) ρs).indicator G x + K.indicator G x :=
    hS.add (hG.indicator hKm)
  have hpow : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  calc ∫⁻ x, G x ∂μ
      ≤ ∫⁻ x, ((∑ k, (Metric.ball (z k) ρs).indicator G x + K.indicator G x) +
          E.indicator G x) ∂μ := lintegral_mono fun x => weight_le_pieces G z ρs R0 x
    _ = ∑ k, ∫⁻ x in Metric.ball (z k) ρs, G x ∂μ + ∫⁻ x in K, G x ∂μ + ∫⁻ x in E, G x ∂μ := by
        rw [lintegral_add_left hSK, lintegral_add_left hS,
          lintegral_finsetSum _ fun k _ => hG.indicator (hBm k), lintegral_indicator hKm,
          lintegral_indicator hEm]
        simp only [lintegral_indicator (hBm _)]
    _ ≤ _ := by
        gcongr with k hk
        · -- root pieces
          rw [cutoffWeightedGmcBallMass, hlog]
          calc ∫⁻ x in Metric.ball (z k) ρs, G x ∂μ
              ≤ ∫⁻ x in Metric.ball (z k) ρs, ENNReal.ofReal CR *
                  ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) ∂μ := by
                refine setLIntegral_mono_ae' (hBm k) ?_
                filter_upwards [hne] with x hx0 hx
                exact hroot k x hx hx0
            _ ≤ ∫⁻ x in Metric.ball (z k) 1, ENNReal.ofReal CR *
                  ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) ∂μ :=
                lintegral_mono_set (Metric.ball_subset_ball hρs1)
            _ = ENNReal.ofReal CR * ∫⁻ x in Metric.ball (z k) 1,
                  ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) ∂μ :=
                lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
                  (((measurable_id.sub_const _).norm.add_const _).pow_const _))
        · -- the bulk piece
          calc ∫⁻ x in K, G x ∂μ ≤ ∫⁻ _x in K, ENNReal.ofReal CB ∂μ := by
                refine setLIntegral_mono_ae' hKm ?_
                filter_upwards [hne] with x hx0 hx
                exact hbulk x hx.1 hx.2 hx0
            _ = ENNReal.ofReal CB * μ K := setLIntegral_const _ _
            _ ≤ ENNReal.ofReal CB * μ (Metric.closedBall 0 R0) := by
                gcongr
                intro x hx
                rw [Metric.mem_closedBall, dist_zero_right]
                exact hx.1
        · -- the exterior piece
          rw [← lintegral_const_mul _ hpow]
          exact setLIntegral_mono' hEm fun x hx => hext x hx

end DOZZ.Proofs
