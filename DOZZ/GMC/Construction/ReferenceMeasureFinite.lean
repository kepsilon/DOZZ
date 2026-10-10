/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import DOZZ.Hypergeom.Planar.RadialCriteria

/-! The equator GMC reference measure has finite total mass. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The deterministic reference density is integrable on the whole plane. -/
theorem gmcReferenceMeasure_univ_ne_top :
    gmcReferenceMeasure Set.univ ≠ ∞ := by
  let B : Set ℂ := Metric.ball 0 1
  let f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hBallVolume : volume B ≠ ∞ := by
    have hclosed : volume (Metric.closedBall (0 : ℂ) 1) ≠ ∞ :=
      (isCompact_closedBall (0 : ℂ) (1 : ℝ)).measure_ne_top
    apply ne_of_lt
    exact (measure_mono (show B ⊆ Metric.closedBall (0 : ℂ) 1 from
      Metric.ball_subset_closedBall)).trans_lt
      (lt_top_iff_ne_top.mpr hclosed)
  have htailReal : IntegrableOn (fun x : ℂ => ‖x‖ ^ (-4 : ℝ)) Bᶜ volume := by
    apply (DOZZ.Proofs.integrableOn_norm_rpow_ball_compl_iff (-4) 1 (by norm_num)).2
    norm_num
  have htailNonneg : 0 ≤ᵐ[volume.restrict Bᶜ]
      (fun x : ℂ => ‖x‖ ^ (-4 : ℝ)) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) _)
  have htailFinite :
      (∫⁻ x in Bᶜ, ENNReal.ofReal (‖x‖ ^ (-4 : ℝ)) ∂volume) ≠ ∞ := by
    change Integrable (fun x : ℂ => ‖x‖ ^ (-4 : ℝ)) (volume.restrict Bᶜ) at htailReal
    rw [← ofReal_integral_eq_lintegral_ofReal htailReal htailNonneg]
    exact ENNReal.ofReal_ne_top
  have hballBound : (∫⁻ x in B, f x ∂volume) ≤ volume B := by
    calc
      (∫⁻ x in B, f x ∂volume) ≤ ∫⁻ x in B, (1 : ℝ≥0∞) ∂volume :=
        setLIntegral_mono (s := B) (f := f) (g := fun _ : ℂ => (1 : ℝ≥0∞))
          measurable_const (fun x hx => by
        have hnorm : 1 ≤ normPlus x := le_max_left _ _
        have hp : normPlus x ^ (-4 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hnorm (by norm_num)
        simp only [f]
        exact ENNReal.ofReal_le_one.mpr hp)
      _ = volume B := by simp
  have htailBound : (∫⁻ x in Bᶜ, f x ∂volume) ≤
      ∫⁻ x in Bᶜ, ENNReal.ofReal (‖x‖ ^ (-4 : ℝ)) ∂volume := by
    exact setLIntegral_mono (s := Bᶜ) (f := f)
      (g := fun x : ℂ => ENNReal.ofReal (‖x‖ ^ (-4 : ℝ))) (by fun_prop)
      (fun x hx => by
        have hxnorm : 1 ≤ ‖x‖ := by
          change ¬ x ∈ Metric.ball (0 : ℂ) 1 at hx
          have hdist : ¬ dist x (0 : ℂ) < 1 := by
            simpa [Metric.mem_ball] using hx
          rw [dist_zero_right] at hdist
          exact le_of_not_gt hdist
        have hmax : normPlus x = ‖x‖ := by
          simp [normPlus, max_eq_right hxnorm]
        simp [f, hmax])
  have htailFinite' : (∫⁻ x in Bᶜ, f x ∂volume) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt htailBound (lt_top_iff_ne_top.mpr htailFinite))
  have htotal : (∫⁻ x, f x ∂volume) ≠ ∞ := by
    rw [← lintegral_add_compl f hB]
    exact ENNReal.add_ne_top.mpr
      ⟨ne_of_lt (lt_of_le_of_lt hballBound (lt_top_iff_ne_top.mpr hBallVolume)),
        htailFinite'⟩
  change (volume.withDensity f) Set.univ ≠ ∞
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using htotal

end DOZZ.Proofs
