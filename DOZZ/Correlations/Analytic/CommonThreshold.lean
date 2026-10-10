/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.AnnularThresholdAE
public import DOZZ.Correlations.Analytic.CommonPowerEnvelope

/-! The threshold estimate with one common envelope for both signs of the mass power. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- A lower negative-power envelope and an upper positive-power envelope control both terms in
the annular threshold estimate. No first-moment hypothesis on the annular mass is used. -/
theorem cpow_common_threshold
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L Z Y U : Ω → ℝ) (lo hi : ℝ) (p : ℂ)
    (hY : AEMeasurable Y P)
    (hH : AEMeasurable (fun ω => ENNReal.ofReal (L ω ^ lo + U ω ^ hi)) P)
    (hL : ∀ᵐ ω ∂P, 0 < L ω) (hLZ : ∀ᵐ ω ∂P, L ω ≤ Z ω)
    (hYpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (hZU : ∀ᵐ ω ∂P, Z ω + Y ω ≤ U ω)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hlop : lo ≤ p.re - 1) (hphi : p.re ≤ hi)
    (u : ℝ) (hu : 0 < u) (m q : ℝ) (hm : 0 < m) (hq : 1 < q) :
    (∫⁻ ω, ENNReal.ofReal ‖((Z ω + Y ω : ℝ) : ℂ) ^ p - (Z ω : ℂ) ^ p‖ ∂P) ≤
      ENNReal.ofReal u * ENNReal.ofReal (2 * ‖p‖) *
        (∫⁻ ω, ENNReal.ofReal (L ω ^ lo + U ω ^ hi) ∂P) +
      ((ENNReal.ofReal 2) ^ q *
        (∫⁻ ω, (ENNReal.ofReal (L ω ^ lo + U ω ^ hi)) ^ q ∂P)) ^ (1 / q) *
        ((∫⁻ ω, (ENNReal.ofReal (Y ω)) ^ m ∂P) / (ENNReal.ofReal u) ^ m) ^
          (1 / (q / (q - 1))) := by
  let H (ω : Ω) := ENNReal.ofReal (L ω ^ lo + U ω ^ hi)
  let F (ω : Ω) := ENNReal.ofReal ‖((Z ω + Y ω : ℝ) : ℂ) ^ p - (Z ω : ℂ) ^ p‖
  have hs : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) < ENNReal.ofReal u →
      F ω ≤ ENNReal.ofReal u * (ENNReal.ofReal (2 * ‖p‖) * H ω) := by
    filter_upwards [hL, hLZ, hYpos, hZU] with ω hL hLZ hY hZU hsmall
    have hyu : Y ω < u := (ENNReal.ofReal_lt_ofReal_iff hu).mp hsmall
    have he := (cpow_common_envelope (L ω) (Z ω) (Y ω) (U ω) lo hi p
      hL hLZ hY hZU hlo hhi hlop hphi).1
    have hU : 0 < U ω := (hL.trans_le hLZ).trans_le
      ((le_add_of_nonneg_right hY).trans hZU)
    have hE : 0 ≤ L ω ^ lo + U ω ^ hi :=
      add_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hU.le _)
    have hbound := he.trans (mul_le_mul_of_nonneg_left hyu.le
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) hE))
    have hnonneg : 0 ≤ 2 * ‖p‖ := by positivity
    have hh := ENNReal.ofReal_le_ofReal hbound
    rw [ENNReal.ofReal_mul (mul_nonneg hnonneg hE),
      ENNReal.ofReal_mul hnonneg] at hh
    simpa only [F, H, mul_comm, mul_left_comm, mul_assoc] using hh
  have hl : ∀ᵐ ω ∂P, F ω ≤ ENNReal.ofReal 2 * H ω := by
    filter_upwards [hL, hLZ, hYpos, hZU] with ω hL hLZ hY hZU
    have he := (cpow_common_envelope (L ω) (Z ω) (Y ω) (U ω) lo hi p
      hL hLZ hY hZU hlo hhi hlop hphi).2
    simpa only [F, H, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using
      ENNReal.ofReal_le_ofReal he
  have ht := annular_threshold_estimate_ae P
    (fun ω => ENNReal.ofReal (Y ω)) (fun ω => ENNReal.ofReal (2 * ‖p‖) * H ω)
    (fun ω => ENNReal.ofReal 2 * H ω) F (ENNReal.measurable_ofReal.comp_aemeasurable hY)
    (aemeasurable_const.mul hH) (ENNReal.ofReal u) (ENNReal.ofReal_pos.mpr hu).ne'
    ENNReal.ofReal_ne_top m q hm hq hs hl
  have hd : (∫⁻ ω, ENNReal.ofReal (2 * ‖p‖) * H ω ∂P) =
      ENNReal.ofReal (2 * ‖p‖) * ∫⁻ ω, H ω ∂P :=
    lintegral_const_mul'' _ hH
  have hb : (∫⁻ ω, (ENNReal.ofReal 2 * H ω) ^ q ∂P) =
      (ENNReal.ofReal 2) ^ q * ∫⁻ ω, H ω ^ q ∂P := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]
    exact lintegral_const_mul'' _ (hH.pow_const q)
  simpa only [hd, hb, H, F, mul_assoc] using ht

end DOZZ.Proofs
