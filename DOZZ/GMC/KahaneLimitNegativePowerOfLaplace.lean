/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneMellinEnvelope

/-! Negative-moment comparison from lower Laplace integrals, with arbitrary ambient measures. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The negative-power limit comparison follows from the Laplace-transform comparison and does
not require `L¹` convergence. This is the negative-power part of `thm:limit-kahane`. -/
theorem kahane_limit_negative_power_of_laplace
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ℝ≥0) (Y : ΩY → ℝ≥0) (q : ℝ) (hq : 0 < q)
    (hLap : ∀ t : ℝ, 0 < t →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (X ω : ℝ))) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (Y ω : ℝ))) ∂PY) :
    (∫⁻ ω, ENNReal.rpow (X ω : ℝ≥0∞) (-q) ∂PX) ≤
      ∫⁻ ω, ENNReal.rpow (Y ω : ℝ≥0∞) (-q) ∂PY := by
  classical
  by_cases htop : (∫⁻ ω, ENNReal.rpow (Y ω : ℝ≥0∞) (-q) ∂PY) = ∞
  · rw [htop]
    exact le_top
  let fX : ΩX → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-q * (X ω : ℝ)))
  let fY : ΩY → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-q * (Y ω : ℝ)))
  have hfYfinite : (∫⁻ ω, fY ω ∂PY) ≠ ∞ := by
    apply ne_top_of_le_ne_top htop
    apply lintegral_mono
    intro ω
    change ENNReal.ofReal (Real.exp (-q * (Y ω : ℝ))) ≤ (Y ω : ℝ≥0∞) ^ (-q)
    simpa only [ENNReal.ofReal_coe_nnreal] using
      exp_neg_mul_le_negative_power q (Y ω : ℝ) hq (NNReal.coe_nonneg _)
  have hfXfinite : (∫⁻ ω, fX ω ∂PX) ≠ ∞ :=
    ne_top_of_le_ne_top hfYfinite (hLap q hq)
  obtain ⟨gX, hgX, hgfX, hEqX⟩ := exists_measurable_le_lintegral_eq PX fX
  obtain ⟨gY, hgY, hgfY, hEqY⟩ := exists_measurable_le_lintegral_eq PY fY
  have hgXfinite (ω : ΩX) : gX ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgfX ω)
  have hgYfinite (ω : ΩY) : gY ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgfY ω)
  have hMomentX : (∫⁻ ω, ENNReal.rpow (X ω : ℝ≥0∞) (-q) ∂PX) =
      ∫⁻ ω, mellinEnvelope q (gX ω) ∂PX := by
    calc
      _ = ∫⁻ ω, mellinEnvelope q (fX ω) ∂PX := by
        apply lintegral_congr
        intro ω
        change (X ω : ℝ≥0∞) ^ (-q) =
          mellinEnvelope q (ENNReal.ofReal (Real.exp (-q * (X ω : ℝ))))
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (mellinEnvelope_exp q (X ω : ℝ) hq (NNReal.coe_nonneg _)).symm
      _ = _ := lintegral_transform_eq_of_lower_envelope PX fX gX hgX hgfX hEqX hfXfinite
        (mellinEnvelope q) (inverseMellinEnvelope q) (mellinEnvelope_monotone q hq)
        (inverseMellinEnvelope_measurable q) (fun ω z hz =>
          ⟨inverseMellinEnvelope_le_exp q (X ω : ℝ) hq (NNReal.coe_nonneg _) z hz,
            (mellinEnvelope_inverse q hq z).ge⟩)
  have hMomentY : (∫⁻ ω, ENNReal.rpow (Y ω : ℝ≥0∞) (-q) ∂PY) =
      ∫⁻ ω, mellinEnvelope q (gY ω) ∂PY := by
    calc
      _ = ∫⁻ ω, mellinEnvelope q (fY ω) ∂PY := by
        apply lintegral_congr
        intro ω
        change (Y ω : ℝ≥0∞) ^ (-q) =
          mellinEnvelope q (ENNReal.ofReal (Real.exp (-q * (Y ω : ℝ))))
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (mellinEnvelope_exp q (Y ω : ℝ) hq (NNReal.coe_nonneg _)).symm
      _ = _ := lintegral_transform_eq_of_lower_envelope PY fY gY hgY hgfY hEqY hfYfinite
        (mellinEnvelope q) (inverseMellinEnvelope q) (mellinEnvelope_monotone q hq)
        (inverseMellinEnvelope_measurable q) (fun ω z hz =>
          ⟨inverseMellinEnvelope_le_exp q (Y ω : ℝ) hq (NNReal.coe_nonneg _) z hz,
            (mellinEnvelope_inverse q hq z).ge⟩)
  have hExp (m t : ℝ) : ENNReal.ofReal (Real.exp (-q * m)) ^ (t / q) =
      ENNReal.ofReal (Real.exp (-t * m)) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    field_simp
  have horder (t : ℝ) (ht : 0 < t) : (∫⁻ ω, gX ω ^ (t / q) ∂PX) ≤
      ∫⁻ ω, gY ω ^ (t / q) ∂PY := by
    rw [← lintegral_rpow_eq_of_lower_envelope PX fX gX hgX hgfX hEqX hfXfinite _ (div_pos ht hq),
      ← lintegral_rpow_eq_of_lower_envelope PY fY gY hgY hgfY hEqY hfYfinite _ (div_pos ht hq)]
    simp only [fX, fY, hExp]
    exact hLap t ht
  rw [hMomentX, hMomentY,
    lintegral_mellinEnvelope_eq PX gX hgX hgXfinite (lt_top_iff_ne_top.mpr (hEqX ▸ hfXfinite)) q hq,
    lintegral_mellinEnvelope_eq PY gY hgY hgYfinite (lt_top_iff_ne_top.mpr (hEqY ▸ hfYfinite)) q hq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_mul_of_nonneg_left (horder t ht) (by positivity)



end DOZZ.Proofs
