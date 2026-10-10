/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedUniformLower

/-! Every negative order is available for the common fixed-disk lower mass. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Multiplying a fixed positive-radius disk mass by any positive finite constant preserves
all its nonpositive moments. -/
theorem scaled_disk_negative_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1 / 8) (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (t : ℝ) (ht : t ≤ 0) :
    (∫⁻ ω, (c * M ω (Metric.ball z r)) ^ t ∂P) < ⊤ := by
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
    (Metric.ball z r) Metric.isOpen_ball.measurableSet
  have hi := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM z r hr hrsmall t
    (lt_of_le_of_lt ht (by positivity : (0 : ℝ) < 4 / γ ^ 2))
  simp_rw [ennreal_mul_rpow_of_ne_zero_ne_top _ _ hc hc' t]
  rw [lintegral_const_mul'' _ (hm.pow_const t)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc hc').lt_top hi

end DOZZ.Proofs
