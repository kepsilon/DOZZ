/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ProbabilityPullback
public import DOZZ.Correlations.Tails.CompactPinMoment

/-! The copied-pin compact-test limit on the actual product probability space. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- Gaussian marginal moments control exponential moments of a pin difference even when
its two operands are correlated. -/
theorem pin_difference_exp_abs_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U V : Ω → ℝ)
    (hU : HasGaussianLaw U P) (hV : HasGaussianLaw V P)
    (hmU : (∫ ω, U ω ∂P) = 0) (hmV : (∫ ω, V ω ∂P) = 0) (l : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|U ω-V ω|)) ∂P) < ⊤ := by
  let a := max l 0
  have ha : 0 ≤ a := le_max_right _ _
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (l*|U ω-V ω|)) ≤
      ENNReal.ofReal (Real.exp (a*|U ω|)) * ENNReal.ofReal (Real.exp (a*|V ω|)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ a * |U ω-V ω| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ a * (|U ω|+|V ω|) := mul_le_mul_of_nonneg_left (abs_sub _ _) ha
      _ = _ := by ring
  exact ((lintegral_mono hpoint).trans
    (gaussian_product_lintegral_exp_abs_le P U V hU hV hmU hmV
      (variance U P) (variance V P) le_rfl le_rfl a)).trans_lt ENNReal.ofReal_lt_top

/-- Actual source GMC cutoffs converge with the copied pin difference in a compact
exponential test. The source field `Y` may be the translated and re-pinned field; no
independence between that field and the first pin is assumed. -/
theorem actual_copied_pin_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (Y : Ω → Distr) (Yc : Ω → ℂ → ℝ → ℝ)
    (hY : IsEquatorGFF P Y) (hYc : IsCircleAverage P Y Yc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P Y γ N)
    (z : ℂ) (hz : 2 ≤ ‖z‖)
    (f c : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    TendstoInMeasure (P.prod P)
      (fun (n : ℕ) q => ∫ x, f x * Real.exp (c x * (Xc q.2 z 0-Xc q.1 z 0))
        ∂regularizedGMC P Yc γ n q.1)
      atTop (fun q => ∫ x, f x * Real.exp (c x * (Xc q.2 z 0-Xc q.1 z 0)) ∂N q.1) := by
  let : IsProbabilityMeasure P := hX.1
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (P.prod P) P := measurePreserving_fst
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst Y hY
  have hYc' := isCircleAverage_measurePreserving P (P.prod P) Prod.fst hfst Y Yc hY hYc
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst Y hY γ N hN
  have hpin : Measurable (fun ω => Xc ω z 0) :=
    (hc.1 0).comp (measurable_id.prodMk measurable_const)
  have hθ : Measurable (fun q : Ω × Ω => Xc q.2 z 0-Xc q.1 z 0) :=
    (hpin.comp measurable_snd).sub (hpin.comp measurable_fst)
  obtain ⟨hG, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hg := hG.hasGaussianLaw_eval (z, (0 : ℝ))
  have hNlaw : HasLaw (fun ω => Xc ω z 0)
      (gaussianReal 0 (2 * Real.log ‖z‖).toNNReal) P := by
    refine ⟨hg.aemeasurable, ?_⟩
    rw [hg.map_eq_gaussianReal, hm, ← covariance_self hg.aemeasurable,
      offCenter_origin_variance X Xc hX hc z hz]
  have h1 := hNlaw.comp (measurePreserving_fst (μ := P) (ν := P)).hasLaw
  have h2 := hNlaw.comp (measurePreserving_snd (μ := P) (ν := P)).hasLaw
  have hmean1 : (∫ q : Ω × Ω, Xc q.1 z 0 ∂P.prod P) = 0 := by
    simpa only [Function.comp_def, integral_id_gaussianReal] using h1.integral_eq
  have hmean2 : (∫ q : Ω × Ω, Xc q.2 z 0 ∂P.prod P) = 0 := by
    simpa only [Function.comp_def, integral_id_gaussianReal] using h2.integral_eq
  have h := gmc_correlated_exponential_test_limit (P.prod P) (Y ∘ Prod.fst)
    hY' (Yc ∘ Prod.fst) hYc' γ hγ hγ2 (N ∘ Prod.fst) hN' f c hfc _ hθ
      (fun l => pin_difference_exp_abs_moment (P.prod P) _ _
        h2.hasGaussianLaw h1.hasGaussianLaw hmean2 hmean1 l)
  simp only [regularizedGMC_measurePreserving P (P.prod P) Prod.fst hfst Y Yc hYc] at h
  simpa only [Function.comp_def] using h


end DOZZ.Proofs
