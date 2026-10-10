/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.ClippedDyadic
public import DOZZ.GMC.Moments.LimitFatou
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# The first sharp positive-moment induction step

The finite-cutoff root identity is assembled with the inner cutoff disk, the bounded
outer mass, and the geometric dyadic sum. All constants are independent of the root
and cutoff. The input at order `p-1` in this first step is the proved first moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The exact polynomial exponent at the order used inside the rooted mass. -/
noncomputable def gmcRootOrderExponent (γ q : ℝ) : ℝ :=
  2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2

/-- The sharp exponent remaining after the singular covariance insertion. -/
noncomputable def gmcRootAnnularExponent (γ q : ℝ) : ℝ := gmcRootOrderExponent γ q - γ ^ 2 * q

/-- The root annular exponent is strictly positive at the next subcritical order. -/
theorem gmcRootAnnularExponent_pos
    (γ q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2) :
    0 < gmcRootAnnularExponent γ q := by
  have hc : (q + 1) * γ ^ 2 < 4 := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hcrit
  have hp : 0 < 2 - γ ^ 2 * (q + 1) / 2 := by nlinarith
  have he : gmcRootAnnularExponent γ q = q * (2 - γ ^ 2 * (q + 1) / 2) := by
    unfold gmcRootAnnularExponent gmcRootOrderExponent
    ring
  rw [he]
  exact mul_pos hq hp

/-- One finite reference first-moment constant for the entire dyadic calculation. -/
noncomputable def gmcRootSubunitReference (R : ℝ) : ℝ≥0∞ :=
  1 + gmcReferenceMeasure (Metric.ball (0 : ℂ) R)

/-- Explicit innermost-disk comparison constant after discarding only a bounded positive
power of the cutoff radius. -/
noncomputable def gmcRootInnerConstant (γ q R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (gmcRootOrderExponent γ q) * R ^ (-gmcRootOrderExponent γ q))

/-- Explicit geometric-series comparison constant for the active dyadic scales. -/
noncomputable def gmcRootDyadicConstant (γ q R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)))⁻¹

/-- The complete clipped-mass moment constant includes all three source pieces. -/
noncomputable def gmcRootClippedConstant (γ q R : ℝ) : ℝ≥0∞ :=
  (gmcRootInnerConstant γ q R + ENNReal.ofReal (R ^ (-γ ^ 2 * q)) +
    gmcRootDyadicConstant γ q R) * gmcRootSubunitReference R

/-- The reference factor is finite on every spatial radius. -/
theorem gmcRootSubunitReference_lt_top (R : ℝ) : gmcRootSubunitReference R < ∞ := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  exact ENNReal.add_lt_top.mpr ⟨by simp, measure_lt_top _ _⟩

/-- The dyadic factor is finite at the strict subcritical threshold. -/
theorem gmcRootDyadicConstant_lt_top
    (γ q R : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2) :
    gmcRootDyadicConstant γ q R < ∞ := by
  have ha : ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)) < 1 :=
    gmc_clipped_dyadic_ratio_lt_one γ q hγ hq hcrit
  have hd : 1 - ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)) ≠ 0 := by
    intro h
    exact (not_le_of_gt ha) (tsub_eq_zero_iff_le.mp h)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hd))

/-- Thus the complete clipped-mass constant is finite before applying the root identity. -/
theorem gmcRootClippedConstant_lt_top
    (γ q R : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2) :
    gmcRootClippedConstant γ q R < ∞ := by
  unfold gmcRootClippedConstant
  exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩,
      gmcRootDyadicConstant_lt_top γ q R hγ hq hcrit⟩) (gmcRootSubunitReference_lt_top R)

/-- The inner cutoff disk has a single moment constant independent of cutoff and root. -/
theorem regularizedGMC_root_inner_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hq1 : q ≤ 1) (hcrit : q + 1 < 4 / γ ^ 2)
    {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hcut : 2 * Real.exp (-t) ≤ R)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (ENNReal.ofReal ((Real.exp (-t)) ^ (-γ ^ 2)) *
      regularizedGMC P Xc γ t ω (Metric.ball u (2 * Real.exp (-t)))) ^ q ∂P) ≤
        gmcRootInnerConstant γ q R * gmcRootSubunitReference R := by
  have h := regularizedGMC_inner_clipped_subunit_moment_bound P X hX Xc hXc γ q hq hq1
    hR hRsmall hcut u hu
  have hp : (Real.exp (-t)) ^ (gmcRootAnnularExponent γ q) ≤ 1 :=
    Real.rpow_le_one (Real.exp_nonneg _) (by linarith)
      (gmcRootAnnularExponent_pos γ q hγ hq hcrit).le
  have hcoef : ((2 : ℝ) ^ (gmcRootOrderExponent γ q) * R ^ (-gmcRootOrderExponent γ q)) *
      (Real.exp (-t)) ^ (gmcRootAnnularExponent γ q) ≤
        (2 : ℝ) ^ (gmcRootOrderExponent γ q) * R ^ (-gmcRootOrderExponent γ q) := by
    exact (mul_le_mul_of_nonneg_left hp (mul_nonneg
      (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hR.le _))).trans_eq (mul_one _)
  exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)

/-- The active dyadic sum has a single moment constant independent of cutoff and root. -/
theorem regularizedGMC_root_dyadic_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (∑' n : ℕ, gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
      γ R (Real.exp (-t)) u n) ^ q ∂P) ≤
        gmcRootDyadicConstant γ q R * gmcRootSubunitReference R := by
  have hm (n : ℕ) : AEMeasurable (fun ω =>
      (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) u n) ^ q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (measurable_regularizedGMC_clipped_dyadic_term P X hX Xc hXc γ R t u n).aemeasurable
  calc
    _ ≤ ∫⁻ ω, ∑' n : ℕ, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
        γ R (Real.exp (-t)) u n) ^ q ∂P := by
      apply lintegral_mono
      intro ω
      exact ennreal_rpow_tsum_le_tsum_rpow _ hq hq1
    _ = ∑' n : ℕ, ∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
        γ R (Real.exp (-t)) u n) ^ q ∂P := lintegral_tsum hm
    _ ≤ _ := regularizedGMC_clipped_dyadic_subunit_moment_sum_bound P X hX Xc hXc γ q hq hq1
      hR hRsmall u hu

/-- The complete clipped insertion has the common bound obtained from all three actual pieces. -/
theorem regularizedGMC_root_clipped_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hq1 : q ≤ 1) (hcrit : q + 1 < 4 / γ ^ 2)
    {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hcut : 2 * Real.exp (-t) ≤ R)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) R,
      ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-t))) ^ (-γ ^ 2))
        ∂regularizedGMC P Xc γ t ω) ^ q ∂P) ≤ gmcRootClippedConstant γ q R := by
  let I : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((Real.exp (-t)) ^ (-γ ^ 2)) *
    regularizedGMC P Xc γ t ω (Metric.ball u (2 * Real.exp (-t)))
  let O : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (R ^ (-γ ^ 2)) *
    regularizedGMC P Xc γ t ω (Metric.ball 0 R)
  let S : Ω → ℝ≥0∞ := fun ω => ∑' n : ℕ,
    gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) u n
  have hI : Measurable (fun ω => (I ω) ^ q) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_const.mul
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc γ t)))
  have hO : Measurable (fun ω => (O ω) ^ q) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_const.mul
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc γ t)))
  have hb : (∫⁻ ω, (O ω) ^ q ∂P) ≤
      ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * gmcRootSubunitReference R := by
    have hc : 0 < R ^ (-γ ^ 2) := Real.rpow_pos_of_pos hR _
    simp only [O, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      ENNReal.ofReal_rpow_of_pos hc, ← Real.rpow_mul hR.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (regularizedGMC_subunit_moment_uniform P X hX Xc hXc γ t q
      hq.le hq1 (Metric.ball 0 R) Metric.isOpen_ball.measurableSet)
  calc
    _ ≤ ∫⁻ ω, (I ω) ^ q + (O ω) ^ q + (S ω) ^ q ∂P := by
      apply lintegral_mono
      intro ω
      have h := ENNReal.rpow_le_rpow (gmc_clipped_mass_le_dyadic
        (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) hR (Real.exp_pos _) u
          (Metric.ball 0 R)) hq.le
      exact h.trans ((ENNReal.rpow_add_le_add_rpow (I ω + O ω) (S ω) hq.le hq1).trans
        (add_le_add (ENNReal.rpow_add_le_add_rpow (I ω) (O ω) hq.le hq1) le_rfl))
    _ = (∫⁻ ω, (I ω) ^ q ∂P) + (∫⁻ ω, (O ω) ^ q ∂P) + (∫⁻ ω, (S ω) ^ q ∂P) := by
      have hIO : AEMeasurable (fun ω => (I ω) ^ q + (O ω) ^ q) P := (hI.add hO).aemeasurable
      rw [lintegral_add_left' hIO, lintegral_add_left' hI.aemeasurable]
    _ ≤ (gmcRootInnerConstant γ q R * gmcRootSubunitReference R) +
        (ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * gmcRootSubunitReference R) +
          (gmcRootDyadicConstant γ q R * gmcRootSubunitReference R) :=
      add_le_add (add_le_add (regularizedGMC_root_inner_moment_uniform P X hX Xc hXc γ q
        hγ hq hq1 hcrit hR hRsmall hcut u hu) hb)
          (regularizedGMC_root_dyadic_moment_uniform P X hX Xc hXc γ q hq hq1 hR hRsmall u hu)
    _ = _ := by unfold gmcRootClippedConstant; rw [add_mul, add_mul]

/-- Applying the proved finite-cutoff root identity closes the fine-cutoff reference moments
for every `1<p<=2` in the strict subcritical range. No higher-moment premise is supplied. -/
theorem regularizedGMC_reference_positive_moment_fine_upto_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2) (hcrit : p < 4 / γ ^ 2)
    {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (ht : 0 ≤ t)
    (hcut : 2 * Real.exp (-t) ≤ R) :
    gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) *
        (gmcRootClippedConstant γ (p - 1) R * gmcReferenceMeasure (Metric.ball 0 R)) := by
  have hq : 0 < p - 1 := by linarith
  have hq1 : p - 1 ≤ 1 := by linarith
  have hc : (p - 1) + 1 < 4 / γ ^ 2 := by simpa only [sub_add_cancel] using hcrit
  have hchart : ∀ x ∈ Metric.ball (0 : ℂ) R, ‖x‖ ≤ R := by
    intro x hx
    exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  have h := regularizedGMC_positive_moment_le_clipped P X hX Xc hXc γ R t p hR.le ht hp
    (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart
  change gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ _ at h
  have hbound : (∫⁻ u in Metric.ball (0 : ℂ) R, ∫⁻ ω,
      (∫⁻ x in Metric.ball (0 : ℂ) R, ENNReal.ofReal
        ((max ‖x - u‖ (Real.exp (-t))) ^ (-γ ^ 2)) ∂regularizedGMC P Xc γ t ω) ^ (p - 1)
          ∂P ∂gmcReferenceMeasure) ≤
        gmcRootClippedConstant γ (p - 1) R * gmcReferenceMeasure (Metric.ball 0 R) := by
    calc
      _ ≤ ∫⁻ _u in Metric.ball (0 : ℂ) R, gmcRootClippedConstant γ (p - 1) R ∂gmcReferenceMeasure := by
        apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
        intro u hu
        exact regularizedGMC_root_clipped_moment_uniform P X hX Xc hXc γ (p - 1) hγ hq hq1 hc
          hR hRsmall hcut u (hchart u hu)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact h.trans (mul_le_mul' le_rfl hbound)

/-- Coarse and fine cutoff estimates together give one uniform reference bound at every
cutoff `t>=0`, for every subcritical order in the first induction interval. -/
theorem regularizedGMC_reference_positive_moment_uniform_upto_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let T : ℝ := Real.log (2 / R)
  let F : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) *
    (gmcRootClippedConstant γ (p - 1) R * gmcReferenceMeasure (Metric.ball 0 R))
  let B : ℝ≥0∞ := (gmcReferenceMeasure (Metric.ball (0 : ℂ) R)) ^ p *
    ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R)))
  have hF : F < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (gmcRootClippedConstant_lt_top γ (p - 1) R hγ (by linarith)
      (by simpa only [sub_add_cancel] using hcrit)) (measure_lt_top _ _))
  have hB : B < ∞ := ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)))
    ENNReal.ofReal_lt_top
  refine ⟨F + B, ENNReal.add_lt_top.mpr ⟨hF, hB⟩, ?_⟩
  intro t ht
  by_cases hcut : 2 * Real.exp (-t) ≤ R
  · exact (regularizedGMC_reference_positive_moment_fine_upto_two P X hX Xc hXc γ p hγ hp hp2
      hcrit hR hRsmall ht hcut).trans (le_add_of_nonneg_right zero_le)
  · have htT : t ≤ T := by
      have hr : 0 < 2 / R := div_pos (by norm_num) hR
      have he : Real.exp (-T) = R / 2 := by
        dsimp [T]
        rw [Real.exp_neg, Real.exp_log hr, inv_div]
      have hexp : Real.exp (-T) < Real.exp (-t) := by rw [he]; linarith
      exact (neg_lt_neg_iff.mp (Real.exp_lt_exp.mp hexp)).le
    have hchart : ∀ x ∈ Metric.ball (0 : ℂ) R, ‖x‖ ≤ R := by
      intro x hx
      exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    exact (regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ R T p hR.le hp.le
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart t ht htT).trans
        (le_add_of_nonneg_left zero_le)


/-- The continuous ball approximants have integral no larger than the actual open-ball mass. -/
theorem gmc_ball_approx_ofReal_integral_le_mass
    (μ : Measure ℂ) [IsFiniteMeasure μ] (z : ℂ) (R : ℝ) (n : ℕ) :
    ENNReal.ofReal (∫ x, openBallApprox z R n x ∂μ) ≤ μ (Metric.ball z R) := by
  have hnonneg (x : ℂ) : 0 ≤ openBallApprox z R n x := (openBallApproxFun_bounds z R n x).1
  have hpoint (x : ℂ) : ENNReal.ofReal (openBallApprox z R n x) ≤
      (Metric.ball z R).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ Metric.ball z R
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_one.mpr (openBallApproxFun_bounds z R n x).2
    · have hn : R ≤ ‖x - z‖ := le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
      have hm : min 1 ((n : ℝ) * (R - ‖x - z‖)) ≤ 0 :=
        (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr hn))
      change ENNReal.ofReal (max 0 (min 1 ((n : ℝ) * (R - ‖x - z‖)))) ≤ _
      rw [max_eq_left hm, ENNReal.ofReal_zero]
      exact zero_le
  rw [ofReal_integral_eq_lintegral_ofReal ((openBallApprox z R n).integrable (μ := μ)) (ae_of_all μ hnonneg)]
  have h := lintegral_mono (μ := μ) hpoint
  rwa [lintegral_indicator_const Metric.isOpen_ball.measurableSet, one_mul] at h

/-- The first sharp positive-moment induction interval passes to every GMC version. Two Fatou
passages use only the literal weak test-integral convergence in `IsGMCOf`. -/
theorem gmc_reference_positive_moment_finite_upto_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2) (hcrit : p < 4 / γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    gmcMassMoment P M (Metric.ball 0 R) p < ∞ := by
  let _ := hX.1
  obtain ⟨Xc, hXc, hlimit⟩ := hM.2
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform_upto_two
    P X hX Xc hXc γ p hγ hp hp2 hcrit hR hRsmall
  let f : ℕ → BoundedContinuousFunction ℂ ℝ := fun k => openBallApprox 0 R k
  let F : ℕ → Ω → ℝ := fun k ω => ∫ x, f k x ∂M ω
  have hcut (k n : ℕ) : AEMeasurable
      (fun ω => ∫ x, f k x ∂regularizedGMC P Xc γ n ω) P := by
    have hzero : ∀ x, x ∉ Metric.closedBall (0 : ℂ) R → f k x = 0 :=
      boundedContinuousFunction_eq_zero_off_tsupport_subset (f k) (Metric.closedBall 0 R)
        (openBallApprox_tsupport_subset 0 R k)
    have hunit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1 := by
      intro x hx
      have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      linarith
    exact regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ n
      (Metric.closedBall 0 R) Metric.isClosed_closedBall.measurableSet hunit
        (f k) (f k).continuous.measurable hzero
  have hconv (k : ℕ) : TendstoInMeasure P
      (fun n : ℕ => fun ω => ∫ x, f k x ∂regularizedGMC P Xc γ n ω) atTop (F k) :=
    (hlimit (f k)).comp tendsto_natCast_atTop_atTop
  have hF (k : ℕ) : AEMeasurable (F k) P := (hconv k).aemeasurable (hcut k)
  have hFn (k : ℕ) (ω : Ω) : 0 ≤ F k ω :=
    integral_nonneg (fun x => (openBallApproxFun_bounds 0 R k x).1)
  have hfirst (k : ℕ) : (∫⁻ ω, ENNReal.ofReal (F k ω) ^ p ∂P) ≤ C := by
    have hmeas (n : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal
        (max (∫ x, f k x ∂regularizedGMC P Xc γ n ω) 0) ^ p) P := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (ENNReal.measurable_ofReal.comp_aemeasurable ((hcut k n).max aemeasurable_const))
    have hb (n : ℕ) : (∫⁻ ω, ENNReal.ofReal
        (max (∫ x, f k x ∂regularizedGMC P Xc γ n ω) 0) ^ p ∂P) ≤ C := by
      have hn : (∫⁻ ω, ENNReal.ofReal
          (max (∫ x, f k x ∂regularizedGMC P Xc γ n ω) 0) ^ p ∂P) ≤
          gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball 0 R) p := by
        apply lintegral_mono_ae
        filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hfin
        let _ := hfin
        have hnonneg : 0 ≤ ∫ x, f k x ∂regularizedGMC P Xc γ n ω :=
          integral_nonneg (fun x => (openBallApproxFun_bounds 0 R k x).1)
        rw [max_eq_left hnonneg]
        exact ENNReal.rpow_le_rpow
          (gmc_ball_approx_ofReal_integral_le_mass (regularizedGMC P Xc γ n ω) 0 R k) (by linarith)
      exact hn.trans (hbound n (Nat.cast_nonneg n))
    exact lintegral_ennreal_rpow_le_of_tendstoInMeasure P _ (F k) p C (hconv k) hmeas
      (ae_of_all P (hFn k)) hb
  let G : Ω → ℝ := fun ω => (M ω (Metric.ball 0 R)).toReal
  have hseq : TendstoInMeasure P F atTop G := by
    apply tendstoInMeasure_of_tendsto_ae (fun k => (hF k).aestronglyMeasurable)
    filter_upwards with ω
    let _ := hM.1 ω
    simpa only [F, f, G, measureReal_def] using openBallApprox_integral_tendsto 0 R (M ω)
  have hpow (k : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal (max (F k ω) 0) ^ p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable ((hF k).max aemeasurable_const))
  have hb (k : ℕ) : (∫⁻ ω, ENNReal.ofReal (max (F k ω) 0) ^ p ∂P) ≤ C := by
    have he : (fun ω => ENNReal.ofReal (max (F k ω) 0) ^ p) =
        (fun ω => ENNReal.ofReal (F k ω) ^ p) := by
      funext ω
      rw [max_eq_left (hFn k ω)]
    rw [he]
    exact hfirst k
  have hf := lintegral_ennreal_rpow_le_of_tendstoInMeasure P F G p C hseq hpow
    (ae_of_all P (fun ω => ENNReal.toReal_nonneg)) hb
  have he : (∫⁻ ω, ENNReal.ofReal (G ω) ^ p ∂P) = gmcMassMoment P M (Metric.ball 0 R) p := by
    apply lintegral_congr
    intro ω
    let _ := hM.1 ω
    change ENNReal.ofReal ((M ω (Metric.ball 0 R)).toReal) ^ p =
      ENNReal.rpow (M ω (Metric.ball 0 R)) p
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  change (∫⁻ ω, ENNReal.ofReal (G ω) ^ p ∂P) ≤ C at hf
  rw [he] at hf
  exact hf.trans_lt hC

/-- Every small affine disk in the exact chart inherits the proved limiting positive moment
range up to order two. This consumes the all-orders exact-scale law without extra inputs. -/
theorem gmc_local_positive_ball_moment_finite_upto_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ p : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hp : 1 < p) (hp2 : p ≤ 2) (hcrit : p < 4 / γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R s : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hs : 0 < s) (hsR : s ≤ R)
    (z : ℂ) (hz : ‖z‖ + s < 1) :
    gmcMassMoment P M (Metric.ball z s) p < ∞ := by
  have he : s / R * R = s := div_mul_cancel₀ s hR.ne'
  have hiff := gmc_affine_openBall_moment_finite_iff P X hX γ hγ hγ2 M hM
    (a := z) (c := s / R) (R := R) (div_pos hs hR) ((div_le_one hR).mpr hsR)
    hR (by linarith) (by simpa only [he] using hz) p
  rw [he] at hiff
  exact hiff.mpr (gmc_reference_positive_moment_finite_upto_two P X hX γ p hγ hp hp2 hcrit M hM
    hR hRsmall)

end DOZZ.Proofs
