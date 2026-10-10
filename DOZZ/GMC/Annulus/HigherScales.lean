/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.PositiveBase
public import DOZZ.GMC.Annulus.BallCover
public import DOZZ.Brownian.Lateral.UpperConditionedBlocks

/-!
# Higher-order clipped-scale moment estimates

At order q above one the dyadic pieces are assembled with Minkowski. The reference
moment input is exactly the preceding induction interval, at the same charge and
source circle field. No spatial independence or limiting rooted identity is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A preceding cutoff-uniform reference estimate transfers to every active local ball.
The rescaled reference cutoff is nonnegative because its circle radius is at most R. -/
theorem regularizedGMC_local_ball_moment_upper_of_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞)
    (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) q ≤ C)
    {s t : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hcut : Real.exp (-t) ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball z s) q ≤
      ENNReal.ofReal ((s / R) ^ (gmcRootOrderExponent γ q)) * C := by
  have hscaleCircle : Real.exp (-(t + Real.log (s / R))) = Real.exp (-t) * (R / s) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (s / R)),
      Real.exp_log (div_pos hs hR), inv_div]
  have hm : Real.exp (-t) * (R / s) ≤ R := by
    have h := mul_le_mul_of_nonneg_right hcut (div_nonneg hR.le hs.le)
    have he : s * (R / s) = R := by field_simp
    exact h.trans_eq he
  have hr : 0 ≤ t + Real.log (s / R) := by
    have he : Real.exp (-(t + Real.log (s / R))) ≤ 1 := by rw [hscaleCircle]; linarith
    exact neg_nonpos.mp (Real.exp_le_one_iff.mp he)
  have hbase : R + Real.exp (-t) * (R / s) ≤ 1 := by linarith
  have htarget : ‖z‖ + s + Real.exp (-t) ≤ 1 := by linarith
  rw [regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z hs hsR hR (by linarith)
    (by linarith) hbase htarget q]
  exact mul_le_mul' le_rfl (hRef _ hr)

/-- The actual active dyadic pieces carry the sharp geometric moment factor at arbitrary
positive order. The preceding reference bound is the only induction input. -/
theorem regularizedGMC_clipped_dyadic_moment_bound_of_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hq : 0 < q) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞)
    (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) q ≤ C)
    (t : ℝ) (u : ℂ) (hu : ‖u‖ ≤ R) (n : ℕ) :
    (∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
      γ R (Real.exp (-t)) u n) ^ q ∂P) ≤
      ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) *
        ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)) ^ n * C := by
  by_cases ha : Real.exp (-t) ≤ gmcDyadicRadius R n
  · have hn : 0 < gmcDyadicRadius R n := by unfold gmcDyadicRadius; positivity
    have hnR : gmcDyadicRadius R n ≤ R := by
      unfold gmcDyadicRadius
      apply (div_le_iff₀ (by positivity)).mpr
      calc
        R = R * 1 := (mul_one R).symm
        _ ≤ R * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le
    have hn1 : 0 < gmcDyadicRadius R (n + 1) := by unfold gmcDyadicRadius; positivity
    have hc : 0 < (gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2) := Real.rpow_pos_of_pos hn1 _
    have he : (∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
        γ R (Real.exp (-t)) u n) ^ q ∂P) =
        ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2 * q)) *
          gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball u (gmcDyadicRadius R n)) q := by
      simp only [gmcClippedDyadicTerm, ite_eq_left ha, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
        ENNReal.ofReal_rpow_of_pos hc, ← Real.rpow_mul hn1.le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    rw [he]
    have hb := regularizedGMC_local_ball_moment_upper_of_reference P X hX Xc hXc γ q hR
      hRsmall C hRef hn hnR ha u hu
    have h := mul_le_mul' (le_refl (ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2 * q)))) hb
    have hecoef := gmc_dyadic_weight_scale_eq_geometric γ q (gmcRootOrderExponent γ q) R hR n
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hn1.le _), hecoef,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)] at h
    exact h
  · simp only [gmcClippedDyadicTerm, ite_eq_right ha, ENNReal.zero_rpow_of_pos hq, lintegral_zero]
    exact zero_le

/-- The explicit higher-order dyadic constant obtained by Minkowski and a geometric series. -/
noncomputable def gmcRootHigherDyadicConstant (γ q R : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  (ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) ^ (1 / q) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)) ^ (1 / q))⁻¹ * C ^ (1 / q)) ^ q

/-- The higher-order geometric constant is finite at the strict subcritical next order. -/
theorem gmcRootHigherDyadicConstant_lt_top
    (γ q R : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2)
    (C : ℝ≥0∞) (hC : C < ∞) : gmcRootHigherDyadicConstant γ q R C < ∞ := by
  have ha := ENNReal.rpow_lt_one (gmc_clipped_dyadic_ratio_lt_one γ q hγ hq hcrit) (one_div_pos.mpr hq)
  have hd : 1 - ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)) ^ (1 / q) ≠ 0 := by
    intro h
    exact (not_le_of_gt ha) (tsub_eq_zero_iff_le.mp h)
  unfold gmcRootHigherDyadicConstant
  apply lt_top_iff_ne_top.mpr
  apply ENNReal.rpow_ne_top_of_nonneg hq.le
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.mpr hq).le ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr hd)) (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.mpr hq).le hC.ne)

/-- Actual Minkowski assembly of the active clipped dyadic pieces at higher orders. -/
theorem regularizedGMC_root_dyadic_higher_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hq : 1 ≤ q) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞)
    (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) q ≤ C)
    (t : ℝ) (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (∑' n : ℕ, gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
      γ R (Real.exp (-t)) u n) ^ q ∂P) ≤ gmcRootHigherDyadicConstant γ q R C := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) u n
  let a : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q))
  let D : ℝ≥0∞ := ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q))
  have hF (n : ℕ) : AEMeasurable (F n) P :=
    (measurable_regularizedGMC_clipped_dyadic_term P X hX Xc hXc γ R t u n).aemeasurable
  have hb (n : ℕ) : (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q) ≤
      D ^ (1 / q) * (a ^ (1 / q)) ^ n * C ^ (1 / q) := by
    have h := ENNReal.rpow_le_rpow
      (regularizedGMC_clipped_dyadic_moment_bound_of_reference P X hX Xc hXc γ q hq0
        hR hRsmall C hRef t u hu n) (one_div_pos.mpr hq0).le
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hq0).le,
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hq0).le] at h
    have he : (a ^ n) ^ (1 / q) = (a ^ (1 / q)) ^ n := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 1
      ring
    exact h.trans_eq (by rw [he])
  have hs : (∑' n : ℕ, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q)) ≤
      D ^ (1 / q) * (1 - a ^ (1 / q))⁻¹ * C ^ (1 / q) := by
    have h := ENNReal.tsum_le_tsum hb
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric] at h
    exact h
  exact (lintegral_tsum_rpow_le_root_moments_power P F hF q hq).trans
    (ENNReal.rpow_le_rpow hs hq0.le)

/-- The inner cutoff disk also consumes exactly the preceding uniform reference bound. -/
theorem regularizedGMC_root_inner_moment_uniform_of_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞)
    (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) q ≤ C)
    (t : ℝ) (hcut : 2 * Real.exp (-t) ≤ R) (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (ENNReal.ofReal ((Real.exp (-t)) ^ (-γ ^ 2)) *
      regularizedGMC P Xc γ t ω (Metric.ball u (2 * Real.exp (-t)))) ^ q ∂P) ≤
        gmcRootInnerConstant γ q R * C := by
  let δ := Real.exp (-t)
  let ξ := gmcRootOrderExponent γ q
  have hδ : 0 < δ := Real.exp_pos _
  have hc : 0 < δ ^ (-γ ^ 2) := Real.rpow_pos_of_pos hδ _
  have he : (∫⁻ ω, (ENNReal.ofReal (δ ^ (-γ ^ 2)) *
      regularizedGMC P Xc γ t ω (Metric.ball u (2 * δ))) ^ q ∂P) =
      ENNReal.ofReal (δ ^ (-γ ^ 2 * q)) *
        gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball u (2 * δ)) q := by
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.ofReal_rpow_of_pos hc,
      ← Real.rpow_mul hδ.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [he]
  have hb := regularizedGMC_local_ball_moment_upper_of_reference P X hX Xc hXc γ q hR
    hRsmall C hRef (mul_pos (by norm_num) hδ) hcut (by dsimp [δ]; linarith [Real.exp_pos (-t)]) u hu
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (δ ^ (-γ ^ 2 * q)))) hb
  have hecoef : δ ^ (-γ ^ 2 * q) * ((2 * δ) / R) ^ ξ =
      (2 : ℝ) ^ ξ * R ^ (-ξ) * δ ^ (ξ - γ ^ 2 * q) := by
    rw [Real.div_rpow (by positivity) hR.le, Real.mul_rpow (by norm_num) hδ.le,
      div_eq_mul_inv, ← Real.rpow_neg hR.le, sub_eq_add_neg, Real.rpow_add hδ]
    ring_nf
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hecoef] at h
  have hp : δ ^ (ξ - γ ^ 2 * q) ≤ 1 := Real.rpow_le_one hδ.le (by dsimp [δ]; linarith)
    (gmcRootAnnularExponent_pos γ q hγ hq hcrit).le
  have hcoef : (2 : ℝ) ^ ξ * R ^ (-ξ) * δ ^ (ξ - γ ^ 2 * q) ≤ (2 : ℝ) ^ ξ * R ^ (-ξ) :=
    (mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hR.le _))).trans_eq (mul_one _)
  exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)

/-- A finite three-piece power bound for the inner, outer and dyadic contributions. -/
theorem gmc_root_three_piece_rpow_le (a b c : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (a + b + c) ^ q ≤ (3 : ℝ≥0∞) ^ q * (a ^ q + b ^ q + c ^ q) := by
  let f : Fin 3 → ℝ≥0∞ := ![a, b, c]
  have h := ennreal_finset_sum_rpow_le_card_rpow_sum (Finset.univ : Finset (Fin 3))
    ⟨0, Finset.mem_univ 0⟩ f q hq
  simpa [f, Fin.sum_univ_succ, add_assoc] using h

/-- Explicit complete clipped-root constant in the higher-order step. -/
noncomputable def gmcRootHigherClippedConstant (γ q R : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ q * (gmcRootInnerConstant γ q R * C +
    ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * C + gmcRootHigherDyadicConstant γ q R C)

/-- The higher-order clipped-root constant is finite from the preceding finite reference bound. -/
theorem gmcRootHigherClippedConstant_lt_top
    (γ q R : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2)
    (C : ℝ≥0∞) (hC : C < ∞) : gmcRootHigherClippedConstant γ q R C < ∞ := by
  unfold gmcRootHigherClippedConstant
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hq.le (by simp)))
    (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC⟩,
        gmcRootHigherDyadicConstant_lt_top γ q R hγ hq hcrit C hC⟩)

/-- Complete higher-order clipped-mass assembly. No independence between its spatial pieces
is assumed: a finite-sum bound handles three pieces, and Minkowski handles the dyadic sum. -/
theorem regularizedGMC_root_clipped_higher_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ q : ℝ) (hγ : 0 < γ) (hq : 1 ≤ q) (hcrit : q + 1 < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞)
    (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) q ≤ C)
    (t : ℝ) (ht : 0 ≤ t) (hcut : 2 * Real.exp (-t) ≤ R) (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) R,
      ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-t))) ^ (-γ ^ 2))
        ∂regularizedGMC P Xc γ t ω) ^ q ∂P) ≤ gmcRootHigherClippedConstant γ q R C := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
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
  have hb : (∫⁻ ω, (O ω) ^ q ∂P) ≤ ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * C := by
    have hc : 0 < R ^ (-γ ^ 2) := Real.rpow_pos_of_pos hR _
    simp only [O, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ENNReal.ofReal_rpow_of_pos hc, ← Real.rpow_mul hR.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (hRef t ht)
  calc
    _ ≤ ∫⁻ ω, (3 : ℝ≥0∞) ^ q * ((I ω) ^ q + (O ω) ^ q + (S ω) ^ q) ∂P := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.rpow_le_rpow (gmc_clipped_mass_le_dyadic
        (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) hR (Real.exp_pos _) u
          (Metric.ball 0 R)) hq0.le).trans (gmc_root_three_piece_rpow_le (I ω) (O ω) (S ω) q hq0.le)
    _ = (3 : ℝ≥0∞) ^ q * ((∫⁻ ω, (I ω) ^ q ∂P) + (∫⁻ ω, (O ω) ^ q ∂P) +
        (∫⁻ ω, (S ω) ^ q ∂P)) := by
      have hIO : AEMeasurable (fun ω => (I ω) ^ q + (O ω) ^ q) P := (hI.add hO).aemeasurable
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)),
        lintegral_add_left' hIO, lintegral_add_left' hI.aemeasurable]
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add (add_le_add
      (regularizedGMC_root_inner_moment_uniform_of_reference P X hX Xc hXc γ q hγ hq0 hcrit
        hR hRsmall C hRef t hcut u hu) hb)
          (regularizedGMC_root_dyadic_higher_moment_uniform P X hX Xc hXc γ q hq hR hRsmall C hRef t u hu))

/-- The higher-order root step preserves cutoff uniformity. Its sole moment input is the
proved preceding order `p-1`, on the actual same source field and reference disk. -/
theorem regularizedGMC_reference_moment_uniform_of_preceding_order
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 2 ≤ p) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞) (hC : C < ∞)
    (hRef : ∀ r : ℝ, 0 ≤ r →
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) (p - 1) ≤ C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ B := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hq : 1 ≤ p - 1 := by linarith
  have hq0 : 0 < p - 1 := by linarith
  have hcritq : (p - 1) + 1 < 4 / γ ^ 2 := by simpa only [sub_add_cancel] using hcrit
  let T : ℝ := Real.log (2 / R)
  let F : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) *
    (gmcRootHigherClippedConstant γ (p - 1) R C * gmcReferenceMeasure (Metric.ball 0 R))
  let B : ℝ≥0∞ := (gmcReferenceMeasure (Metric.ball (0 : ℂ) R)) ^ p *
    ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R)))
  have hF : F < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (gmcRootHigherClippedConstant_lt_top γ (p - 1) R hγ hq0 hcritq C hC)
      (measure_lt_top _ _))
  have hB : B < ∞ := ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)))
    ENNReal.ofReal_lt_top
  have hchart : ∀ x ∈ Metric.ball (0 : ℂ) R, ‖x‖ ≤ R := by
    intro x hx
    exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  refine ⟨F + B, ENNReal.add_lt_top.mpr ⟨hF, hB⟩, ?_⟩
  intro t ht
  by_cases hcut : 2 * Real.exp (-t) ≤ R
  · have h := regularizedGMC_positive_moment_le_clipped P X hX Xc hXc γ R t p hR.le ht
      (by linarith) (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart
    have hb : (∫⁻ u in Metric.ball (0 : ℂ) R, ∫⁻ ω,
        (∫⁻ x in Metric.ball (0 : ℂ) R, ENNReal.ofReal
          ((max ‖x - u‖ (Real.exp (-t))) ^ (-γ ^ 2)) ∂regularizedGMC P Xc γ t ω) ^ (p - 1)
            ∂P ∂gmcReferenceMeasure) ≤
          gmcRootHigherClippedConstant γ (p - 1) R C * gmcReferenceMeasure (Metric.ball 0 R) := by
      calc
        _ ≤ ∫⁻ _u in Metric.ball (0 : ℂ) R,
            gmcRootHigherClippedConstant γ (p - 1) R C ∂gmcReferenceMeasure := by
          apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
          intro u hu
          exact regularizedGMC_root_clipped_higher_moment_uniform P X hX Xc hXc γ (p - 1)
            hγ hq hcritq hR hRsmall C hRef t ht hcut u (hchart u hu)
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
    exact (h.trans (mul_le_mul' le_rfl hb)).trans (le_add_of_nonneg_right zero_le)
  · have htT : t ≤ T := by
      have he : Real.exp (-T) = R / 2 := by
        dsimp [T]
        rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hR), inv_div]
      have hexp : Real.exp (-T) < Real.exp (-t) := by rw [he]; linarith
      exact (neg_lt_neg_iff.mp (Real.exp_lt_exp.mp hexp)).le
    exact (regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ R T p hR.le (by linarith)
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart t ht htT).trans
        (le_add_of_nonneg_left zero_le)

/-- Integer-interval induction closes every strictly subcritical positive reference moment
above one, uniformly in the actual circle cutoff. -/
theorem regularizedGMC_reference_positive_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
  have hstep : ∀ n : ℕ, ∀ p : ℝ, 1 < p → p ≤ (n : ℝ) + 2 → p < 4 / γ ^ 2 →
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
        gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
    intro n
    induction n with
    | zero =>
      intro p hp hp2 hcrit
      exact regularizedGMC_reference_positive_moment_uniform_upto_two P X hX Xc hXc γ p hγ hp
        (by simpa only [Nat.cast_zero, zero_add] using hp2) hcrit hR hRsmall
    | succ n ih =>
      intro p hp hpn hcrit
      by_cases hsmall : p ≤ (n : ℝ) + 2
      · exact ih p hp hsmall hcrit
      · have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hq : 1 < p - 1 := by linarith
        have hqn : p - 1 ≤ (n : ℝ) + 2 := by
          simp only [Nat.cast_add, Nat.cast_one] at hpn
          linarith
        have hqcrit : p - 1 < 4 / γ ^ 2 := by linarith
        obtain ⟨C, hC, hRef⟩ := ih (p - 1) hq hqn hqcrit
        exact regularizedGMC_reference_moment_uniform_of_preceding_order P X hX Xc hXc γ p hγ
          (by linarith) hcrit hR hRsmall C hC hRef
  obtain ⟨n, hn⟩ := exists_nat_gt p
  exact hstep n p hp (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]) hcrit

/-- The starting subunit range and higher-order induction together cover every positive
order in the literal sharp range, uniformly over all nonnegative cutoff parameters. -/
theorem regularizedGMC_reference_moment_uniform_nonnegative
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 0 ≤ p) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
  by_cases hp1 : p ≤ 1
  · refine ⟨gmcRootSubunitReference R, gmcRootSubunitReference_lt_top R, ?_⟩
    intro t ht
    exact regularizedGMC_subunit_moment_uniform P X hX Xc hXc γ t p hp hp1
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet
  · exact regularizedGMC_reference_positive_moment_uniform P X hX Xc hXc γ p hγ
      (lt_of_not_ge hp1) hcrit hR hRsmall

/-- The complete sharp positive-moment induction passes to every GMC version. Two Fatou passages use
only the literal weak test-integral convergence in `IsGMCOf`. -/
theorem gmc_reference_positive_moment_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hcrit : p < 4 / γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    gmcMassMoment P M (Metric.ball 0 R) p < ∞ := by
  let _ := hX.1
  obtain ⟨Xc, hXc, hlimit⟩ := hM.2
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform
    P X hX Xc hXc γ p hγ hp hcrit hR hRsmall
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


/-- All nonnegative limiting reference moments in the sharp range are finite, including the
subunit starting range and zero order. -/
theorem gmc_reference_nonnegative_moment_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 0 ≤ p) (hcrit : p < 4 / γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    gmcMassMoment P M (Metric.ball 0 R) p < ∞ := by
  by_cases hp1 : p ≤ 1
  · have h := gmc_mass_subunit_moment_bound P X hX γ M hM (Metric.ball 0 R) hp hp1
    let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
    exact h.trans_lt (ENNReal.add_lt_top.mpr ⟨by simp, measure_lt_top _ _⟩)
  · exact gmc_reference_positive_moment_finite P X hX γ p hγ (lt_of_not_ge hp1) hcrit M hM hR hRsmall

/-- The sharp upper ball estimate for every nonnegative subcritical order, at small radii in
the exact chart. The coefficient is strictly positive and independent of center and radius. -/
theorem gmc_local_ball_nonnegative_sharp_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ p : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 ≤ p) (hcrit : p < 4 / γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ R → ‖z‖ + s < 1 →
      gmcMassMoment P M (Metric.ball z s) p ≤ ENNReal.ofReal (C * s ^ gmcScaleExponent γ p) := by
  let B := gmcMassMoment P M (Metric.ball 0 R) p
  have hB : B < ∞ := gmc_reference_nonnegative_moment_finite P X hX γ p hγ hp hcrit M hM hR hRsmall
  let D : ℝ := R ^ (-gmcScaleExponent γ p) * B.toReal
  have hD : 0 ≤ D := mul_nonneg (Real.rpow_nonneg hR.le _) ENNReal.toReal_nonneg
  refine ⟨D + 1, by linarith, ?_⟩
  intro z s hs hsR hzs
  rw [gmc_local_ball_moment_radius_factor P X hX γ hγ hγ2 M hM z hs hR hsR (by linarith) hzs p]
  have he : ENNReal.ofReal (R ^ (-gmcScaleExponent γ p)) *
      ENNReal.ofReal (s ^ gmcScaleExponent γ p) * B = ENNReal.ofReal (D * s ^ gmcScaleExponent γ p) := by
    rw [← ENNReal.ofReal_toReal hB.ne, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hs.le _))]
    congr 1
    dsimp [D]
    ring
  rw [he]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs.le _))



end DOZZ.Proofs
