/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.GaussianIntegration
/-!
# Off-center radial orthogonality and the correlated pin

The literal lateral family is Gaussian and independent of the full radial Brownian path. Its
radial-origin pairing retains the correlated equator pin. The lateral covariance is expanded into
the radial projection and two separable pin terms; evaluating the remaining projection integral as
the logarithmic lateral kernel of `DOZZ.circleAverage_offCenter_decomposition` is the final assembly
step.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Inward radial Bochner averages pair with the off-center origin by its constant variance. -/
theorem radialIntegralL2_origin_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (ψ : TestFn) (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (radialIntegralL2 X Xc hc z ψ) (circleAverageL2 hc (z, 0)) P =
      ∫ w : ℂ, ψ w * (2 * Real.log ‖z‖) := by
  rw [radialIntegralL2_circle_covariance X Xc hX hc z ψ (notMem_tsupport_of_punctured hψ)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul]
  · have hdist := hψ (subset_tsupport ψ hw)
    have ht : 0 ≤ -Real.log ‖w - z‖ :=
      neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hdist.2.le)
    rw [circleAverage_covariance_exterior P X Xc hX hc z hz ht le_rfl,
      min_eq_right ht, zero_add]

/-- The literal lateral field has the correlated off-center pin prescribed by the source. -/
theorem offCenter_lateral_origin_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (ψ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (fun ω => X ω ψ - ∫ w : ℂ, ψ w * Xc ω z (-Real.log ‖w - z‖))
      (fun ω => Xc ω z 0) P = ∫ w : ℂ, ψ w * (Real.log ‖w‖ - Real.log ‖z‖) := by
  let T := (equatorGFF_test_memLp X hX ψ).toLp (fun ω => X ω ψ)
  let R := radialIntegralL2 X Xc hc z ψ
  let N := circleAverageL2 hc (z, 0)
  rw [← covariance_congr_ae (lateralEvaluationL2_ae_eq X Xc hX hc hmeas z ψ
    (notMem_tsupport_of_punctured hψ)) (circleAverageL2_ae_eq hc (z, 0))]
  change covariance (⇑(T - R)) N P = _
  rw [covariance_congr_ae (Lp.coeFn_sub T R) (EventuallyEq.rfl : (⇑N) =ᵐ[P] N),
    covariance_sub_left (Lp.memLp T) (Lp.memLp R) (Lp.memLp N),
    covariance_congr_ae (MemLp.coeFn_toLp (equatorGFF_test_memLp X hX ψ))
      (circleAverageL2_ae_eq hc (z, 0)), covariance_comm (fun ω => X ω ψ),
    circleAverage_test_covariance P X Xc hX hc,
    radialIntegralL2_origin_covariance X Xc hX hc z hz ψ hψ]
  have hleft : Integrable (fun w : ℂ => ψ w * ∫ v, gffKernel w v ∂circleMeasure z 0) :=
    (ψ.continuous.mul (continuous_circleKernelPotential z 0)).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right
  have hright : Integrable (fun w : ℂ => ψ w * (2 * Real.log ‖z‖)) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).mul_const _
  unfold circleCross
  rw [← integral_sub hleft hright]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul, sub_self]
  · have hdist := hψ (subset_tsupport ψ hw)
    have hwone : 1 ≤ ‖w‖ := by
      have htri2 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - w) w
      rw [norm_sub_rev z w] at htri2
      linarith [hdist.2]
    have hpin : (∫ v, Real.log (normPlus v) ∂circleMeasure z 0) = Real.log ‖z‖ :=
      integral_log_normPlus_circleMeasure_exterior (by simpa only [neg_zero, Real.exp_zero, one_add_one_eq_two] using hz)
    dsimp only
    rw [integral_gffKernel_circleMeasure, hpin, neg_zero, Real.exp_zero,
      norm_sub_rev z w, max_eq_left hdist.2.le, Real.log_one,
      normPlus, max_eq_right hwone]
    ring

omit [IsProbabilityMeasure P] in
/-- The pinning terms cancel from a test paired with a circle increment. -/
theorem circleCross_sub_eq_integral (z : ℂ) (r s : ℝ) (ψ : TestFn) :
    circleCross z r ψ - circleCross z s ψ =
      ∫ w : ℂ, ψ w * (Real.log (max (Real.exp (-s)) ‖z - w‖) -
        Real.log (max (Real.exp (-r)) ‖z - w‖)) +
        ψ w * ((∫ v, Real.log (normPlus v) ∂circleMeasure z r) -
          (∫ v, Real.log (normPlus v) ∂circleMeasure z s)) := by
  have hi t : Integrable (fun w : ℂ => ψ w * ∫ v, gffKernel w v ∂circleMeasure z t) :=
    (ψ.continuous.mul (continuous_circleKernelPotential z t)).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right
  unfold circleCross
  rw [← integral_sub (hi r) (hi s)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [integral_gffKernel_circleMeasure, integral_gffKernel_circleMeasure]
  ring

omit [IsProbabilityMeasure P] in
/-- A truncated logarithm converts directly into Brownian radial time. -/
theorem neg_log_max_exp_eq_min {a t : ℝ} (ha : 0 < a) :
    -Real.log (max (Real.exp (-t)) a) = min t (-Real.log a) := by
  rcases le_total (Real.exp (-t)) a with h | h
  · have ht := Real.log_le_log (Real.exp_pos (-t)) h
    rw [Real.log_exp] at ht
    rw [max_eq_right h, min_eq_right (by linarith)]
  · have ht := Real.log_le_log ha h
    rw [Real.log_exp] at ht
    rw [max_eq_left h, Real.log_exp, neg_neg, min_eq_left (by linarith)]

/-- Exterior radial increments pair with inward tests by the Brownian minimum kernel. -/
theorem offCenter_increment_test_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (t : ℝ≥0) (ψ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (fun ω => Xc ω z t - Xc ω z 0) (fun ω => X ω ψ) P =
      ∫ w : ℂ, ψ w * min (t : ℝ) (-Real.log ‖w - z‖) := by
  rw [covariance_fun_sub_left (hc.2.1 z t) (hc.2.1 z 0) (equatorGFF_test_memLp X hX ψ),
    circleAverage_test_covariance P X Xc hX hc,
    circleAverage_test_covariance P X Xc hX hc, circleCross_sub_eq_integral]
  have hpin r (hr : 0 ≤ r) : (∫ v, Real.log (normPlus v) ∂circleMeasure z r) = Real.log ‖z‖ :=
    integral_log_normPlus_circleMeasure_exterior
      ((add_le_add le_rfl (exp_neg_le_one hr)).trans (by simpa only [one_add_one_eq_two] using hz))
  rw [hpin t t.coe_nonneg, hpin 0 le_rfl, sub_self]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul, zero_add]
  · have hdist := hψ (subset_tsupport ψ hw)
    rw [neg_zero, Real.exp_zero, norm_sub_rev z w, max_eq_left hdist.2.le, Real.log_one,
      zero_sub, neg_log_max_exp_eq_min hdist.1, mul_zero, add_zero]

/-- The radial Bochner component has the same covariance with each Brownian increment. -/
theorem offCenter_increment_radial_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (t : ℝ≥0) (ψ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (fun ω => Xc ω z t - Xc ω z 0) (radialIntegralL2 X Xc hc z ψ) P =
      ∫ w : ℂ, ψ w * min (t : ℝ) (-Real.log ‖w - z‖) := by
  rw [covariance_comm]
  have hae : (⇑(circleAverageL2 hc (z, t) - circleAverageL2 hc (z, 0))) =ᵐ[P]
      fun ω => Xc ω z t - Xc ω z 0 := (Lp.coeFn_sub (circleAverageL2 hc (z, t)) (circleAverageL2 hc (z, 0))).trans
    ((circleAverageL2_ae_eq hc (z, t)).sub (circleAverageL2_ae_eq hc (z, 0)))
  rw [← covariance_congr_ae (EventuallyEq.rfl : (⇑(radialIntegralL2 X Xc hc z ψ)) =ᵐ[P] _ ) hae,
    radialIntegralL2_covariance X Xc hX hc z ψ (notMem_tsupport_of_punctured hψ)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul]
  · have hdist := hψ (subset_tsupport ψ hw)
    have ht : 0 ≤ -Real.log ‖w - z‖ :=
      neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hdist.2.le)
    rw [covariance_congr_ae (circleAverageL2_ae_eq hc _) hae,
      covariance_fun_sub_right (hc.2.1 z _) (hc.2.1 z t) (hc.2.1 z 0),
      circleAverage_covariance_exterior P X Xc hX hc z hz ht t.coe_nonneg,
      circleAverage_covariance_exterior P X Xc hX hc z hz ht le_rfl,
      min_eq_right ht, zero_add, min_comm]
    ring

/-- The lateral test is orthogonal to the whole exterior radial Brownian path. -/
theorem offCenter_increment_lateral_covariance_zero (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (t : ℝ≥0) (ψ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (fun ω => Xc ω z t - Xc ω z 0)
      (fun ω => X ω ψ - ∫ w : ℂ, ψ w * Xc ω z (-Real.log ‖w - z‖)) P = 0 := by
  have hrad := radialIntegralL2_ae_eq X Xc hX hc hmeas z ψ (notMem_tsupport_of_punctured hψ)
  have hmem : MemLp (fun ω => ∫ w : ℂ, ψ w * Xc ω z (-Real.log ‖w - z‖)) 2 P :=
    MemLp.ae_eq hrad (Lp.memLp _)
  have hb : MemLp (fun ω => Xc ω z t - Xc ω z 0) 2 P := (hc.2.1 z t).sub (hc.2.1 z 0)
  rw [covariance_fun_sub_right hb
      (equatorGFF_test_memLp X hX ψ) hmem,
    ← covariance_congr_ae (EventuallyEq.rfl : (fun ω => Xc ω z t - Xc ω z 0) =ᵐ[P] _) hrad,
    offCenter_increment_test_covariance X Xc hX hc z hz t ψ hψ,
    offCenter_increment_radial_covariance X Xc hX hc z hz t ψ hψ, sub_self]

/-- The radial increments and the literal off-center origin/lateral block form one jointly
Gaussian family, rather than just separate Gaussian blocks. -/
theorem offCenter_increment_lateral_isGaussianProcess (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) (z : ℂ) :
    IsGaussianProcess (Sum.elim
      (fun t : ℝ≥0 => fun ω => Xc ω z t - Xc ω z 0)
      (fun j : Option {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}} =>
        fun ω => j.elim (Xc ω z 0) fun ψ =>
          X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖))) P := by
  let E := {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}}
  let U : ℝ≥0 ⊕ Option E → Lp ℝ 2 P := Sum.elim
    (fun t => circleAverageL2 hc (z, t) - circleAverageL2 hc (z, 0))
    (fun j => j.elim (circleAverageL2 hc (z, 0)) (fun ψ => lateralEvaluationL2 X Xc hX hc z ψ.val))
  let K := gaussianHilbertSpan (gffStructureL2Family X Xc hX hc)
  have hcircle (p : ℂ × ℝ) : circleAverageL2 hc p ∈ K :=
    mem_gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) (Sum.inl p)
  have hlateral (ψ : E) : lateralEvaluationL2 X Xc hX hc z ψ.val ∈ K :=
    lateralEvaluationL2_mem_gaussianHilbertSpan X Xc hX hc z ψ.val
      (notMem_tsupport_of_punctured ψ.property)
  have hmem : ∀ j, U j ∈ K := by
    intro j
    cases j with
    | inl t =>
      change circleAverageL2 hc (z, t) - circleAverageL2 hc (z, 0) ∈ K
      exact K.sub_mem (hcircle (z, t)) (hcircle (z, 0))
    | inr j =>
      cases j with
      | none => exact hcircle (z, 0)
      | some ψ =>
        exact hlateral ψ
  apply (isGaussianProcess_of_mem_gaussianHilbertSpan
    (gffStructureL2Family_isGaussianProcess X Xc hX hc) U hmem).congr
  intro j
  cases j with
  | inl t =>
    exact (Lp.coeFn_sub (circleAverageL2 hc (z, t)) (circleAverageL2 hc (z, 0))).trans
      ((circleAverageL2_ae_eq hc (z, t)).sub (circleAverageL2_ae_eq hc (z, 0)))
  | inr j =>
    cases j with
    | none => exact circleAverageL2_ae_eq hc (z, 0)
    | some ψ =>
      exact lateralEvaluationL2_ae_eq X Xc hX hc hmeas z ψ.val
        (notMem_tsupport_of_punctured ψ.property)

/-- Gaussian orthogonality gives independence of the whole radial path from its joint
origin/lateral block. -/
theorem offCenter_increment_lateral_indepFun (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) :
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω z t - Xc ω z 0)
      (fun ω => fun j : Option {ψ : TestFn //
          tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}} =>
        j.elim (Xc ω z 0) fun ψ =>
          X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖)) P := by
  have hG := offCenter_increment_lateral_isGaussianProcess X Xc hX hc hmeas z
  apply hG.indepFun_of_covariance_eq_zero
    (fun t => ((hc.2.1 z t).sub (hc.2.1 z 0)).aemeasurable)
    (fun j => (hG.hasGaussianLaw_eval (Sum.inr j)).aemeasurable)
  intro t j
  cases j with
  | none =>
    change covariance (fun ω => Xc ω z t - Xc ω z 0) (fun ω => Xc ω z 0) P = 0
    rw [covariance_fun_sub_left (hc.2.1 z t) (hc.2.1 z 0) (hc.2.1 z 0),
      circleAverage_covariance_exterior P X Xc hX hc z hz t.coe_nonneg le_rfl,
      circleAverage_covariance_exterior P X Xc hX hc z hz le_rfl le_rfl,
      min_eq_right t.coe_nonneg, min_self, sub_self]
  | some ψ =>
    exact offCenter_increment_lateral_covariance_zero X Xc hX hc hmeas z hz t ψ.val ψ.property

/-- Every inward circle has the same pairing with the lateral field as its radial origin. -/
theorem offCenter_circle_lateral_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (r : ℝ) (hr : 0 ≤ r) (ψ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (fun ω => Xc ω z r)
      (fun ω => X ω ψ - ∫ w : ℂ, ψ w * Xc ω z (-Real.log ‖w - z‖)) P =
      ∫ w : ℂ, ψ w * (Real.log ‖w‖ - Real.log ‖z‖) := by
  have hY : MemLp (fun ω => X ω ψ - ∫ w : ℂ, ψ w * Xc ω z (-Real.log ‖w - z‖)) 2 P :=
    MemLp.ae_eq (lateralEvaluationL2_ae_eq X Xc hX hc hmeas z ψ
      (notMem_tsupport_of_punctured hψ)) (Lp.memLp _)
  have hzero := offCenter_increment_lateral_covariance_zero X Xc hX hc hmeas z hz ⟨r, hr⟩ ψ hψ
  change covariance (fun ω => Xc ω z r - Xc ω z 0) _ P = 0 at hzero
  rw [covariance_fun_sub_left (hc.2.1 z r) (hc.2.1 z 0) hY] at hzero
  have hN := offCenter_lateral_origin_covariance X Xc hX hc hmeas z hz ψ hψ
  rw [covariance_comm] at hN
  linarith

/-- The covariance of a radial Bochner test and a lateral test is a separable pin pairing. -/
theorem offCenter_radial_lateral_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (ψ χ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1})
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (radialIntegralL2 X Xc hc z ψ) (lateralEvaluationL2 X Xc hX hc z χ) P =
      (∫ w : ℂ, ψ w) * (∫ v : ℂ, χ v * (Real.log ‖v‖ - Real.log ‖z‖)) := by
  rw [radialIntegralL2_covariance X Xc hX hc z ψ (notMem_tsupport_of_punctured hψ)]
  have heq : (fun w : ℂ => ψ w * covariance (circleAverageL2 hc (z, -Real.log ‖w - z‖))
      (lateralEvaluationL2 X Xc hX hc z χ) P) =ᵐ[volume]
      fun w => ψ w * (∫ v : ℂ, χ v * (Real.log ‖v‖ - Real.log ‖z‖)) := by
    apply Eventually.of_forall
    intro w
    dsimp only
    by_cases hw : ψ w = 0
    · simp only [hw, zero_mul]
    · have hdist := hψ (subset_tsupport ψ hw)
      have ht : 0 ≤ -Real.log ‖w - z‖ :=
        neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hdist.2.le)
      rw [covariance_congr_ae (circleAverageL2_ae_eq hc _)
        (lateralEvaluationL2_ae_eq X Xc hX hc hmeas z χ (notMem_tsupport_of_punctured hχ)),
        offCenter_circle_lateral_covariance X Xc hX hc hmeas z hz _ ht χ hχ]
  rw [integral_congr_ae heq, integral_mul_const]

/-- The lateral covariance is the original test covariance minus the radial projection and
its two separable correlated pin terms. -/
theorem offCenter_lateral_covariance_expansion (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (ψ χ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1})
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (lateralEvaluationL2 X Xc hX hc z ψ) (lateralEvaluationL2 X Xc hX hc z χ) P =
      gffCov ψ χ - covariance (radialIntegralL2 X Xc hc z ψ) (radialIntegralL2 X Xc hc z χ) P -
        (∫ w : ℂ, ψ w) * (∫ v : ℂ, χ v * (Real.log ‖v‖ - Real.log ‖z‖)) -
        (∫ v : ℂ, χ v) * (∫ w : ℂ, ψ w * (Real.log ‖w‖ - Real.log ‖z‖)) := by
  let Tψ := (equatorGFF_test_memLp X hX ψ).toLp (fun ω => X ω ψ)
  let Tχ := (equatorGFF_test_memLp X hX χ).toLp (fun ω => X ω χ)
  let Rψ := radialIntegralL2 X Xc hc z ψ
  let Rχ := radialIntegralL2 X Xc hc z χ
  have h1 := offCenter_radial_lateral_covariance X Xc hX hc hmeas z hz ψ χ hψ hχ
  have h2 := offCenter_radial_lateral_covariance X Xc hX hc hmeas z hz χ ψ hχ hψ
  change covariance Rψ (⇑(Tχ - Rχ)) P = _ at h1
  change covariance Rχ (⇑(Tψ - Rψ)) P = _ at h2
  rw [covariance_congr_ae (EventuallyEq.rfl : (⇑Rψ) =ᵐ[P] _ ) (Lp.coeFn_sub Tχ Rχ),
    covariance_sub_right (Lp.memLp Rψ) (Lp.memLp Tχ) (Lp.memLp Rχ)] at h1
  rw [covariance_congr_ae (EventuallyEq.rfl : (⇑Rχ) =ᵐ[P] _ ) (Lp.coeFn_sub Tψ Rψ),
    covariance_sub_right (Lp.memLp Rχ) (Lp.memLp Tψ) (Lp.memLp Rψ), covariance_comm Rχ Rψ] at h2
  have htests : covariance Tψ Tχ P = gffCov ψ χ := by
    rw [covariance_congr_ae (MemLp.coeFn_toLp (equatorGFF_test_memLp X hX ψ))
      (MemLp.coeFn_toLp (equatorGFF_test_memLp X hX χ)), equatorGFF_test_covariance X hX]
  change covariance (⇑(Tψ - Rψ)) (⇑(Tχ - Rχ)) P = _
  rw [covariance_congr_ae (Lp.coeFn_sub Tψ Rψ) (Lp.coeFn_sub Tχ Rχ),
    covariance_sub_sub (Lp.memLp Tψ) (Lp.memLp Rψ) (Lp.memLp Tχ) (Lp.memLp Rχ),
    htests, covariance_comm Tψ Rχ]
  linarith

/-- Pairing a centered integrable L² family with a fixed L² vector is integrable. -/
theorem integrable_covariance_L2_left {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (F : A → Lp ℝ 2 P) (hF : Integrable F μ) (V : Lp ℝ 2 P)
    (hzero : ∀ a, (∫ ω, F a ω ∂P) = 0) :
    Integrable (fun a => covariance (F a) V P) μ := by
  simp_rw [covariance_L2_eq, hzero, zero_mul, sub_zero]
  have hi := (innerSL ℝ V).integrable_comp hF
  change Integrable (fun a => inner ℝ V (F a)) μ at hi
  simpa only [real_inner_comm V] using hi

/-- Every compact weighted radial covariance has the integrability needed for subtracting
its projection kernel inside the final lateral covariance calculation. -/
theorem integrable_testFn_mul_radial_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (ψ : TestFn)
    (hz : z ∉ tsupport ψ) (V : Lp ℝ 2 P) :
    Integrable (fun w : ℂ => ψ w * covariance
      (circleAverageL2 hc (z, -Real.log ‖w - z‖)) V P) := by
  have hi := integrable_covariance_L2_left volume
    (fun w : ℂ => ψ w • circleAverageL2 hc (z, -Real.log ‖w - z‖))
    (integrable_testFn_smul_radialL2 X Xc hX hc z ψ hz) V (fun w => by
      rw [integral_mean_L2_smul, circleAverageL2_integral_eq_zero P X Xc hX hc, mul_zero])
  simpa only [covariance_L2_smul_left] using hi

omit [IsProbabilityMeasure P] in
/-- The off-center radial origin has the exact variance. -/
theorem offCenter_origin_variance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖) :
    covariance (fun ω => Xc ω z 0) (fun ω => Xc ω z 0) P = 2 * Real.log ‖z‖ := by
  simpa only [min_self, zero_add] using
    circleAverage_covariance_exterior P X Xc hX hc z hz (r := 0) (s := 0) le_rfl le_rfl

omit [IsProbabilityMeasure P] in
/-- Concentric Brownian times correspond to the logarithm of the larger geometric radius. -/
theorem min_neg_log_eq_neg_log_max {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min (-Real.log a) (-Real.log b) = -Real.log (max a b) := by
  rcases le_total a b with h | h
  · have hl := Real.log_le_log ha h
    rw [max_eq_right h, min_eq_right (neg_le_neg hl)]
  · have hl := Real.log_le_log hb h
    rw [max_eq_left h, min_eq_left (neg_le_neg hl)]

omit [IsProbabilityMeasure P] in
/-- The radial projection kernel at two inward geometric radii, before test integration. -/
theorem offCenter_radial_geometric_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (haone : a ≤ 1) (hbone : b ≤ 1) :
    covariance (fun ω => Xc ω z (-Real.log a)) (fun ω => Xc ω z (-Real.log b)) P =
      -Real.log (max a b) + 2 * Real.log ‖z‖ := by
  rw [circleAverage_covariance_exterior P X Xc hX hc z hz
      (neg_nonneg.mpr (Real.log_nonpos ha.le haone))
      (neg_nonneg.mpr (Real.log_nonpos hb.le hbone)),
    min_neg_log_eq_neg_log_max ha hb]

omit [IsProbabilityMeasure P] in

omit [IsProbabilityMeasure P] in
/-- A compact test avoiding a point is integrable against a logarithmic pole at that point. -/
theorem integrable_testFn_mul_log_norm_sub (ψ : TestFn) (z : ℂ) (hz : z ∉ tsupport ψ) :
    Integrable (fun w : ℂ => ψ w * Real.log ‖w - z‖) := by
  have hc : Continuous (fun w : ℂ => ψ w * Real.log ‖w - z‖) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    by_cases hw : w = z
    · subst w
      apply (show ContinuousAt (fun _ : ℂ => (0 : ℝ)) z from continuousAt_const).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
      change ψ w = 0 at hw
      rw [hw, zero_mul]
    · exact ψ.continuous.continuousAt.mul
        ((continuous_id.sub continuous_const).norm.continuousAt.log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)))
  exact hc.integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right

/-- The radial projection kernel is integrable against every inward test, at every pole. -/
theorem integrable_offCenter_radial_kernel (z w : ℂ) (χ : TestFn)
    (hχ : z ∉ tsupport χ) :
    Integrable (fun v : ℂ => (-Real.log (max ‖w - z‖ ‖v - z‖) + 2 * Real.log ‖z‖) * χ v) := by
  have hi : Integrable (fun v : ℂ => χ v * Real.log (max ‖w - z‖ ‖v - z‖)) := by
    by_cases hw : w = z
    · simpa only [hw, sub_self, norm_zero, max_eq_right (norm_nonneg _)] using
        integrable_testFn_mul_log_norm_sub χ z hχ
    · have hp : Continuous (fun v : ℂ => Real.log (max ‖w - z‖ ‖v - z‖)) :=
        (continuous_const.max (continuous_id.sub continuous_const).norm).log
          (fun _ => ne_of_gt ((norm_pos_iff.mpr (sub_ne_zero.mpr hw)).trans_le (le_max_left _ _)))
      exact (χ.continuous.mul hp).integrable_of_hasCompactSupport χ.hasCompactSupport.mul_right
  have hc : Integrable (fun v : ℂ => χ v * (2 * Real.log ‖z‖)) :=
    (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).mul_const _
  convert hi.neg.add hc using 1
  funext v
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- One inward circle pairs with a radial test by the explicit concentric projection kernel. -/
theorem offCenter_circle_radial_geometric_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (a : ℝ) (ha : 0 < a) (haone : a ≤ 1) (χ : TestFn)
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (circleAverageL2 hc (z, -Real.log a)) (radialIntegralL2 X Xc hc z χ) P =
      ∫ v : ℂ, (-Real.log (max a ‖v - z‖) + 2 * Real.log ‖z‖) * χ v := by
  rw [covariance_comm, radialIntegralL2_circle_covariance X Xc hX hc z χ
    (notMem_tsupport_of_punctured hχ)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : χ v = 0
  · simp only [hv, zero_mul, mul_zero]
  · have hd := hχ (subset_tsupport χ hv)
    rw [covariance_comm, offCenter_radial_geometric_covariance X Xc hX hc z hz ha hd.1 haone hd.2.le]
    ring

/-- The full radial test covariance has the explicit logarithmic projection kernel. -/
theorem offCenter_radial_covariance_geometric (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (ψ χ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1})
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (radialIntegralL2 X Xc hc z ψ) (radialIntegralL2 X Xc hc z χ) P =
      ∫ w : ℂ, ψ w * ∫ v : ℂ,
        (-Real.log (max ‖w - z‖ ‖v - z‖) + 2 * Real.log ‖z‖) * χ v := by
  rw [radialIntegralL2_covariance X Xc hX hc z ψ (notMem_tsupport_of_punctured hψ)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul]
  · have hd := hψ (subset_tsupport ψ hw)
    rw [offCenter_circle_radial_geometric_covariance X Xc hX hc z hz ‖w - z‖ hd.1 hd.2.le χ hχ]

/-- The projected radial kernel also has the outer integrability needed for bilinear cancellation. -/
theorem integrable_offCenter_radial_pairing (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (ψ χ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1})
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    Integrable (fun w : ℂ => ψ w * ∫ v : ℂ,
      (-Real.log (max ‖w - z‖ ‖v - z‖) + 2 * Real.log ‖z‖) * χ v) := by
  have hi := integrable_testFn_mul_radial_covariance X Xc hX hc z ψ
    (notMem_tsupport_of_punctured hψ) (radialIntegralL2 X Xc hc z χ)
  apply hi.congr
  apply Eventually.of_forall
  intro w
  dsimp only
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul]
  · have hd := hψ (subset_tsupport ψ hw)
    rw [offCenter_circle_radial_geometric_covariance X Xc hX hc z hz ‖w - z‖ hd.1 hd.2.le χ hχ]

omit [IsProbabilityMeasure P] in
/-- The correlated pin pairing of `DOZZ.circleAverage_offCenter_decomposition` can be evaluated
using the globally continuous pin. -/
theorem offCenter_pin_pair_eq (z : ℂ) (hz : 2 ≤ ‖z‖) (ψ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    (∫ w : ℂ, ψ w * (Real.log ‖w‖ - Real.log ‖z‖)) =
      ∫ w : ℂ, ψ w * (Real.log (normPlus w) - Real.log ‖z‖) := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  by_cases hw : ψ w = 0
  · simp only [hw, zero_mul]
  · have hd := hψ (subset_tsupport ψ hw)
    have htri : ‖z‖ ≤ ‖w - z‖ + ‖w‖ := by
      simpa only [sub_add_cancel, norm_sub_rev z w] using norm_add_le (z - w) w
    have hwone : 1 ≤ ‖w‖ := by linarith [hd.2]
    rw [normPlus, max_eq_right hwone]

/-- Radial projection and its two correlated pin terms cancel to the lateral kernel of
`DOZZ.circleAverage_offCenter_decomposition`. -/
theorem offCenter_kernel_cancellation (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖)
    (ψ χ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1})
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    gffCov ψ χ - covariance (radialIntegralL2 X Xc hc z ψ) (radialIntegralL2 X Xc hc z χ) P -
      (∫ w : ℂ, ψ w) * (∫ v : ℂ, χ v * (Real.log ‖v‖ - Real.log ‖z‖)) -
      (∫ v : ℂ, χ v) * (∫ w : ℂ, ψ w * (Real.log ‖w‖ - Real.log ‖z‖)) =
      ∫ w : ℂ, ψ w * ∫ v : ℂ,
        (-Real.log ‖w - v‖ + Real.log (max ‖w - z‖ ‖v - z‖)) * χ v := by
  let p : ℂ → ℝ := fun w => Real.log (normPlus w) - Real.log ‖z‖
  have hp : Continuous p := continuous_log_normPlus.sub continuous_const
  have hχi : Integrable χ (volume : Measure ℂ) :=
    χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hχp : Integrable (fun v : ℂ => p v * χ v) :=
    (hp.mul χ.continuous).integrable_of_hasCompactSupport χ.hasCompactSupport.mul_left
  have hinner w : (∫ v : ℂ, (gffKernel w v - p w - p v) * χ v) =
      (∫ v : ℂ, gffKernel w v * χ v) - p w * (∫ v : ℂ, χ v) - (∫ v : ℂ, p v * χ v) := by
    have hkg := integrable_testKernel_section χ w
    have heq v : (gffKernel w v - p w - p v) * χ v =
        (gffKernel w v * χ v - p w * χ v) - p v * χ v := by ring
    simp_rw [heq]
    have h1 := integral_sub hkg (hχi.const_mul (p w))
    have h2 := integral_sub (hkg.sub (hχi.const_mul (p w))) hχp
    simp only [Pi.sub_apply] at h2
    rw [h2, h1, integral_const_mul]
  have hAi : Integrable (fun w : ℂ => ψ w * ∫ v : ℂ, (gffKernel w v - p w - p v) * χ v) := by
    simp_rw [hinner]
    exact (ψ.continuous.mul (((continuous_testKernelPotential χ).sub
      (hp.mul continuous_const)).sub continuous_const)).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.mul_right
  have hRi := integrable_offCenter_radial_pairing X Xc hX hc z hz ψ χ hψ hχ
  have hAinneri w : Integrable (fun v : ℂ => (gffKernel w v - p w - p v) * χ v) := by
    have hi := ((integrable_testKernel_section χ w).sub (hχi.const_mul (p w))).sub hχp
    convert hi using 1
    funext v
    simp only [Pi.sub_apply]
    ring
  calc
    _ = (gffCov ψ χ - (∫ w : ℂ, ψ w * p w) * (∫ v : ℂ, χ v) -
        (∫ w : ℂ, ψ w) * (∫ v : ℂ, χ v * p v) +
        (∫ w : ℂ, ψ w) * (∫ v : ℂ, χ v) * 0) -
        covariance (radialIntegralL2 X Xc hc z ψ) (radialIntegralL2 X Xc hc z χ) P := by
      rw [offCenter_pin_pair_eq z hz ψ hψ, offCenter_pin_pair_eq z hz χ hχ]
      dsimp only [p]
      ring
    _ = (∫ w : ℂ, ψ w * ∫ v : ℂ, (gffKernel w v - p w - p v) * χ v) -
        (∫ w : ℂ, ψ w * ∫ v : ℂ,
          (-Real.log (max ‖w - z‖ ‖v - z‖) + 2 * Real.log ‖z‖) * χ v) := by
      rw [gffCov_sub_potential_integral ψ χ p hp 0,
        offCenter_radial_covariance_geometric X Xc hX hc z hz ψ χ hψ hχ]
      simp only [add_zero]
    _ = _ := by
      rw [← integral_sub hAi hRi]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro w
      dsimp only
      rw [← mul_sub, ← integral_sub (hAinneri w)
        (integrable_offCenter_radial_kernel z w χ (notMem_tsupport_of_punctured hχ))]
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro v
      dsimp only [p, gffKernel]
      ring

/-- The actual off-center lateral evaluations have the logarithmic covariance of
`DOZZ.circleAverage_offCenter_decomposition`. -/
theorem offCenter_lateral_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (ψ χ : TestFn)
    (hψ : tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1})
    (hχ : tsupport χ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}) :
    covariance (fun ω => X ω ψ - ∫ w : ℂ, ψ w * Xc ω z (-Real.log ‖w - z‖))
      (fun ω => X ω χ - ∫ w : ℂ, χ w * Xc ω z (-Real.log ‖w - z‖)) P =
      ∫ w : ℂ, ψ w * ∫ v : ℂ,
        (-Real.log ‖w - v‖ + Real.log (max ‖w - z‖ ‖v - z‖)) * χ v := by
  rw [← covariance_congr_ae
    (lateralEvaluationL2_ae_eq X Xc hX hc hmeas z ψ (notMem_tsupport_of_punctured hψ))
    (lateralEvaluationL2_ae_eq X Xc hX hc hmeas z χ (notMem_tsupport_of_punctured hχ)),
    offCenter_lateral_covariance_expansion X Xc hX hc hmeas z hz ψ χ hψ hχ,
    offCenter_kernel_cancellation X Xc hX hc z hz ψ χ hψ hχ]

omit [IsProbabilityMeasure P] in
/-- Exact off-center decomposition of the jointly measurable circle witness. -/
theorem circleAverage_offCenter_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) :
    IsGaussianProcess (fun j : Option {ψ : TestFn //
        tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}} => fun ω =>
      j.elim (Xc ω z 0) fun ψ => X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖)) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω z t - Xc ω z 0)
      (fun ω => fun j : Option {ψ : TestFn //
          tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}} =>
        j.elim (Xc ω z 0) fun ψ =>
          X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖)) P ∧
    covariance (fun ω => Xc ω z 0) (fun ω => Xc ω z 0) P = 2 * Real.log ‖z‖ ∧
    (∀ ψ : {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}},
      covariance (fun ω => X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖))
        (fun ω => Xc ω z 0) P =
        ∫ w : ℂ, ψ.val w * (Real.log ‖w‖ - Real.log ‖z‖)) ∧
    (∀ ψ χ : {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}},
      covariance (fun ω => X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖))
        (fun ω => X ω χ.val - ∫ w : ℂ, χ.val w * Xc ω z (-Real.log ‖w - z‖)) P =
        ∫ w : ℂ, ψ.val w * ∫ w' : ℂ,
          (-Real.log ‖w - w'‖ + Real.log (max ‖w - z‖ ‖w' - z‖)) * χ.val w') := by
  have hc := (continuous_circleAverage_version_spec P X Xc Xc hc hmeas hcont
    (fun _ _ => EventuallyEq.rfl)).1
  let _ := hX.1
  refine ⟨offCenter_lateral_isGaussianProcess X Xc hX hc hmeas z,
    offCenter_increment_lateral_indepFun X Xc hX hc hmeas z hz,
    offCenter_origin_variance X Xc hX hc z hz, ?_, ?_⟩
  · intro ψ
    exact offCenter_lateral_origin_covariance X Xc hX hc hmeas z hz ψ.val ψ.property
  · intro ψ χ
    exact offCenter_lateral_covariance X Xc hX hc hmeas z hz ψ.val χ.val ψ.property χ.property

end DOZZ.Proofs
