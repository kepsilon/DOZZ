/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.CircleCovariance
public import Mathlib.Probability.Process.Kolmogorov
public import DOZZ.GFFStructure.HolderVersions
public import Mathlib.Analysis.InnerProductSpace.ProdL2
/-!
# Continuous circle-average versions

The unit-mass pinning terms cancel from circle increments. Truncated logarithmic potentials control
their variances, and Gaussian scaling gives all even moment bounds. Width-one radius strips satisfy
the dimension-three Kolmogorov condition with exponents eight and four. The literal closed
covariance is jointly continuous, including all intersecting circle branches. Its continuity follows
from the given L² field rather than from separate branchwise derivatives. Clamped strip processes
admit Hölder modifications in a three-dimensional Hilbert carrier. A countable overlapping cover and
one measurable agreement event give a jointly measurable global version retaining the given witness.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs

/-- The radius-truncated logarithmic potential has an explicit transport error bound. -/
theorem integral_circle_logmax_sub_le (x y : ℂ) (r s : ℝ) :
    (∫ z, Real.log (max (Real.exp (-s)) ‖y - z‖) ∂circleMeasure x r) -
      Real.log (Real.exp (-s)) ≤
        (‖x - y‖ + |Real.exp (-r) - Real.exp (-s)|) / Real.exp (-s) := by
  let _ := circleMeasure_isProbability x r
  let a := Real.exp (-r)
  let b := Real.exp (-s)
  let D := ‖x - y‖ + |a - b|
  have hb : 0 < b := Real.exp_pos _
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hlog : Continuous (fun z : ℂ => Real.log (max b ‖y - z‖)) :=
    (continuous_const.max (continuous_const.sub continuous_id).norm).log
      (fun _ => ne_of_gt (hb.trans_le (le_max_left _ _)))
  have hi := integrable_circleMeasure_of_circleIntegrable x r hlog.measurable hlog.continuousOn.circleIntegrable'
  have hpoint : ∀ᵐ z ∂circleMeasure x r, Real.log (max b ‖y - z‖) ≤ Real.log (b + D) := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    apply Real.log_le_log (hb.trans_le (le_max_left _ _))
    apply max_le (le_add_of_nonneg_right hD)
    have hdist : ‖y - z‖ ≤ ‖x - y‖ + a := by
      calc
        ‖y - z‖ = ‖(y - x) + (x - z)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
        _ = ‖x - y‖ + a := by rw [norm_sub_rev y x, norm_sub_rev x z, hz]
    have hab := le_abs_self (a - b)
    dsimp [D]
    linarith
  have hmean := integral_mono_ae hi (integrable_const (Real.log (b + D))) hpoint
  rw [integral_const, probReal_univ, one_smul] at hmean
  have hratio : Real.log (b + D) - Real.log b ≤ D / b := by
    have h := Real.log_le_sub_one_of_pos (div_pos (add_pos_of_pos_of_nonneg hb hD) hb)
    rw [Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg hb hD)) (ne_of_gt hb)] at h
    have he : (b + D) / b - 1 = D / b := by field_simp; ring
    rwa [he] at h
  exact (sub_le_sub_right hmean _).trans hratio

/-- Center/radius increments are independent of the equator pin: only raw log energy remains. -/
theorem circleAverage_increment_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x y : ℂ) (r s : ℝ) :
    variance (fun ω => Xc ω x r - Xc ω y s) P = r + s +
      2 * (∫ z, Real.log (max (Real.exp (-s)) ‖y - z‖) ∂circleMeasure x r) := by
  let _ := hX.1
  have hm : AEMeasurable (fun ω => Xc ω x r - Xc ω y s) P :=
    ((hc.2.1 x r).sub (hc.2.1 y s)).aemeasurable
  rw [← covariance_self hm,
    covariance_fun_sub_fun_sub (hc.2.1 x r) (hc.2.1 y s) (hc.2.1 x r) (hc.2.1 y s),
    circleAverage_covariance_self X Xc hX hc,
    circleAverage_covariance_self X Xc hX hc, covariance_comm (fun ω => Xc ω y s),
    circleAverage_covariance_integral P X Xc hX hc,
    integral_integral_gffKernel_eq_logmax, circleSelfEnergy_eq, circleSelfEnergy_eq]
  ring

/-- Quantitative second moment bound for moving both the center and logarithmic radius. -/
theorem circleAverage_increment_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x y : ℂ) (r s : ℝ) :
    variance (fun ω => Xc ω x r - Xc ω y s) P ≤ |r - s| +
      2 * (‖x - y‖ + |Real.exp (-r) - Real.exp (-s)|) / Real.exp (-s) := by
  rw [circleAverage_increment_variance P X Xc hX hc]
  have h := integral_circle_logmax_sub_le x y r s
  rw [Real.log_exp] at h
  have hab := le_abs_self (r - s)
  simp only [div_eq_mul_inv] at h ⊢
  linarith

/-- The original circle witness as an element of the given probability space's L². -/
noncomputable def circleAverageL2 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (p : ℂ × ℝ) : Lp ℝ 2 P :=
  (hc.2.1 p.1 p.2).toLp (fun ω => Xc ω p.1 p.2)

/-- The chosen L² representative agrees with the original coordinate almost surely. -/
theorem circleAverageL2_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (p : ℂ × ℝ) :
    circleAverageL2 hc p =ᵐ[P] fun ω => Xc ω p.1 p.2 :=
  MemLp.coeFn_toLp _

/-- Centering turns the L² increment norm into the circle increment variance. -/
theorem circleAverageL2_norm_sub_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (p q : ℂ × ℝ) :
    ‖circleAverageL2 hc p - circleAverageL2 hc q‖ ^ 2 =
      variance (fun ω => Xc ω p.1 p.2 - Xc ω q.1 q.2) P := by
  let _ := hX.1
  let D := circleAverageL2 hc p - circleAverageL2 hc q
  have hae : D =ᵐ[P] fun ω => Xc ω p.1 p.2 - Xc ω q.1 q.2 := by
    filter_upwards [Lp.coeFn_sub (circleAverageL2 hc p) (circleAverageL2 hc q),
      circleAverageL2_ae_eq hc p, circleAverageL2_ae_eq hc q] with ω hD hp hq
    rw [hD, Pi.sub_apply, hp, hq]
  have hm : AEMeasurable (fun ω => Xc ω p.1 p.2 - Xc ω q.1 q.2) P :=
    ((hc.2.1 p.1 p.2).sub (hc.2.1 q.1 q.2)).aemeasurable
  have hmean : (∫ ω, D ω ∂P) = 0 := by
    rw [integral_congr_ae hae]
    have hi := integral_sub ((hc.2.1 p.1 p.2).integrable (by norm_num))
      ((hc.2.1 q.1 q.2).integrable (by norm_num))
    rw [hi, (circleAverage_isGaussianProcess P X Xc hX hc).2,
      (circleAverage_isGaussianProcess P X Xc hX hc).2, sub_self]
  have hcov := covariance_L2_eq D D
  rw [hmean, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hcov
  rw [← covariance_self hm, ← covariance_congr_ae hae hae, hcov]

/-- Circle averages depend continuously on center and radius in L², before construction of
an almost surely continuous sample version. -/
theorem continuous_circleAverageL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    Continuous (circleAverageL2 hc) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hbound q : ‖circleAverageL2 hc q - circleAverageL2 hc p‖ ^ 2 ≤
      |q.2 - p.2| + 2 * (‖q.1 - p.1‖ + |Real.exp (-q.2) - Real.exp (-p.2)|) /
        Real.exp (-p.2) := by
    rw [circleAverageL2_norm_sub_sq P X Xc hX hc]
    exact circleAverage_increment_variance_le P X Xc hX hc q.1 p.1 q.2 p.2
  have hb : Tendsto (fun q : ℂ × ℝ =>
      |q.2 - p.2| + 2 * (‖q.1 - p.1‖ + |Real.exp (-q.2) - Real.exp (-p.2)|) /
        Real.exp (-p.2)) (𝓝 p) (𝓝 0) := by
    have h : Continuous (fun q : ℂ × ℝ =>
      |q.2 - p.2| + 2 * (‖q.1 - p.1‖ + |Real.exp (-q.2) - Real.exp (-p.2)|) /
        Real.exp (-p.2)) := by fun_prop
    simpa only [sub_self, norm_zero, abs_zero, zero_add, mul_zero, zero_div, add_zero]
      using h.continuousAt.tendsto (x := p)
  have hs := squeeze_zero (fun q : ℂ × ℝ => sq_nonneg ‖circleAverageL2 hc q - circleAverageL2 hc p‖)
    hbound hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

/-- Coordinatewise modifications preserve the energy-limit clause of `DOZZ.IsCircleAverage` and L²
membership; the only separate requirement is its literal measurability clause. -/
theorem isCircleAverage_of_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc Y : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc)
    (hmeas : ∀ r, Measurable (fun p : Ω × ℂ => Y p.1 p.2 r))
    (heq : ∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) :
    IsCircleAverage P X Y := by
  refine ⟨hmeas, (fun x r => MemLp.ae_eq (heq x r).symm (hc.2.1 x r)), ?_⟩
  intro x r f hf
  have hn n : eLpNorm (fun ω => X ω (f n) - Y ω x r) 2 P =
      eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [heq x r] with ω hω
    rw [hω]
  simpa only [hn] using hc.2.2 x r f hf

/-- Relative radius error is controlled locally by logarithmic radius error. -/
theorem exp_neg_relative_error_le {r s : ℝ} (hrs : |r - s| ≤ 1) :
    |Real.exp (-r) - Real.exp (-s)| / Real.exp (-s) ≤ 2 * |r - s| := by
  have he : (Real.exp (-r) - Real.exp (-s)) / Real.exp (-s) = Real.exp (s - r) - 1 := by
    rw [sub_div, div_self (Real.exp_ne_zero _), ← Real.exp_sub]
    rw [show -r - -s = s - r by ring]
  have h := Real.abs_exp_sub_one_le (x := s - r) (by simpa only [abs_sub_comm] using hrs)
  rw [← he, abs_div, abs_of_pos (Real.exp_pos _)] at h
  simpa only [abs_sub_comm] using h

/-- A uniform local variance bound on each bounded logarithmic-radius strip. -/
theorem circleAverage_increment_variance_le_on_strip {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x y : ℂ) (r s S : ℝ)
    (hs : s ≤ S) (hrs : |r - s| ≤ 1) :
    variance (fun ω => Xc ω x r - Xc ω y s) P ≤
      (5 + 2 * Real.exp S) * (‖x - y‖ + |r - s|) := by
  have h := circleAverage_increment_variance_le P X Xc hX hc x y r s
  have hradius := exp_neg_relative_error_le hrs
  have hcenter : ‖x - y‖ / Real.exp (-s) ≤ Real.exp S * ‖x - y‖ := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hs) (norm_nonneg _)
  have hsplit : 2 * (‖x - y‖ + |Real.exp (-r) - Real.exp (-s)|) / Real.exp (-s) =
      2 * (‖x - y‖ / Real.exp (-s)) +
      2 * (|Real.exp (-r) - Real.exp (-s)| / Real.exp (-s)) := by ring
  rw [hsplit] at h
  have hn := norm_nonneg (x - y)
  have ha := abs_nonneg (r - s)
  have he := Real.exp_pos S
  nlinarith

/-- Even moments of a centered real Gaussian scale as the corresponding variance power,
including the zero-variance law. -/
theorem integral_abs_pow_gaussianReal (v : ℝ≥0) (m : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 v) =
      (v : ℝ) ^ m * (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 1) := by
  let a := Real.sqrt (v : ℝ)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
  have he : (gaussianReal 0 1).map (fun x : ℝ => a * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact NNReal.eq ha2
  rw [← he, integral_map (by fun_prop) (by fun_prop)]
  have hp x : |a * x| ^ (2 * m) = (v : ℝ) ^ m * |x| ^ (2 * m) := by
    rw [abs_mul, mul_pow, abs_of_nonneg ha, pow_mul, ha2]
  simp_rw [hp]
  exact integral_const_mul _ _

/-- Gaussian even moments are controlled by any nonnegative variance bound. -/
theorem hasGaussianLaw_integral_abs_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (U : Ω → ℝ) (hG : HasGaussianLaw U P)
    (hmean : (∫ ω, U ω ∂P) = 0) (m : ℕ) {B : ℝ}
    (hB : variance U P ≤ B) :
    (∫ ω, |U ω| ^ (2 * m) ∂P) ≤
      B ^ m * (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 1) := by
  have he : (∫ ω, |U ω| ^ (2 * m) ∂P) =
      (variance U P) ^ m * (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 1) := by
    have hi := integral_map hG.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => |x| ^ (2 * m)) (P.map U) by fun_prop)
    rw [hG.map_eq_gaussianReal, hmean, integral_abs_pow_gaussianReal,
      Real.coe_toNNReal _ (variance_nonneg _ _)] at hi
    exact hi.symm
  rw [he]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (variance_nonneg _ _) hB _)
    (integral_nonneg (fun x => pow_nonneg (abs_nonneg x) _))


/-- On a radius strip of width one, the increment variance is uniformly bounded by the
ambient product distance. The center may range over the whole plane. -/
theorem circleAverage_increment_variance_le_dist_on_strip {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (S : ℝ)
    (p q : {p : ℂ × ℝ // p.2 ∈ Icc S (S + 1)}) :
    variance (fun ω => Xc ω p.val.1 p.val.2 - Xc ω q.val.1 q.val.2) P ≤
      (2 * (5 + 2 * Real.exp (S + 1))) * dist p q := by
  have hrs : |p.val.2 - q.val.2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [p.property.1, p.property.2, q.property.1, q.property.2]
  have hv := circleAverage_increment_variance_le_on_strip P X Xc hX hc
    p.val.1 q.val.1 p.val.2 q.val.2 (S + 1) q.property.2 hrs
  have hsum : ‖p.val.1 - q.val.1‖ + |p.val.2 - q.val.2| ≤ 2 * dist p q := by
    change _ ≤ 2 * max (dist p.val.1 q.val.1) (dist p.val.2 q.val.2)
    rw [dist_eq_norm, Real.dist_eq]
    have h1 := le_max_left ‖p.val.1 - q.val.1‖ |p.val.2 - q.val.2|
    have h2 := le_max_right ‖p.val.1 - q.val.1‖ |p.val.2 - q.val.2|
    linarith
  exact hv.trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring))


/-- Every width-one radius strip satisfies the dimension-three Kolmogorov condition with
moment exponent eight and distance exponent four. This is a moment estimate, not a sample
continuity theorem. -/
theorem circleAverage_isKolmogorovProcess_on_strip {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (S : ℝ) :
    ∃ M : ℝ≥0, IsKolmogorovProcess
      (fun p : {p : ℂ × ℝ // p.2 ∈ Icc S (S + 1)} => fun ω => Xc ω p.val.1 p.val.2)
      P 8 4 M := by
  let _ := hX.1
  let C := 2 * (5 + 2 * Real.exp (S + 1))
  let A := ∫ x : ℝ, |x| ^ 8 ∂gaussianReal 0 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := integral_nonneg (fun x => pow_nonneg (abs_nonneg x) _)
  let M : ℝ≥0 := ⟨C ^ 4 * A, mul_nonneg (pow_nonneg hC _) hA⟩
  refine ⟨M, IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun p => circleAverage_measurable_eval X Xc hc p.val.1 p.val.2) ?_ (by norm_num) (by norm_num)⟩
  intro p q
  let U : Ω → ℝ := fun ω => Xc ω p.val.1 p.val.2 - Xc ω q.val.1 q.val.2
  have hG : HasGaussianLaw U P :=
    (circleAverage_isGaussianProcess P X Xc hX hc).1.hasGaussianLaw_fun_sub
      (s := p.val) (t := q.val)
  have hmean : (∫ ω, U ω ∂P) = 0 := by
    have hi := integral_sub ((hc.2.1 p.val.1 p.val.2).integrable (by norm_num))
      ((hc.2.1 q.val.1 q.val.2).integrable (by norm_num))
    rw [hi, (circleAverage_isGaussianProcess P X Xc hX hc).2,
      (circleAverage_isGaussianProcess P X Xc hX hc).2, sub_self]
  have hmoment : (∫ ω, |U ω| ^ 8 ∂P) ≤ (C ^ 4 * A) * dist p q ^ 4 := by
    have hm := hasGaussianLaw_integral_abs_pow_le U hG hmean 4
      (circleAverage_increment_variance_le_dist_on_strip P X Xc hX hc S p q)
    change _ ≤ (C * dist p q) ^ 4 * A at hm
    exact hm.trans_eq (by ring)
  have hi : Integrable (fun ω => |U ω| ^ 8) P := by
    simpa only [Real.norm_eq_abs] using
      (hG.memLp (p := (8 : ℝ≥0∞)) (by norm_num)).integrable_norm_pow'
  have hlin := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (U ω)) 8))
  have hconv : (∫⁻ ω, edist (Xc ω p.val.1 p.val.2) (Xc ω q.val.1 q.val.2) ^ (8 : ℝ) ∂P) =
      ENNReal.ofReal (∫ ω, |U ω| ^ 8 ∂P) := by
    rw [hlin]
    apply lintegral_congr
    intro ω
    rw [edist_dist, Real.dist_eq]
    simpa only [ENNReal.rpow_ofNat, U] using (ENNReal.ofReal_pow (abs_nonneg (U ω)) 8).symm
  rw [hconv]
  have hb := ENNReal.ofReal_le_ofReal hmoment
  rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hC _) hA),
    ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist p q) 4] at hb
  change _ ≤ ENNReal.ofReal (C ^ 4 * A) * ENNReal.ofReal (dist p q) ^ 4 at hb
  rw [edist_dist, ENNReal.rpow_ofNat, ← ENNReal.ofReal_coe_nnreal (p := M)]
  exact hb

/-- Every L² circle representative has zero expectation. -/
theorem circleAverageL2_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (p : ℂ × ℝ) :
    (∫ ω, circleAverageL2 hc p ω ∂P) = 0 := by
  rw [integral_congr_ae (circleAverageL2_ae_eq hc p)]
  exact (circleAverage_isGaussianProcess P X Xc hX hc).2 p.1 p.2

/-- The actual circle covariance is the inner product of its given-space L² representatives. -/
theorem circleAverage_covariance_eq_inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (p q : ℂ × ℝ) :
    covariance (fun ω => Xc ω p.1 p.2) (fun ω => Xc ω q.1 q.2) P =
      inner ℝ (circleAverageL2 hc p) (circleAverageL2 hc q) := by
  let _ := hX.1
  rw [← covariance_congr_ae (circleAverageL2_ae_eq hc p) (circleAverageL2_ae_eq hc q),
    covariance_L2_eq, circleAverageL2_integral_eq_zero P X Xc hX hc,
    zero_mul, sub_zero]

/-- The all-center covariance is jointly continuous in both circle parameters, without
using the closed intersecting-circle series. -/
theorem continuous_circleAverage_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    Continuous (fun p : (ℂ × ℝ) × (ℂ × ℝ) =>
      covariance (fun ω => Xc ω p.1.1 p.1.2) (fun ω => Xc ω p.2.1 p.2.2) P) := by
  simp_rw [circleAverage_covariance_eq_inner P X Xc hX hc]
  exact ((continuous_circleAverageL2 P X Xc hX hc).comp continuous_fst).inner
    ((continuous_circleAverageL2 P X Xc hX hc).comp continuous_snd)

/-- Once a jointly measurable continuous coordinatewise version has been constructed, it satisfies
every clause of the conclusion of `DOZZ.exists_continuous_circleAverage`. -/
theorem continuous_circleAverage_version_spec {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc Y : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2))
    (heq : ∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) :
    IsCircleAverage P X Y ∧
      Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2)) ∧
      (∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) := by
  refine ⟨isCircleAverage_of_ae_eq P X Xc Y hc ?_ heq, hmeas, hcont, heq⟩
  intro r
  exact hmeas.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))




/-- Hilbert coordinates for the three-dimensional circle parameter space. -/
abbrev CircleParameter := WithLp 2 (ℂ × ℝ)

/-- Clamp the logarithmic radius to a width-one closed strip. -/
def circleStripParameter (S : ℝ) (p : CircleParameter) :
    {p : ℂ × ℝ // p.2 ∈ Icc S (S+1)} :=
  ⟨(p.fst, max S (min p.snd (S+1))), by
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩⟩

/-- Clamping does not increase the parameter distance. -/
theorem circleStripParameter_lipschitz (S : ℝ) :
    LipschitzWith 1 (circleStripParameter S) := by
  have hf : LipschitzWith 1 (fun p : CircleParameter => p.fst) :=
    LipschitzWith.of_edist_le (WithLp.edist_fst_le (p := 2))
  have hs : LipschitzWith 1 (fun p : CircleParameter => p.snd) :=
    LipschitzWith.of_edist_le (WithLp.edist_snd_le (p := 2))
  have hclip : LipschitzWith 1 (fun p : CircleParameter => max S (min p.snd (S+1))) := by
    simpa only [max_comm] using (hs.min_const (S+1)).max_const S
  intro p q
  change edist (p.fst, max S (min p.snd (S+1)))
    (q.fst, max S (min q.snd (S+1))) ≤ (1 : ℝ≥0∞) * edist p q
  simpa only [max_self, ENNReal.coe_one] using (hf.prodMk hclip) p q

/-- Pulling a Kolmogorov process back through a contraction preserves its constants. -/
theorem IsKolmogorovProcess.comp_one {T U Ω E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace U] [PseudoEMetricSpace E] [MeasurableSpace Ω]
    {X : T → Ω → E} {P : Measure Ω} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) {f : U → T} (hf : LipschitzWith 1 f) :
    IsKolmogorovProcess (fun t => X (f t)) P p q M := by
  refine ⟨fun s t => hX.measurablePair (f s) (f t), ?_, hX.p_pos, hX.q_pos⟩
  intro s t
  apply (hX.kolmogorovCondition (f s) (f t)).trans
  have hdist : edist (f s) (f t) ≤ edist s t := by
    simpa only [ENNReal.coe_one, one_mul] using hf s t
  exact mul_le_mul le_rfl (ENNReal.rpow_le_rpow hdist hX.q_pos.le) zero_le zero_le

/-- The Hilbert parameter carrier has real dimension three. -/
theorem finrank_circleParameter : Module.finrank ℝ CircleParameter = 3 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq, Module.finrank_prod]
  norm_num

/-- A clamped circle process has a measurable version with every sample path continuous. -/
theorem exists_continuous_clamped_circleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (S : ℝ) :
    ∃ Z : (ℂ × ℝ) → Ω → ℝ,
      (∀ p, Measurable (Z p)) ∧ (∀ ω, Continuous (fun p => Z p ω)) ∧
      ∀ p, Z p =ᵐ[P] fun ω => Xc ω p.1 (max S (min p.2 (S+1))) := by
  let _ := hX.1
  obtain ⟨M, hM⟩ := circleAverage_isKolmogorovProcess_on_strip P X Xc hX hc S
  have hK := DOZZ.Proofs.IsKolmogorovProcess.comp_one hM (circleStripParameter_lipschitz S)
  have hcover := isCoverWithBoundedCoveringNumber_balls CircleParameter
  rw [finrank_circleParameter] at hcover
  obtain ⟨Y, hYmeas, hYeq, hYholder⟩ := exists_modification_holder' hcover
    hK.IsAEKolmogorovProcess (fun n => by finiteness) (by norm_num) (by norm_num)
  have hYcont ω : Continuous (fun p => Y p ω) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨U, hU, hholder⟩ := hYholder ω p
    obtain ⟨C, hC⟩ := hholder (1/16) (by norm_num) (by norm_num)
    exact (hC.continuousOn (by norm_num)).continuousAt hU
  refine ⟨fun p => Y (WithLp.toLp 2 p), fun p => hYmeas _,
    fun ω => (hYcont ω).comp (WithLp.prod_continuous_toLp 2 ℂ ℝ), ?_⟩
  intro p
  exact hYeq (WithLp.toLp 2 p)


/-- A countable overlapping open radius cover, with a quarter-unit interior margin. -/
def circleVersionStrip (k : ℤ) : Set (ℂ × ℝ) :=
  {p | (k : ℝ)/2-1/4 < p.2 ∧ p.2 < (k : ℝ)/2+3/4}

/-- Each strip is open in both circle parameters. -/
theorem isOpen_circleVersionStrip (k : ℤ) : IsOpen (circleVersionStrip k) := by
  exact (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)

/-- Every circle parameter lies in one of the overlapping strips. -/
theorem exists_mem_circleVersionStrip (p : ℂ × ℝ) : ∃ k, p ∈ circleVersionStrip k := by
  refine ⟨⌊2*p.2⌋, ?_⟩
  have hlow := Int.floor_le (2*p.2)
  have hupp := Int.lt_floor_add_one (2*p.2)
  change (⌊2*p.2⌋ : ℝ)/2-1/4 < p.2 ∧ p.2 < (⌊2*p.2⌋ : ℝ)/2+3/4
  constructor <;> linarith

/-- On an open strip the clamped process equals the original process exactly. -/
theorem circleVersionStrip_clamp_eq {k : ℤ} {p : ℂ × ℝ}
    (hp : p ∈ circleVersionStrip k) :
    max ((k : ℝ)/2-1/4) (min p.2 (((k : ℝ)/2-1/4)+1)) = p.2 := by
  rw [min_eq_left (by change p.2 ≤ _; dsimp [circleVersionStrip] at hp; linarith [hp.2]),
    max_eq_right hp.1.le]

/-- Jointly continuous modification of the given witness (see [KRV, §2.1]). Continuity is not
asserted for an arbitrary original witness. -/
theorem exists_continuous_circleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    ∃ Y : Ω → ℂ → ℝ → ℝ,
      IsCircleAverage P X Y ∧
      Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2)) ∧
      (∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) := by
  have hlocal (k : ℤ) := exists_continuous_clamped_circleAverage P X Xc hX hc ((k : ℝ)/2-1/4)
  choose Z hZmeas hZcont hZeq using hlocal
  have hZeq' k p (hp : p ∈ circleVersionStrip k) :
      Z k p =ᵐ[P] fun ω => Xc ω p.1 p.2 := by
    simpa only [circleVersionStrip_clamp_eq hp] using hZeq k p
  obtain ⟨Y, hYmeas, hYcont, hYeq, hYjoint⟩ :=
    exists_continuous_modification_of_open_cover P (fun p ω => Xc ω p.1 p.2)
      circleVersionStrip isOpen_circleVersionStrip exists_mem_circleVersionStrip
      Z hZmeas hZcont hZeq'
  exact ⟨fun ω x r => Y (x,r) ω,
    continuous_circleAverage_version_spec P X Xc (fun ω x r => Y (x,r) ω)
      hc hYjoint (ae_of_all P hYcont) (fun x r => hYeq (x,r))⟩


end DOZZ.Proofs
