/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import DOZZ.Hypergeom.Planar.Beta
public import DOZZ.Hypergeom.Planar.TwoPointRpow

/-! Gaussian and Laplace foundations for the positive planar Riesz convolution. -/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace DOZZ.Proofs

/-- The positive real beta integral in terms of Euler's Gamma function. -/
theorem beta_integral_gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ θ : ℝ in Ioc 0 1, θ ^ (a - 1) * (1 - θ) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hbetaC := Complex.betaIntegral_eq_Gamma_mul_div
    ((a : ℝ) : ℂ) ((b : ℝ) : ℂ) (by simpa using ha) (by simpa using hb)
  rw [betaIntegral_ofReal] at hbetaC
  apply Complex.ofReal_injective
  have hbetaC' := hbetaC
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hbetaC'
  simpa [Complex.ofReal_mul, Complex.ofReal_div] using hbetaC'

private theorem beta_tail_change_variables (x y : ℝ) :
    (∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))) =
      ∫ t : ℝ in Ioc 0 1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
  let f : ℝ → ℝ := fun v => v / (1 + v)
  have hImage : f '' Ioi (0 : ℝ) = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : 0 < v := mem_Ioi.mp hv
      have hden : 0 < 1 + v := by linarith
      constructor
      · exact div_pos hv' hden
      · rw [div_lt_one hden]
        linarith
    · rintro ⟨ht, ht1⟩
      refine ⟨t / (1 - t), div_pos ht (sub_pos.mpr ht1), ?_⟩
      dsimp [f]
      field_simp
      ring
  have hInj : InjOn f (Ioi (0 : ℝ)) := by
    intro v hv w hw h
    have hvpos : 0 < v := mem_Ioi.mp hv
    have hwpos : 0 < w := mem_Ioi.mp hw
    have hv' : 1 + v ≠ 0 := by linarith
    have hw' : 1 + w ≠ 0 := by linarith
    have hcross : v * (1 + w) = w * (1 + v) :=
      (div_eq_div_iff hv' hw').mp (by simpa [f] using h)
    nlinarith [hcross]
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f ((1 + v) ^ 2)⁻¹ (Ioi (0 : ℝ)) v := by
    intro v hv
    have hvpos : 0 < v := mem_Ioi.mp hv
    have hd : 0 < 1 + v := by linarith
    have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 v := by
      convert (hasDerivAt_id v).const_add 1 using 1
      · funext t
        simp
    have hdiv := (hasDerivAt_id v).div hden hd.ne'
    have hfun : HasDerivAt (fun t : ℝ => t / (1 + t)) ((1 + v) ^ 2)⁻¹ v := by
      convert hdiv using 1
      · rfl
      · field_simp
        simp only [id_eq]
        ring
    simpa only [f] using hfun.hasDerivWithinAt
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := f) (f' := fun v => ((1 + v) ^ 2)⁻¹)
    measurableSet_Ioi hderiv hInj (fun t : ℝ => t ^ (x - 1) * (1 - t) ^ (y - 1))
  rw [hImage] at hchange
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc] at hchange
  calc
    ∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))
        = ∫ v : ℝ in Ioi 0,
          |((1 + v) ^ 2)⁻¹| * ((f v) ^ (x - 1) * (1 - f v) ^ (y - 1)) := by
            symm
            apply setIntegral_congr_fun measurableSet_Ioi
            intro v hv
            have hv0 : 0 < v := hv
            have hd : 0 < 1 + v := by linarith
            change |((1 + v) ^ 2)⁻¹| *
                ((f v) ^ (x - 1) * (1 - f v) ^ (y - 1)) =
              v ^ (x - 1) * (1 + v) ^ (-(x + y))
            have hcomp : 1 - f v = 1 / (1 + v) := by
              dsimp [f]
              field_simp
              ring
            rw [hcomp, abs_of_pos (by positivity)]
            rw [← Real.rpow_natCast (1 + v) 2]
            rw [Real.div_rpow hv0.le hd.le, Real.div_rpow zero_le_one hd.le]
            rw [Real.one_rpow]
            rw [Real.rpow_neg hd.le]
            have hpowers : (1 + v) ^ (2 : ℝ) * (1 + v) ^ (x - 1) * (1 + v) ^ (y - 1) =
                (1 + v) ^ (x + y) := by
              rw [← Real.rpow_add hd]
              rw [← Real.rpow_add hd]
              congr 1
              ring
            field_simp [ne_of_gt (Real.rpow_pos_of_pos hd (x - 1)),
              ne_of_gt (Real.rpow_pos_of_pos hd (y - 1)),
              ne_of_gt (Real.rpow_pos_of_pos hd (x + y))]
            rw [← hpowers]
            ring_nf
    _ = ∫ t : ℝ in Ioc 0 1, t ^ (x - 1) * (1 - t) ^ (y - 1) := hchange.symm

/-- The positive beta integral on the positive half-line. -/
theorem beta_tail_integral_gamma (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
  rw [beta_tail_change_variables]
  exact beta_integral_gamma x y hx hy

private theorem beta_tail_integrable (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => v ^ (x - 1) * (1 + v) ^ (-(x + y))) (Ioi 0) := by
  by_contra hnot
  have hzero : (∫ v : ℝ in Ioi 0,
      v ^ (x - 1) * (1 + v) ^ (-(x + y))) = 0 := integral_undef hnot
  have hBeta := beta_tail_integral_gamma x y hx hy
  rw [hzero] at hBeta
  have hpos : 0 < Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
    exact div_pos (mul_pos (Real.Gamma_pos_of_pos hx) (Real.Gamma_pos_of_pos hy))
      (Real.Gamma_pos_of_pos (add_pos hx hy))
  linarith [hBeta]

/-- Euler's Gamma integral with a positive exponential rate. -/
theorem integral_laplace_power (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    ∫ t : ℝ in Ioi 0, t ^ (a - 1) * Real.exp (-(x * t)) =
      Real.Gamma a * x ^ (-a) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hx]
  calc
    (1 / x) ^ a * Real.Gamma a = x ^ (-a) * Real.Gamma a := by
      rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
    _ = Real.Gamma a * x ^ (-a) := by ring

private theorem lintegral_laplace_power (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
      (t ^ (a - 1) * Real.exp (-(x * t)))) =
      ENNReal.ofReal (Real.Gamma a * x ^ (-a)) := by
  have hInt : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(x * t))) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := a - 1) (b := x) (by linarith) one_pos hx using 1
    ext t
    simp only [Real.rpow_one, neg_mul]
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => t ^ (a - 1) * Real.exp (-(x * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (mem_Ioi.mp ht)) _)
      (Real.exp_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNonneg, integral_laplace_power a x ha hx]

private theorem lintegral_laplace_power_mul (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
      (t ^ (a - 1) * Real.exp (-(r ^ 2 * t)))) =
      ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (r ^ (-2 * a)) := by
  rw [lintegral_laplace_power a (r ^ 2) ha (by positivity)]
  have hpow : (r ^ (2 : ℕ)) ^ (-a) = r ^ (-2 * a) := by
    calc
      (r ^ (2 : ℕ)) ^ (-a) = (r ^ (2 : ℝ)) ^ (-a) := by
        exact congrArg (fun x : ℝ => x ^ (-a)) (Real.rpow_natCast r 2).symm
      _ = r ^ (2 * (-a)) := (Real.rpow_mul hr.le 2 (-a)).symm
      _ = r ^ (-2 * a) := by congr 1; ring
  rw [hpow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.Gamma a)]

private theorem lintegral_beta_tail (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫⁻ v : ℝ in Ioi 0, ENNReal.ofReal
      (v ^ (x - 1) * (1 + v) ^ (-(x + y)))) =
      ENNReal.ofReal (Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)) := by
  have hInt := beta_tail_integrable x y hx hy
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun v : ℝ => v ^ (x - 1) * (1 + v) ^ (-(x + y))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (mem_Ioi.mp hv)) _)
      (Real.rpow_nonneg (by linarith [mem_Ioi.mp hv]) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNonneg,
    beta_tail_integral_gamma x y hx hy]

private theorem lintegral_scale_Ioi (t : ℝ) (ht : 0 < t)
    (u : ℝ → ENNReal) :
    (∫⁻ s : ℝ in Ioi 0, u s) =
      ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal t * u (t * y) := by
  let f : ℝ → ℝ := fun y => t * y
  have hImage : f '' Ioi (0 : ℝ) = Ioi 0 := by
    ext s
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mul_pos ht hy
    · intro hs
      refine ⟨s / t, div_pos hs ht, ?_⟩
      dsimp [f]
      field_simp
  have hmono : MonotoneOn f (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left hxy ht.le
  have hderiv : ∀ y ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f t (Ioi (0 : ℝ)) y := by
    intro y hy
    have hfun : HasDerivAt f t y := by
      simpa [f, mul_comm] using (hasDerivAt_id y).const_mul t
    exact hfun.hasDerivWithinAt
  have hchange := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    measurableSet_Ioi hderiv hmono u
  rw [hImage] at hchange
  simpa [f] using hchange

private theorem laplace_parameter_scale_identity (a b R t y : ℝ)
    (ht : 0 < t) (hy : 0 < y) :
    t * (t ^ (a - 1) * (t * y) ^ (b - 1) / (t + t * y) *
    Real.exp (-((t * (t * y) / (t + t * y)) * R ^ (2 : ℝ)))) =
    (y ^ (b - 1) / (1 + y)) *
      (t ^ (a + b - 2) * Real.exp (-((R ^ (2 : ℝ) * y / (1 + y)) * t))) := by
  have hden : t + t * y = t * (1 + y) := by ring
  have hsum : t ^ (a - 1) * t ^ (b - 1) = t ^ (a + b - 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hbase : t * (t ^ (a - 1) * t ^ (b - 1)) / (t + t * y) =
      t ^ (a + b - 2) / (1 + y) := by
    rw [hden, hsum]
    field_simp [ne_of_gt ht, ne_of_gt (by linarith : 0 < 1 + y)]
  have hexp : -((t * (t * y) / (t + t * y)) * R ^ (2 : ℝ)) =
      -((R ^ (2 : ℝ) * y / (1 + y)) * t) := by
    rw [hden]
    field_simp [ne_of_gt ht, ne_of_gt (by linarith : 0 < 1 + y)]
  calc
    _ = (t * (t ^ (a - 1) * t ^ (b - 1)) / (t + t * y)) *
          y ^ (b - 1) * Real.exp (-((t * (t * y) / (t + t * y)) * R ^ (2 : ℝ))) := by
            rw [Real.mul_rpow ht.le hy.le]
            ring
    _ = _ := by rw [hbase, hexp]; ring

/-- Evaluation of the scale-ratio parameter integral produced by the positive Laplace kernels.
The substitution `s = t y` reduces it to one Gamma and one beta integral. -/
theorem laplace_scale_ratio_lintegral (a b R : ℝ) (ha' : a < 1)
    (hb' : b < 1) (hab : 1 < a + b) (hR : 0 < R) :
    (∫⁻ y : ℝ in Ioi 0,
        ENNReal.ofReal (y ^ (b - 1) / (1 + y)) *
        (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
          (t ^ (a + b - 2) * Real.exp (-((R ^ (2 : ℝ) * y / (1 + y)) * t))))) =
      ENNReal.ofReal (Real.Gamma (a + b - 1) * R ^ (-2 * (a + b - 1)) *
        (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))) := by
  let p := a + b - 1
  have hp : 0 < p := by dsimp [p]; linarith
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have hscale : 0 < Real.Gamma p * R ^ (-2 * p) :=
    mul_pos (Real.Gamma_pos_of_pos hp) (Real.rpow_pos_of_pos hR _)
  calc
    (∫⁻ y : ℝ in Ioi 0,
        ENNReal.ofReal (y ^ (b - 1) / (1 + y)) *
        (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
          (t ^ (a + b - 2) * Real.exp (-((R ^ (2 : ℝ) * y / (1 + y)) * t))))) =
      ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal
        ((Real.Gamma p * R ^ (-2 * p)) *
          (y ^ ((1 - a) - 1) * (1 + y) ^ (-((1 - a) + (1 - b))))) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
            have hypos : 0 < y := mem_Ioi.mp hy
            have hden : 0 < 1 + y := by linarith
            have hc : 0 < R ^ (2 : ℝ) * y / (1 + y) := by positivity
            rw [show a + b - 2 = p - 1 by dsimp [p]; ring]
            rw [lintegral_laplace_power p (R ^ (2 : ℝ) * y / (1 + y)) hp hc]
            have hRpow : (R ^ (2 : ℝ)) ^ (-p) = R ^ (-2 * p) := by
              calc
                (R ^ (2 : ℝ)) ^ (-p) = R ^ (2 * (-p)) :=
                  (Real.rpow_mul hR.le 2 (-p)).symm
                _ = R ^ (-2 * p) := by congr 1; ring_nf
            have hfactor : (R ^ (2 : ℝ) * y / (1 + y)) ^ (-p) =
                R ^ (-2 * p) * y ^ (-p) * (1 + y) ^ p := by
              rw [Real.div_rpow (by positivity : 0 ≤ R ^ (2 : ℝ) * y) hden.le,
                Real.mul_rpow (Real.rpow_nonneg hR.le _) hypos.le, hRpow,
                Real.rpow_neg hden.le]
              field_simp
            have hysum : y ^ (b - 1) * y ^ (-p) = y ^ ((1 - a) - 1) := by
              rw [← Real.rpow_add hypos]
              congr 1
              dsimp [p]
              ring_nf
            have hdenpow : (1 + y) ^ p / (1 + y) =
                (1 + y) ^ (-((1 - a) + (1 - b))) := by
              rw [← Real.rpow_sub_one hden.ne']
              congr 1
              dsimp [p]
              ring_nf
            have hreal : y ^ (b - 1) / (1 + y) *
                (Real.Gamma p * (R ^ (2 : ℝ) * y / (1 + y)) ^ (-p)) =
                (Real.Gamma p * R ^ (-2 * p)) *
                  (y ^ ((1 - a) - 1) * (1 + y) ^ (-((1 - a) + (1 - b)))) := by
              calc
                _ = (Real.Gamma p * R ^ (-2 * p)) *
                    ((y ^ (b - 1) * y ^ (-p)) * ((1 + y) ^ p / (1 + y))) := by
                      rw [hfactor]
                      field_simp [ne_of_gt hden]
                _ = _ := by rw [hysum, hdenpow]
            rw [← ENNReal.ofReal_mul
              (by positivity : 0 ≤ y ^ (b - 1) / (1 + y))]
            exact congrArg ENNReal.ofReal hreal
    _ = ENNReal.ofReal (Real.Gamma p * R ^ (-2 * p)) *
        (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal
          (y ^ ((1 - a) - 1) * (1 + y) ^ (-((1 - a) + (1 - b))))) := by
            calc
              (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal
                  ((Real.Gamma p * R ^ (-2 * p)) *
                    (y ^ ((1 - a) - 1) * (1 + y) ^ (-((1 - a) + (1 - b)))))) =
                ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (Real.Gamma p * R ^ (-2 * p)) *
                  ENNReal.ofReal (y ^ ((1 - a) - 1) * (1 + y) ^ (-((1 - a) + (1 - b)))) := by
                    apply lintegral_congr_ae
                    filter_upwards [] with y
                    exact ENNReal.ofReal_mul (le_of_lt hscale)
              _ = _ := by rw [lintegral_const_mul _ (by fun_prop)]
    _ = ENNReal.ofReal (Real.Gamma p * R ^ (-2 * p) *
        (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))) := by
            rw [lintegral_beta_tail (1 - a) (1 - b) h1a h1b]
            rw [show (1 - a) + (1 - b) = 2 - a - b by ring]
            rw [← ENNReal.ofReal_mul (le_of_lt hscale)]
    _ = _ := by rw [show p = a + b - 1 by rfl]

/-- The two positive Laplace parameters reduce to the scale-ratio integral. -/
theorem laplace_parameter_lintegral (a b R : ℝ) (ha' : a < 1)
    (hb' : b < 1) (hab : 1 < a + b) (hR : 0 < R) :
    (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
        Real.exp (-((t * s / (t + s)) * R ^ (2 : ℝ))))) =
      ENNReal.ofReal (Real.Gamma (a + b - 1) * R ^ (-2 * (a + b - 1)) *
        (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))) := by
  let F : ℝ → ℝ → ENNReal := fun t s => ENNReal.ofReal
    (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
      Real.exp (-((t * s / (t + s)) * R ^ (2 : ℝ))))
  calc
    (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, F t s) =
        ∫⁻ t : ℝ in Ioi 0, ∫⁻ y : ℝ in Ioi 0,
          ENNReal.ofReal t * F t (t * y) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact lintegral_scale_Ioi t ht (F t)
    _ = ∫⁻ y : ℝ in Ioi 0, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal t * F t (t * y) := by
            rw [lintegral_lintegral_swap (by fun_prop)]
    _ = ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (y ^ (b - 1) / (1 + y)) *
          (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
            (t ^ (a + b - 2) * Real.exp (-((R ^ (2 : ℝ) * y / (1 + y)) * t)))) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
            have hypos : 0 < y := mem_Ioi.mp hy
            calc
              (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal t * F t (t * y)) =
                  ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (y ^ (b - 1) / (1 + y)) *
                    ENNReal.ofReal (t ^ (a + b - 2) *
                      Real.exp (-((R ^ (2 : ℝ) * y / (1 + y)) * t))) := by
                    apply lintegral_congr_ae
                    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
                    have htpos : 0 < t := mem_Ioi.mp ht
                    have hreal := laplace_parameter_scale_identity a b R t y htpos hypos
                    calc
                      ENNReal.ofReal t * F t (t * y) =
                          ENNReal.ofReal (t * (t ^ (a - 1) * (t * y) ^ (b - 1) /
                            (t + t * y) *
                              Real.exp (-((t * (t * y) / (t + t * y)) * R ^ (2 : ℝ))))) := by
                                dsimp [F]
                                rw [← ENNReal.ofReal_mul htpos.le]
                      _ = ENNReal.ofReal (y ^ (b - 1) / (1 + y) *
                            (t ^ (a + b - 2) *
                              Real.exp (-((R ^ (2 : ℝ) * y / (1 + y)) * t)))) :=
                            congrArg ENNReal.ofReal hreal
                      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]
              _ = _ := by rw [lintegral_const_mul _ (by fun_prop)]
    _ = _ := laplace_scale_ratio_lintegral a b R ha' hb' hab hR


/-- Translating a planar Gaussian does not change its integral. -/
theorem integral_real_gaussian_shift (a : ℝ) (ha : 0 < a) (w : ℂ) :
    ∫ u : ℂ, Real.exp (-a * ‖u - w‖ ^ 2) = Real.pi / a := by
  have hgauss : ∫ u : ℂ, Real.exp (-a * ‖u‖ ^ 2) = Real.pi / a := by
    simpa [Complex.finrank_real_complex] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) ha)
  have hshift := (MeasureTheory.measurePreserving_add_right volume w).integral_comp
    (Homeomorph.addRight w).measurableEmbedding
    (fun u : ℂ => Real.exp (-a * ‖u - w‖ ^ 2))
  calc
    ∫ u : ℂ, Real.exp (-a * ‖u - w‖ ^ 2) =
        ∫ u : ℂ, Real.exp (-a * ‖u‖ ^ 2) := by
          symm
          simpa only [add_sub_cancel_right] using hshift
    _ = Real.pi / a := hgauss

/-- The convolution of two planar Gaussians, obtained by completing the square. -/
theorem integral_planar_gaussian_product (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (z : ℂ) :
    ∫ u : ℂ, Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2) =
      (Real.pi / (s + t)) * Real.exp (-(s * t / (s + t)) * ‖z‖ ^ 2) := by
  let q := s + t
  let c := t / q
  have hq : 0 < q := by dsimp [q]; linarith
  have hc : 0 < c := div_pos ht hq
  have hsq (u : ℂ) :
      s * ‖u‖ ^ 2 + t * ‖u - z‖ ^ 2 =
        q * ‖u - c • z‖ ^ 2 + (s * t / q) * ‖z‖ ^ 2 := by
    have h1 := norm_sub_sq_real u z
    have h2 := norm_sub_sq_real u (c • z)
    rw [h1, h2, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    dsimp [q, c]
    field_simp
    ring
  have hfun (u : ℂ) :
      Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2) =
        Real.exp (-q * ‖u - c • z‖ ^ 2) * Real.exp (-(s * t / q) * ‖z‖ ^ 2) := by
    calc
      _ = Real.exp (-(s * ‖u‖ ^ 2 + t * ‖u - z‖ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-(q * ‖u - c • z‖ ^ 2 + (s * t / q) * ‖z‖ ^ 2)) := by rw [hsq]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    ∫ u : ℂ, Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2) =
        ∫ u : ℂ, Real.exp (-q * ‖u - c • z‖ ^ 2) *
          Real.exp (-(s * t / q) * ‖z‖ ^ 2) := by
            apply integral_congr_ae
            filter_upwards [] with u
            exact hfun u
    _ = (∫ u : ℂ, Real.exp (-q * ‖u - c • z‖ ^ 2)) *
          Real.exp (-(s * t / q) * ‖z‖ ^ 2) := by rw [integral_mul_const]
    _ = _ := by
      rw [integral_real_gaussian_shift q hq (c • z)]

private theorem lintegral_planar_gaussian_product (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (z : ℂ) :
    (∫⁻ u : ℂ, ENNReal.ofReal
      (Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2))) =
      ENNReal.ofReal ((Real.pi / (s + t)) *
        Real.exp (-(s * t / (s + t)) * ‖z‖ ^ 2)) := by
  let q := s + t
  let c := t / q
  have hq : 0 < q := by dsimp [q]; linarith
  have hc : 0 < c := div_pos ht hq
  have hsq (u : ℂ) :
      s * ‖u‖ ^ 2 + t * ‖u - z‖ ^ 2 =
        q * ‖u - c • z‖ ^ 2 + (s * t / q) * ‖z‖ ^ 2 := by
    have h1 := norm_sub_sq_real u z
    have h2 := norm_sub_sq_real u (c • z)
    rw [h1, h2, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    dsimp [q, c]
    field_simp
    ring
  have hfun (u : ℂ) :
      Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2) =
        Real.exp (-q * ‖u - c • z‖ ^ 2) *
          Real.exp (-(s * t / q) * ‖z‖ ^ 2) := by
    calc
      _ = Real.exp (-(s * ‖u‖ ^ 2 + t * ‖u - z‖ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-(q * ‖u - c • z‖ ^ 2 + (s * t / q) * ‖z‖ ^ 2)) := by
        rw [hsq]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hbaseC : Integrable (fun u : ℂ => Complex.exp (-(q : ℂ) * ‖u‖ ^ 2)) := by
    simpa [Complex.ofReal_exp] using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := ℂ) (b := (q : ℂ)) (by simp [hq]) 0 (0 : ℂ))
  have hbase : Integrable (fun u : ℂ => Real.exp (-q * ‖u‖ ^ 2)) := by
    apply hbaseC.re.congr
    filter_upwards [] with u
    rw [show (-(q : ℂ) * ‖u‖ ^ 2) = (-(q * ‖u‖ ^ 2) : ℝ) by push_cast; ring]
    rw [show -q * ‖u‖ ^ 2 = -(q * ‖u‖ ^ 2) by ring]
    exact Complex.exp_ofReal_re _
  have hshift : Integrable (fun u : ℂ => Real.exp (-q * ‖u - c • z‖ ^ 2)) := by
    simpa [sub_eq_add_neg, add_comm] using hbase.comp_add_left (-(c • z))
  have hprod : Integrable (fun u : ℂ =>
      Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2)) := by
    have hconst := hshift.const_mul (Real.exp (-(s * t / q) * ‖z‖ ^ 2))
    apply hconst.congr
    filter_upwards [] with u
    calc
      Real.exp (-(s * t / q) * ‖z‖ ^ 2) * Real.exp (-q * ‖u - c • z‖ ^ 2) =
          Real.exp (-q * ‖u - c • z‖ ^ 2) * Real.exp (-(s * t / q) * ‖z‖ ^ 2) := by ring
      _ = Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2) := (hfun u).symm
  have hnonneg : 0 ≤ᵐ[volume]
      (fun u : ℂ => Real.exp (-s * ‖u‖ ^ 2) * Real.exp (-t * ‖u - z‖ ^ 2)) := by
    filter_upwards [] with u
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  rw [← ofReal_integral_eq_lintegral_ofReal hprod hnonneg,
    integral_planar_gaussian_product s t hs ht z]

private theorem lintegral_laplace_gaussian_product (c t s : ℝ)
    (ht : 0 < t) (hs : 0 < s) (z : ℂ) :
    (∫⁻ u : ℂ, ENNReal.ofReal c * ENNReal.ofReal
      (Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s)))) =
      ENNReal.ofReal c * ENNReal.ofReal
        ((Real.pi / (t + s)) * Real.exp (-(t * s / (t + s)) * ‖z‖ ^ 2)) := by
  calc
    _ = ENNReal.ofReal c * (∫⁻ u : ℂ, ENNReal.ofReal
        (Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s)))) := by
          rw [lintegral_const_mul _ (by fun_prop)]
    _ = _ := by
          have hExp :
              (∫⁻ u : ℂ, ENNReal.ofReal
                (Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s)))) =
                (∫⁻ u : ℂ, ENNReal.ofReal
                  (Real.exp (-t * ‖u‖ ^ 2) * Real.exp (-s * ‖u - z‖ ^ 2))) := by
            apply lintegral_congr_ae
            filter_upwards [] with u
            apply congrArg ENNReal.ofReal
            congr 1
            · ring_nf
            · ring_nf
          rw [hExp, lintegral_planar_gaussian_product t s ht hs z]

private theorem laplace_gaussian_parameter_factor (a b t s : ℝ)
    (ht : 0 < t) (hs : 0 < s) (z : ℂ) :
    ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1)) *
        ENNReal.ofReal ((Real.pi / (t + s)) *
          Real.exp (-(t * s / (t + s)) * ‖z‖ ^ 2)) =
      ENNReal.ofReal Real.pi * ENNReal.ofReal
        (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
          Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ)))) := by
  have hcoef : 0 ≤ t ^ (a - 1) * s ^ (b - 1) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.rpow_nonneg (le_of_lt hs) _)
  have hnorm : ‖z‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℝ) :=
    (Real.rpow_natCast ‖z‖ 2).symm
  have harg : -(t * s / (t + s)) * ‖z‖ ^ (2 : ℕ) =
      -((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ)) := by
    rw [hnorm]
    ring_nf
  have hexp : Real.exp (-(t * s / (t + s)) * ‖z‖ ^ (2 : ℕ)) =
      Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ))) := by
    apply congrArg Real.exp
    exact harg
  calc
    _ = ENNReal.ofReal
        ((t ^ (a - 1) * s ^ (b - 1)) *
          ((Real.pi / (t + s)) * Real.exp (-(t * s / (t + s)) * ‖z‖ ^ 2))) := by
            rw [← ENNReal.ofReal_mul hcoef]
    _ = ENNReal.ofReal
        (Real.pi * (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
          Real.exp (-((t * s / (t + s)) * ‖z‖ ^ 2)))) := by
            apply congrArg ENNReal.ofReal
            rw [hexp]
            rw [hnorm]
            ring_nf
    _ = _ := by
      rw [← ENNReal.ofReal_mul Real.pi_pos.le]
      apply congrArg ENNReal.ofReal
      rw [hnorm]

private theorem lintegral_const_mul_riesz_parameters (a b : ℝ) (z : ℂ) :
    (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal Real.pi * ENNReal.ofReal
        (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
          Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ))))) =
      ENNReal.ofReal Real.pi * (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
          Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ))))) := by
  calc
    _ = ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal Real.pi * (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
          Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ))))) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [lintegral_const_mul _ (by fun_prop)]
    _ = _ := by rw [lintegral_const_mul _ (by fun_prop)]

private theorem positive_riesz_lintegral_scaled (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) (hb' : b < 1)
    (hab : 1 < a + b) (hz : z ≠ 0) :
    (ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (Real.Gamma b)) *
        (∫⁻ u : ℂ, ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) =
      ENNReal.ofReal Real.pi * ENNReal.ofReal
        (Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
          (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))) := by
  let A : ℂ → ℝ → ENNReal := fun u t => ENNReal.ofReal
    (t ^ (a - 1) * Real.exp (-(‖u‖ ^ 2 * t)))
  let B : ℂ → ℝ → ENNReal := fun u s => ENNReal.ofReal
    (s ^ (b - 1) * Real.exp (-(‖u - z‖ ^ 2 * s)))
  let F : ℂ → ℝ → ℝ → ENNReal := fun u t s => A u t * B u s
  let C : ENNReal := ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (Real.Gamma b)
  let T : ℝ := Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
    (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))
  have hR : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hCpos : 0 < Real.Gamma a * Real.Gamma b :=
    mul_pos hGa hGb
  have hC0 : C ≠ 0 := by
    dsimp [C]
    apply mul_ne_zero
    · exact ENNReal.ofReal_ne_zero_iff.mpr hGa
    · exact ENNReal.ofReal_ne_zero_iff.mpr hGb
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ u ∂volume,
      C * ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b)) =
        ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, F u t s := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume z] with u hu0 huz
    have hA := lintegral_laplace_power_mul a ‖u‖ ha (norm_pos_iff.mpr hu0)
    have hB := lintegral_laplace_power_mul b ‖u - z‖ hb
      (norm_pos_iff.mpr (sub_ne_zero.mpr huz))
    calc
      C * ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b)) =
          (ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (‖u‖ ^ (-2 * a))) *
            (ENNReal.ofReal (Real.Gamma b) * ENNReal.ofReal (‖u - z‖ ^ (-2 * b))) := by
              dsimp [C]
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg u) _)]
              ring
      _ = (∫⁻ t : ℝ in Ioi 0, A u t) *
            (∫⁻ s : ℝ in Ioi 0, B u s) := by
              dsimp [A, B]
              rw [hA, hB]
      _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, A u t * B u s :=
            (lintegral_lintegral_mul (by fun_prop) (by fun_prop)).symm
  have hFactor (u : ℂ) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
      F u t s = ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1)) *
        ENNReal.ofReal (Real.exp (-(‖u‖ ^ 2 * t)) *
          Real.exp (-(‖u - z‖ ^ 2 * s))) := by
    dsimp [F, A, B]
    calc
      _ = ENNReal.ofReal
            ((t ^ (a - 1) * Real.exp (-(‖u‖ ^ 2 * t))) *
              (s ^ (b - 1) * Real.exp (-(‖u - z‖ ^ 2 * s)))) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((t ^ (a - 1) * s ^ (b - 1)) *
            (Real.exp (-(‖u‖ ^ 2 * t)) *
              Real.exp (-(‖u - z‖ ^ 2 * s)))) := by
              congr 1
              ring
      _ = _ := by
              rw [ENNReal.ofReal_mul (mul_nonneg
                (Real.rpow_nonneg (le_of_lt ht) _) (Real.rpow_nonneg (le_of_lt hs) _))]
  have hswap :
      (∫⁻ u : ℂ, ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, F u t s) =
        ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, ∫⁻ u : ℂ, F u t s := by
    calc
      _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ u : ℂ, ∫⁻ s : ℝ in Ioi 0, F u t s := by
            rw [lintegral_lintegral_swap (by fun_prop)]
      _ = _ := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            rw [lintegral_lintegral_swap (by fun_prop)]
  have hgauss :
      (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, ∫⁻ u : ℂ, F u t s) =
        ENNReal.ofReal Real.pi *
          (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
            ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
              Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ))))) := by
    exact (calc
      _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
            ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1)) *
              ENNReal.ofReal ((Real.pi / (t + s)) *
                Real.exp (-(t * s / (t + s)) * ‖z‖ ^ 2)) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
              have hF :
                  (∫⁻ u : ℂ, F u t s) =
                    (∫⁻ u : ℂ, ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1)) *
                      ENNReal.ofReal (Real.exp (-(‖u‖ ^ 2 * t)) *
                        Real.exp (-(‖u - z‖ ^ 2 * s)))) := by
                apply lintegral_congr_ae
                filter_upwards [] with u
                exact hFactor u t s (mem_Ioi.mp ht) (mem_Ioi.mp hs)
              exact hF.trans (lintegral_laplace_gaussian_product
                (t ^ (a - 1) * s ^ (b - 1)) t s (mem_Ioi.mp ht) (mem_Ioi.mp hs) z)
      _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
            ENNReal.ofReal Real.pi * ENNReal.ofReal
              (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
                Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ)))) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
              exact laplace_gaussian_parameter_factor a b t s
                (mem_Ioi.mp ht) (mem_Ioi.mp hs) z
      _ = ENNReal.ofReal Real.pi *
            (∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0,
              ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
                Real.exp (-((t * s / (t + s)) * ‖z‖ ^ (2 : ℝ))))) := by
              exact lintegral_const_mul_riesz_parameters a b z
    )
  change C * (∫⁻ u : ℂ,
      ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) =
    ENNReal.ofReal Real.pi * ENNReal.ofReal T
  calc
    _ = ∫⁻ u : ℂ, C *
        ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b)) := by
          symm
          rw [lintegral_const_mul C (by fun_prop)]
    _ = ∫⁻ u : ℂ, ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, F u t s := by
          apply lintegral_congr_ae
          exact hpoint
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ s : ℝ in Ioi 0, ∫⁻ u : ℂ, F u t s := hswap
    _ = ENNReal.ofReal Real.pi * ENNReal.ofReal T := by
          rw [hgauss, laplace_parameter_lintegral a b ‖z‖ ha' hb' hab hR]

private theorem positive_riesz_lintegral_formula (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) (hb' : b < 1)
    (hab : 1 < a + b) (hz : z ≠ 0) :
    (∫⁻ u : ℂ, ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) =
      ENNReal.ofReal (Real.pi *
        (Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
          (Real.Gamma (1 - a) * Real.Gamma (1 - b) /
            (Real.Gamma a * Real.Gamma b * Real.Gamma (2 - a - b))))) := by
  let C : ENNReal := ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (Real.Gamma b)
  let T : ℝ := Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
    (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hCpos : 0 < Real.Gamma a * Real.Gamma b := mul_pos hGa hGb
  have hC0 : C ≠ 0 := by
    dsimp [C]
    apply mul_ne_zero
    · exact ENNReal.ofReal_ne_zero_iff.mpr hGa
    · exact ENNReal.ofReal_ne_zero_iff.mpr hGb
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hCeq : C = ENNReal.ofReal (Real.Gamma a * Real.Gamma b) := by
    dsimp [C]
    rw [ENNReal.ofReal_mul (by positivity)]
  have hformula : Real.pi * T / (Real.Gamma a * Real.Gamma b) =
      Real.pi * Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
        (Real.Gamma (1 - a) * Real.Gamma (1 - b) /
          (Real.Gamma a * Real.Gamma b * Real.Gamma (2 - a - b))) := by
    dsimp [T]
    field_simp [hCpos.ne', (Real.Gamma_pos_of_pos (by linarith : 0 < 2 - a - b)).ne']
  have hscaled := positive_riesz_lintegral_scaled a b z ha ha' hb hb' hab hz
  have hquot :
      (∫⁻ u : ℂ, ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) =
        ENNReal.ofReal (Real.pi * T / (Real.Gamma a * Real.Gamma b)) := by
    apply (ENNReal.mul_left_inj hC0 hCtop).mp
    calc
      _ = C * (∫⁻ u : ℂ,
          ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) := by
            rw [mul_comm]
      _ = ENNReal.ofReal Real.pi * ENNReal.ofReal T := hscaled
      _ = ENNReal.ofReal (Real.pi * T / (Real.Gamma a * Real.Gamma b)) * C := by
            rw [hCeq, ENNReal.ofReal_div_of_pos hCpos]
            rw [ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hCpos)
              ENNReal.ofReal_ne_top]
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi)]
  calc
    _ = ENNReal.ofReal (Real.pi * T / (Real.Gamma a * Real.Gamma b)) := hquot
    _ = ENNReal.ofReal (Real.pi *
          (Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
            (Real.Gamma (1 - a) * Real.Gamma (1 - b) /
              (Real.Gamma a * Real.Gamma b * Real.Gamma (2 - a - b))))) := by
          congr 1
          rw [hformula]
          ring

/-- The positive planar Riesz kernel is integrable exactly in the range needed below. -/
theorem positive_riesz_convolution_integrable (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    Integrable (fun u : ℂ => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) volume := by
  rw [integrableOn_two_point_rpow_iff (-β) (k - 2) z hz]
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Positive Riesz convolution on the plane, evaluated by Laplace, Gaussian, and beta integrals.
The variables are the source exponents: `|u|^(-β) |u-z|^(k-2)`. -/
theorem positive_riesz_convolution_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) =
      Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β) := by
  have hInt := positive_riesz_convolution_integrable k β hk hβ hβ₂ z hz
  have hnonneg : 0 ≤ᵐ[volume]
      (fun u : ℂ => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) := by
    filter_upwards [] with u
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg u) _)
      (Real.rpow_nonneg (norm_nonneg (u - z)) _)
  have ha : 0 < β / 2 := by linarith
  have ha' : β / 2 < 1 := by linarith
  have hb : 0 < 1 - k / 2 := by linarith
  have hb' : 1 - k / 2 < 1 := by linarith
  have hab : 1 < β / 2 + (1 - k / 2) := by linarith
  have hlin := positive_riesz_lintegral_formula (β / 2) (1 - k / 2) z
    ha ha' hb hb' hab hz
  have hformula :
      Real.pi * (Real.Gamma (β / 2 + (1 - k / 2) - 1) *
        ‖z‖ ^ (-2 * (β / 2 + (1 - k / 2) - 1)) *
          (Real.Gamma (1 - β / 2) * Real.Gamma (1 - (1 - k / 2)) /
            (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
              Real.Gamma (2 - β / 2 - (1 - k / 2))))) =
      Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β) := by
    rw [show -2 * (β / 2 + (1 - k / 2) - 1) = k - β by ring,
      show β / 2 + (1 - k / 2) - 1 = (β - k) / 2 by ring,
      show 1 - (1 - k / 2) = k / 2 by ring,
      show 2 - β / 2 - (1 - k / 2) = 1 + (k - β) / 2 by ring]
    field_simp [
      ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < β / 2)),
      ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - k / 2)),
      ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + (k - β) / 2))]
  have hlin' :
      (∫⁻ u : ℂ, ENNReal.ofReal (‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2))) =
        ENNReal.ofReal (Real.pi *
          (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
            Real.Gamma ((β - k) / 2) /
              (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
                Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β)) := by
    calc
      _ = ∫⁻ u : ℂ, ENNReal.ofReal
          (‖u‖ ^ (-2 * (β / 2)) * ‖u - z‖ ^ (-2 * (1 - k / 2))) := by
            apply lintegral_congr_ae
            filter_upwards [] with u
            apply congrArg ENNReal.ofReal
            rw [show -2 * (β / 2) = -β by ring,
              show -2 * (1 - k / 2) = k - 2 by ring]
      _ = ENNReal.ofReal
          (Real.pi * (Real.Gamma (β / 2 + (1 - k / 2) - 1) *
            ‖z‖ ^ (-2 * (β / 2 + (1 - k / 2) - 1)) *
              (Real.Gamma (1 - β / 2) * Real.Gamma (1 - (1 - k / 2)) /
                (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
                  Real.Gamma (2 - β / 2 - (1 - k / 2)))))) := hlin
      _ = _ := by rw [hformula]
  have hreal : ENNReal.ofReal (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) =
      ENNReal.ofReal (Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
    exact hlin'
  have h1 : 0 < 1 - β / 2 := by linarith
  have h2 : 0 < k / 2 := by linarith
  have h3 : 0 < (β - k) / 2 := by linarith
  have h4 : 0 < β / 2 := by linarith
  have h5 : 0 < 1 - k / 2 := by linarith
  have h6 : 0 < 1 + (k - β) / 2 := by linarith
  have hnum : 0 < Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
      Real.Gamma ((β - k) / 2) := by
    exact mul_pos (mul_pos (Real.Gamma_pos_of_pos h1) (Real.Gamma_pos_of_pos h2))
      (Real.Gamma_pos_of_pos h3)
  have hden : 0 < Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
      Real.Gamma (1 + (k - β) / 2) := by
    exact mul_pos (mul_pos (Real.Gamma_pos_of_pos h4) (Real.Gamma_pos_of_pos h5))
      (Real.Gamma_pos_of_pos h6)
  have hrhs : 0 ≤ Real.pi *
      (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β) := by
    exact le_of_lt (mul_pos (mul_pos Real.pi_pos (div_pos hnum hden))
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _))
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnonneg) hrhs).mp hreal
end DOZZ.Proofs
