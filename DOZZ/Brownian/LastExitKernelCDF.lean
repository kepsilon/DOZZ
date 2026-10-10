/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitGaussianTail
public import DOZZ.Brownian.LastExitKernel
public import DOZZ.Brownian.ConditionedKernelNormalization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Gaussian boundary flux in the last-exit distribution

Expanding the killed Gaussian kernel and the avoidance harmonic function gives four heat tails.
Their derivatives cancel in pairs, leaving the boundary density `p(t,x,c) ν / h(c)`.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- The explicit Gaussian primitive of the deterministic-time avoidance kernel. -/
noncomputable def lastExitGaussianKernelCDF (ν c x t : ℝ) : ℝ :=
  (brownianHeatTail t (c-x-ν*t) -
    Real.exp (-2*ν*x) * brownianHeatTail t (c+x-ν*t) -
    Real.exp (2*ν*(c-x)) * brownianHeatTail t (c-x+ν*t) +
    Real.exp (2*ν*c) * brownianHeatTail t (c+x+ν*t)) / conditionedH ν x

private theorem harmonic_pos {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  exact sub_pos.mpr (Real.exp_lt_one_iff.2 (by nlinarith))

/-- The two drift directions differ by the exact Gaussian exponential factor. -/
theorem brownianHeatDensity_opposite_drift (ν z t : ℝ) (ht : 0 < t) :
    Real.exp (2*ν*z) * brownianHeatDensity t (z+ν*t) =
      brownianHeatDensity t (z-ν*t) := by
  have hp := brownianHeatDensity_tilt (t := t) (ν := ν) (z := z) ht
  have hm := brownianHeatDensity_tilt (t := t) (ν := -ν) (z := z) ht
  rw [show z-(-ν)*t = z+ν*t by ring] at hm
  rw [← hm, ← hp, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The avoidance-weighted Doob transition expands into four ordinary Gaussian densities. -/
theorem conditionedTransition_avoidance_gaussian_expansion (ν c x t y : ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hx : 0 < x) (ht : 0 < t) (hy : c < y) :
    conditionedPositiveTransitionDensity ν t x y * lastExitAvoidanceFactor ν c y =
      (brownianHeatDensity t (y-(x+ν*t)) -
        Real.exp (-2*ν*x) * brownianHeatDensity t (y-(-x+ν*t)) -
        Real.exp (2*ν*(c-x)) * brownianHeatDensity t (y-(x-ν*t)) +
        Real.exp (2*ν*c) * brownianHeatDensity t (y-(-x-ν*t))) / conditionedH ν x := by
  have hy0 : 0 < y := hc.trans hy
  have hcancel : conditionedPositiveTransitionDensity ν t x y * lastExitAvoidanceFactor ν c y =
      (Real.exp (ν*(y-x)-ν^2*t/2) *
        (brownianHeatDensity t (y-x)-brownianHeatDensity t (y+x)) *
        (1-Real.exp (-2*ν*(y-c)))) / conditionedH ν x := by
    simp only [conditionedPositiveTransitionDensity, lastExitAvoidanceFactor,
      ite_eq_left (show 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y from ⟨hν.le,ht,hx,hy0⟩),
      ite_eq_left hy]
    rw [show conditionedH ν (y-c) = 1-Real.exp (-2*ν*(y-c)) by
      simp only [conditionedH, ite_eq_right hν.ne']]
    field_simp [(harmonic_pos hν hy0).ne', (harmonic_pos hν hx).ne']
  have htilt1 := brownianHeatDensity_tilt (t := t) (ν := ν) (z := y-x) ht
  have htilt2 : Real.exp (ν*(y-x)-ν^2*t/2) * brownianHeatDensity t (y+x) =
      Real.exp (-2*ν*x) * brownianHeatDensity t (y+x-ν*t) := by
    rw [show ν*(y-x)-ν^2*t/2 = -2*ν*x+(ν*(y+x)-ν^2*t/2) by ring,
      Real.exp_add, mul_assoc, brownianHeatDensity_tilt ht]
  have hcross1 : brownianHeatDensity t (y-x-ν*t) * Real.exp (-2*ν*(y-c)) =
      Real.exp (2*ν*(c-x)) * brownianHeatDensity t (y-x+ν*t) := by
    rw [← brownianHeatDensity_opposite_drift ν (y-x) t ht]
    rw [mul_right_comm, ← Real.exp_add]
    congr 2
    ring
  have hcross2 : Real.exp (-2*ν*x) * brownianHeatDensity t (y+x-ν*t) *
      Real.exp (-2*ν*(y-c)) = Real.exp (2*ν*c) * brownianHeatDensity t (y+x+ν*t) := by
    rw [← brownianHeatDensity_opposite_drift ν (y+x) t ht]
    rw [← mul_assoc, ← Real.exp_add]
    rw [mul_assoc, mul_comm (brownianHeatDensity t (y+x+ν*t)), ← mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  have hk : Real.exp (ν*(y-x)-ν^2*t/2) *
      (brownianHeatDensity t (y-x)-brownianHeatDensity t (y+x)) =
      brownianHeatDensity t (y-x-ν*t)-Real.exp (-2*ν*x)*brownianHeatDensity t (y+x-ν*t) := by
    rw [mul_sub, htilt1, htilt2]
  rw [hcancel, hk]
  rw [show (brownianHeatDensity t (y-x-ν*t)-Real.exp (-2*ν*x)*brownianHeatDensity t (y+x-ν*t)) *
      (1-Real.exp (-2*ν*(y-c))) =
      brownianHeatDensity t (y-x-ν*t)-Real.exp (-2*ν*x)*brownianHeatDensity t (y+x-ν*t)-
      brownianHeatDensity t (y-x-ν*t)*Real.exp (-2*ν*(y-c))+
      Real.exp (-2*ν*x)*brownianHeatDensity t (y+x-ν*t)*Real.exp (-2*ν*(y-c)) by ring,
    hcross1, hcross2]
  simp only [show y-x-ν*t = y-(x+ν*t) by ring,
    show y+x-ν*t = y-(-x+ν*t) by ring,
    show y-x+ν*t = y-(x-ν*t) by ring,
    show y+x+ν*t = y-(-x-ν*t) by ring]

/-- The Gaussian primitive is the actual avoidance-weighted transition integral. -/
theorem integral_conditionedTransition_avoidance_eq_gaussianCDF (ν c x t : ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hx : 0 < x) (ht : 0 < t) :
    (∫ y, conditionedPositiveTransitionDensity ν t x y * lastExitAvoidanceFactor ν c y) =
      lastExitGaussianKernelCDF ν c x t := by
  have h1 := (integrable_brownianHeatDensity_sub_const ht (x+ν*t)).integrableOn (s := Ioi c)
  have h2 := (integrable_brownianHeatDensity_sub_const ht (-x+ν*t)).integrableOn
    (s := Ioi c) |>.const_mul (Real.exp (-2*ν*x))
  have h3 := (integrable_brownianHeatDensity_sub_const ht (x-ν*t)).integrableOn
    (s := Ioi c) |>.const_mul (Real.exp (2*ν*(c-x)))
  have h4 := (integrable_brownianHeatDensity_sub_const ht (-x-ν*t)).integrableOn
    (s := Ioi c) |>.const_mul (Real.exp (2*ν*c))
  have h12 : IntegrableOn (fun y => brownianHeatDensity t (y-(x+ν*t)) -
      Real.exp (-2*ν*x) * brownianHeatDensity t (y-(-x+ν*t))) (Ioi c) := by
    exact (h1.sub h2).congr (ae_of_all _ fun _ => rfl)
  have h123 : IntegrableOn (fun y => brownianHeatDensity t (y-(x+ν*t)) -
      Real.exp (-2*ν*x) * brownianHeatDensity t (y-(-x+ν*t)) -
      Real.exp (2*ν*(c-x)) * brownianHeatDensity t (y-(x-ν*t))) (Ioi c) := by
    exact (h12.sub h3).congr (ae_of_all _ fun _ => rfl)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioi c) (fun y hy => by
      have hy' : ¬ c < y := hy
      simp [lastExitAvoidanceFactor, hy'])]
  have he : (∫ y in Ioi c, conditionedPositiveTransitionDensity ν t x y * lastExitAvoidanceFactor ν c y) =
      ∫ y in Ioi c,
        (brownianHeatDensity t (y-(x+ν*t)) -
          Real.exp (-2*ν*x) * brownianHeatDensity t (y-(-x+ν*t)) -
          Real.exp (2*ν*(c-x)) * brownianHeatDensity t (y-(x-ν*t)) +
          Real.exp (2*ν*c) * brownianHeatDensity t (y-(-x-ν*t))) / conditionedH ν x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact conditionedTransition_avoidance_gaussian_expansion ν c x t y hν hc hx ht hy
  rw [he, integral_div, integral_add h123 h4,
    integral_sub h12 h3, integral_sub h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul]
  simp_rw [integral_brownianHeatDensity_sub_const_Ioi ht]
  unfold lastExitGaussianKernelCDF
  simp only [show c-(x+ν*t) = c-x-ν*t by ring,
    show c-(-x+ν*t) = c+x-ν*t by ring,
    show c-(x-ν*t) = c-x+ν*t by ring,
    show c-(-x-ν*t) = c+x+ν*t by ring]

/-- The explicit primitive has precisely the last-exit boundary derivative. -/
theorem hasDerivAt_lastExitGaussianKernelCDF (ν c x t : ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (lastExitGaussianKernelCDF ν c x)
      (conditionedPositiveTransitionDensity ν t x c * ν / conditionedH ν c) t := by
  have h1 := hasDerivAt_brownianHeatTail_affine (c-x) (-ν) t ht
  have h2 := (hasDerivAt_brownianHeatTail_affine (c+x) (-ν) t ht).const_mul
    (Real.exp (-2*ν*x))
  have h3 := (hasDerivAt_brownianHeatTail_affine (c-x) ν t ht).const_mul
    (Real.exp (2*ν*(c-x)))
  have h4 := (hasDerivAt_brownianHeatTail_affine (c+x) ν t ht).const_mul
    (Real.exp (2*ν*c))
  have hd := ((h1.sub h2).sub h3).add h4 |>.div_const (conditionedH ν x)
  have hcross1 := brownianHeatDensity_opposite_drift ν (c-x) t ht
  have hcross2 : Real.exp (2*ν*c) * brownianHeatDensity t (c+x+ν*t) =
      Real.exp (-2*ν*x) * brownianHeatDensity t (c+x-ν*t) := by
    rw [show 2*ν*c = -2*ν*x+2*ν*(c+x) by ring, Real.exp_add, mul_assoc,
      brownianHeatDensity_opposite_drift ν (c+x) t ht]
  have htilt1 := brownianHeatDensity_tilt (t := t) (ν := ν) (z := c-x) ht
  have htilt2 : Real.exp (ν*(c-x)-ν^2*t/2) * brownianHeatDensity t (c+x) =
      Real.exp (-2*ν*x) * brownianHeatDensity t (c+x-ν*t) := by
    rw [show ν*(c-x)-ν^2*t/2 = -2*ν*x+(ν*(c+x)-ν^2*t/2) by ring,
      Real.exp_add, mul_assoc, brownianHeatDensity_tilt ht]
  convert hd using 1
  · funext u
    simp only [lastExitGaussianKernelCDF, Pi.add_apply, Pi.neg_apply, neg_mul,
      sub_eq_add_neg]
  · simp only [conditionedPositiveTransitionDensity, ite_eq_left
      (show 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < c from ⟨hν.le,ht,hx,hc⟩)]
    rw [mul_sub, htilt1, htilt2]
    have he1 : c-x+-ν*t = c-x-ν*t := by ring
    have he2 : c+x+-ν*t = c+x-ν*t := by ring
    simp only [he1, he2, neg_div, sub_neg_eq_add]
    rw [← mul_assoc (Real.exp (2*ν*(c-x))), hcross1,
      ← mul_assoc (Real.exp (2*ν*c)), hcross2]
    field_simp [(harmonic_pos hν hx).ne', (harmonic_pos hν hc).ne', ht.ne']
    ring


/-- Integrating the boundary density gives the increment of the avoidance kernel CDF on each
compact interval of positive elapsed times. -/
theorem integral_lastExit_boundaryDensity_Ioc (ν c x a b : ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in Ioc a b, conditionedPositiveTransitionDensity ν u x c * ν / conditionedH ν c) =
      lastExitGaussianKernelCDF ν c x b - lastExitGaussianKernelCDF ν c x a := by
  have hcont : ContinuousOn
      (fun u => conditionedPositiveTransitionDensity ν u x c * ν / conditionedH ν c)
      (Icc a b) := by
    intro u hu
    have hu0 : 0 < u := ha.trans_le hu.1
    have he : (fun v => conditionedPositiveTransitionDensity ν v x c * ν / conditionedH ν c) =ᶠ[𝓝 u]
        (fun v => Real.exp (ν*(c-x)-ν^2*v/2) *
          (Real.exp (-(c-x)^2/(2*v))/Real.sqrt (2*Real.pi*v) -
            Real.exp (-(c+x)^2/(2*v))/Real.sqrt (2*Real.pi*v)) *
          conditionedH ν c / conditionedH ν x * ν / conditionedH ν c) := by
      filter_upwards [Ioi_mem_nhds hu0] with v hv
      change 0 < v at hv
      simp only [conditionedPositiveTransitionDensity,
        ite_eq_left (show 0 ≤ ν ∧ 0 < v ∧ 0 < x ∧ 0 < c from ⟨hν.le,hv,hx,hc⟩),
        brownianHeatDensity, ite_eq_left hv]
    have hf : ContinuousAt (fun v => Real.exp (ν*(c-x)-ν^2*v/2) *
          (Real.exp (-(c-x)^2/(2*v))/Real.sqrt (2*Real.pi*v) -
            Real.exp (-(c+x)^2/(2*v))/Real.sqrt (2*Real.pi*v)) *
          conditionedH ν c / conditionedH ν x * ν / conditionedH ν c) u := by
      fun_prop (disch := positivity)
    exact (hf.congr_of_eventuallyEq he).continuousWithinAt
  have hi : IntervalIntegrable
      (fun u => conditionedPositiveTransitionDensity ν u x c * ν / conditionedH ν c)
      volume a b := hcont.intervalIntegrable_of_Icc hab
  have hd : ∀ u ∈ uIcc a b, HasDerivAt (lastExitGaussianKernelCDF ν c x)
      (conditionedPositiveTransitionDensity ν u x c * ν / conditionedH ν c) u := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact hasDerivAt_lastExitGaussianKernelCDF ν c x u hν hc hx (ha.trans_le hu.1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rwa [intervalIntegral.integral_of_le hab] at he

/-- The same boundary-density increment in absolute time coordinates after a fixed past time. -/
theorem integral_lastExit_boundaryDensity_shifted_Ioc (ν c x s a b : ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hx : 0 < x) (ha : s < a) (hab : a ≤ b) :
    (∫ u in Ioc a b, conditionedPositiveTransitionDensity ν (u-s) x c * ν / conditionedH ν c) =
      lastExitGaussianKernelCDF ν c x (b-s) - lastExitGaussianKernelCDF ν c x (a-s) := by
  rw [← intervalIntegral.integral_of_le hab]
  change (∫ u in a..b, (fun v => conditionedPositiveTransitionDensity ν v x c * ν /
    conditionedH ν c) (u-s)) = _
  rw [intervalIntegral.integral_comp_sub_right
      (fun v => conditionedPositiveTransitionDensity ν v x c * ν / conditionedH ν c) s,
    intervalIntegral.integral_of_le (sub_le_sub_right hab s)]
  exact integral_lastExit_boundaryDensity_Ioc ν c x (a-s) (b-s) hν hc hx
    (sub_pos.mpr ha) (sub_le_sub_right hab s)

end DOZZ.Proofs

end
