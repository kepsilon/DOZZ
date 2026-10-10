/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHalfPlaneBases
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ODE.FamilySystem

/-! Analytic Gauss bases on the half-plane containing the positive branch cut. -/

@[expose] public section

namespace DOZZ.Proofs

open scoped Topology

/-- The open region to the right of the positive real branch cut. -/
def gaussPositiveHalfPlane : Set ℂ := {z | 1 < z.re}

private theorem gaussPositiveHalfPlane_isOpen : IsOpen gaussPositiveHalfPlane := by
  exact isOpen_Ioi.preimage Complex.continuous_re

private theorem gaussPositiveHalfPlane_map_one_sub_left (z : ℂ)
    (hz : z ∈ gaussPositiveHalfPlane) : 1 - z ∈ gaussNegativeHalfPlane := by
  change 1 < z.re at hz
  change (1 - z).re < 0
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private theorem gaussSlitPlane_isOpen_for_positive : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_ne.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private theorem gaussPositiveHalfPlane_one_sub_mem_gaussSlitPlane (z : ℂ)
    (hz : z ∈ gaussPositiveHalfPlane) : 1 - z ∈ gaussSlitPlane := by
  change 1 < z.re at hz
  change (1 - z).im ≠ 0 ∨ (1 - z).re < 1
  right
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The alternate second solution at one, defined across the full positive-cut half-plane. -/
noncomputable def gaussPositiveCrossingSecond (H : ℂ → ℂ → ℂ → ℂ → ℂ)
    (a b c z : ℂ) : ℂ :=
  gaussNegativeCrossingSecond H a b (1 + a + b - c) (1 - z)

/-- The first solution at one is analytic throughout the positive-cut half-plane. -/
theorem gaussGMinus_analyticOnNhd_right
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (gaussGMinus H a b c) gaussPositiveHalfPlane := by
  let c' : ℂ := 1 + a + b - c
  have hc' : ∀ n : ℕ, c' ≠ -(n : ℂ) := by
    simpa [c'] using one_add_a_add_b_sub_c_ne_nat_neg hδ
  have hchar := hH a b c' hc'
  have hsource : AnalyticOnNhd ℂ (H a b c') gaussSlitPlane := by
    simpa [c'] using hchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_positive
  have harg : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z) gaussPositiveHalfPlane := by
    fun_prop
  have hcomp : AnalyticOnNhd ℂ
      (H a b c' ∘ fun z : ℂ => 1 - z) gaussPositiveHalfPlane :=
    hsource.comp harg (fun z hz =>
      gaussPositiveHalfPlane_one_sub_mem_gaussSlitPlane z hz)
  change AnalyticOnNhd ℂ (fun z => H a b c' (1 - z)) gaussPositiveHalfPlane
  simpa only [Function.comp_def, c'] using hcomp

/-- The alternate second solution at one is analytic across the whole positive real cut. -/
theorem gaussPositiveCrossingSecond_analyticOnNhd_right
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (gaussPositiveCrossingSecond H a b c) gaussPositiveHalfPlane := by
  let c' : ℂ := 1 + a + b - c
  have hc' : ∀ n : ℤ, c' ≠ (n : ℂ) := by
    intro n hn
    apply hδ (1 - n)
    dsimp [c'] at hn
    calc
      c - a - b = 1 - (1 + a + b - c) := by ring
      _ = 1 - (n : ℂ) := by rw [hn]
      _ = ((1 - n : ℤ) : ℂ) := by push_cast; ring
  have hsource : AnalyticOnNhd ℂ
      (gaussNegativeCrossingSecond H a b c') gaussNegativeHalfPlane :=
    gaussNegativeCrossingSecond_analyticOnNhd_left hH a b c' hc'
  have harg : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z) gaussPositiveHalfPlane := by
    fun_prop
  have hcomp : AnalyticOnNhd ℂ
      (gaussNegativeCrossingSecond H a b c' ∘ fun z : ℂ => 1 - z)
      gaussPositiveHalfPlane :=
    hsource.comp harg (fun z hz => gaussPositiveHalfPlane_map_one_sub_left z hz)
  change AnalyticOnNhd ℂ
    (fun z => gaussNegativeCrossingSecond H a b (1 + a + b - c) (1 - z))
    gaussPositiveHalfPlane
  simpa only [Function.comp_def, c'] using hcomp

private theorem gaussFPlus_reflection_eq_gaussGPlus
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) :
    gaussFPlus H a b (1 + a + b - c) (1 - z) = gaussGPlus H a b c z := by
  have he : 1 - (1 + a + b - c) = c - a - b := by ring
  have hA : a - (1 + a + b - c) + 1 = c - b := by ring
  have hB : b - (1 + a + b - c) + 1 = c - a := by ring
  have hC : 2 - (1 + a + b - c) = 1 + c - a - b := by ring
  simp only [gaussFPlus, gaussGPlus, he, hA, hB, hC]

/-- Below the positive cut, the alternate second solution agrees with the principal one-basis
second solution. -/
theorem gaussPositiveCrossingSecond_eq_gaussGPlus_of_im_neg
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (a b c z : ℂ) (hz : z.im < 0) :
    gaussPositiveCrossingSecond H a b c z = gaussGPlus H a b c z := by
  have hw : 0 < (1 - z).im := by
    simpa using neg_pos.mpr hz
  calc
    gaussPositiveCrossingSecond H a b c z =
        gaussNegativeCrossingSecond H a b (1 + a + b - c) (1 - z) := rfl
    _ = gaussFPlus H a b (1 + a + b - c) (1 - z) :=
      gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos a b
        (1 + a + b - c) (1 - z) hw
    _ = gaussGPlus H a b c z := gaussFPlus_reflection_eq_gaussGPlus H a b c z

/-- Above the positive cut, the alternate second solution differs from the principal one-basis
second solution by the reflected local monodromy phase. -/
theorem gaussPositiveCrossingSecond_eq_phase_mul_gaussGPlus_of_im_pos
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (a b c z : ℂ) (hz : 0 < z.im) :
    gaussPositiveCrossingSecond H a b c z =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        (1 - (1 + a + b - c))) * gaussGPlus H a b c z := by
  have hw : (1 - z).im < 0 := by
    simpa using neg_neg_of_pos hz
  calc
    gaussPositiveCrossingSecond H a b c z =
        gaussNegativeCrossingSecond H a b (1 + a + b - c) (1 - z) := rfl
    _ = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          (1 - (1 + a + b - c))) * gaussFPlus H a b (1 + a + b - c) (1 - z) :=
      gaussNegativeCrossingSecond_eq_phase_mul_gaussFPlus_of_im_neg a b
        (1 + a + b - c) (1 - z) hw
    _ = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          (1 - (1 + a + b - c))) * gaussGPlus H a b c z := by
      rw [gaussFPlus_reflection_eq_gaussGPlus]

/-- The unpowered one-basis solution solves the Gauss equation on the full right half-plane. -/
theorem gaussGMinus_holomorphicOperator_eq_zero_right
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussPositiveHalfPlane,
      gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 := by
  let c' : ℂ := 1 + a + b - c
  let g : ℂ → ℂ := H a b c'
  let f : ℂ → ℂ := gaussGMinus H a b c
  have hc' : ∀ n : ℕ, c' ≠ -(n : ℂ) := by
    simpa [c'] using one_add_a_add_b_sub_c_ne_nat_neg hδ
  have hsourceODE := gauss_family_holomorphicOperator_eq_zero_on_slit hH a b c' hc'
  have hAnal : AnalyticOnNhd ℂ g gaussSlitPlane := by
    have hchar := hH a b c' hc'
    simpa [g, c'] using hchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_positive
  have hAnal₁ := hAnal.deriv
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hderivEq : gaussPositiveHalfPlane.EqOn (deriv f)
      (fun z => -deriv g (1 - z)) := by
    intro z hz
    have hw := gaussPositiveHalfPlane_map_one_sub_left z hz
    have hcomp := (((hAnal (1 - z)
      (gaussPositiveHalfPlane_one_sub_mem_gaussSlitPlane z hz)).differentiableAt).hasDerivAt).comp
        z (hmap z)
    change deriv (fun w => g (1 - w)) z = -deriv g (1 - z)
    simpa [f, g, gaussGMinus, c', Function.comp_def, mul_comm] using hcomp.deriv
  have hderiv2Eq : gaussPositiveHalfPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    have hfirst := hderivEq.deriv gaussPositiveHalfPlane_isOpen hz
    have hw := gaussPositiveHalfPlane_map_one_sub_left z hz
    have hcomp := (((hAnal₁ (1 - z)
      (gaussPositiveHalfPlane_one_sub_mem_gaussSlitPlane z hz)).differentiableAt).hasDerivAt).comp
        z (hmap z)
    have hneg := hcomp.neg
    calc
      deriv (deriv f) z = deriv (fun w => -deriv g (1 - w)) z := hfirst
      _ = deriv (deriv g) (1 - z) := by
        simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hneg.deriv
  intro z hz
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c' g (1 - z) := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv2Eq hz, hderivEq hz]
    dsimp [f, g, c', gaussGMinus]
    ring
  rw [hEqOp]
  have hwSlit := gaussPositiveHalfPlane_one_sub_mem_gaussSlitPlane z hz
  have hODE := hsourceODE (1 - z) hwSlit
  simpa [g, c'] using hODE

/-- The alternate second solution at one solves the original Gauss equation on the full
positive-cut half-plane, including the positive real axis beyond one. -/
theorem gaussPositiveCrossingSecond_holomorphicOperator_eq_zero_right
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussPositiveHalfPlane,
      gaussHolomorphicOperator a b c (gaussPositiveCrossingSecond H a b c) z = 0 := by
  let c' : ℂ := 1 + a + b - c
  let g : ℂ → ℂ := gaussNegativeCrossingSecond H a b c'
  let f : ℂ → ℂ := gaussPositiveCrossingSecond H a b c
  have hc' : ∀ n : ℤ, c' ≠ (n : ℂ) := by
    intro n hn
    apply hδ (1 - n)
    dsimp [c'] at hn
    calc
      c - a - b = 1 - (1 + a + b - c) := by ring
      _ = 1 - (n : ℂ) := by rw [hn]
      _ = ((1 - n : ℤ) : ℂ) := by push_cast; ring
  have hAnal : AnalyticOnNhd ℂ g gaussNegativeHalfPlane := by
    simpa [g, c'] using gaussNegativeCrossingSecond_analyticOnNhd_left hH a b c' hc'
  have hAnal₁ := hAnal.deriv
  have hAnal₂ := hAnal₁.deriv
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hderivEq : gaussPositiveHalfPlane.EqOn (deriv f)
      (fun z => -deriv g (1 - z)) := by
    intro z hz
    have hw := gaussPositiveHalfPlane_map_one_sub_left z hz
    have hcomp := (hAnal (1 - z) hw).differentiableAt.hasDerivAt.comp z (hmap z)
    change deriv (fun w => g (1 - w)) z = -deriv g (1 - z)
    simpa [Function.comp_def, mul_comm] using hcomp.deriv
  have hderiv2Eq : gaussPositiveHalfPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    have hfirst := hderivEq.deriv gaussPositiveHalfPlane_isOpen hz
    have hw := gaussPositiveHalfPlane_map_one_sub_left z hz
    have hcomp := (hAnal₁ (1 - z) hw).differentiableAt.hasDerivAt.comp z (hmap z)
    have hneg := hcomp.neg
    calc
      deriv (deriv f) z = deriv (fun w => -deriv g (1 - w)) z := hfirst
      _ = deriv (deriv g) (1 - z) := by
        simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hneg.deriv
  intro z hz
  let w : ℂ := 1 - z
  have hw : w ∈ gaussNegativeHalfPlane := by
    simpa [w] using gaussPositiveHalfPlane_map_one_sub_left z hz
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c' g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv2Eq hz, hderivEq hz]
    dsimp [f, g, w, c', gaussPositiveCrossingSecond]
    ring
  rw [hEqOp]
  have hODE := gaussNegativeCrossingSecond_holomorphicOperator_eq_zero_left
    hH a b c' hc' w hw
  simpa [g, c'] using hODE

end DOZZ.Proofs
