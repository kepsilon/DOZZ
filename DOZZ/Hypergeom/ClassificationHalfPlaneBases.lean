/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationCutCrossingBranch
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.Complex.Convex

/-! Analytic Gauss bases on the two half-planes containing the branch cuts. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

private theorem gaussNegativeCrossingPhase_star (c : ℝ) :
    star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) =
      Complex.exp (-((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) := by
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_sub, map_one]
  ring_nf

/-- The negative-cut monodromy phase is unitary for real Gauss parameters. -/
theorem gaussNegativeCrossingPhase_star_mul_self (c : ℝ) :
    star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) = 1 := by
  rw [gaussNegativeCrossingPhase_star]
  rw [← Complex.exp_add]
  rw [show -((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) +
      (2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)) = 0 by ring,
    Complex.exp_zero]

theorem gaussNegativeCrossingPhase_normSq_eq_one (c : ℝ) :
    Complex.normSq (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  change star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) *
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) = (1 : ℂ)
  exact gaussNegativeCrossingPhase_star_mul_self c

/-- The open region to the left of the negative real branch cut. -/
def gaussNegativeHalfPlane : Set ℂ := {z | z.re < 0}

private theorem gaussNegativeHalfPlane_isOpen : IsOpen gaussNegativeHalfPlane := by
  exact isOpen_Iio.preimage Complex.continuous_re

private theorem gaussNegativeHalfPlane_subset_slitPlane :
    ∀ z ∈ gaussNegativeHalfPlane, -z ∈ Complex.slitPlane := by
  intro z hz
  change z.re < 0 at hz
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.neg_re]
  linarith

private theorem gaussNegativeHalfPlane_subset_gaussSlitPlane :
    gaussNegativeHalfPlane ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ z.re < 1
  change z.re < 0 at hz
  exact Or.inr (lt_trans hz (by norm_num))

private theorem gaussSlitPlane_isOpen_for_halfPlane : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_ne.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

/-- The branch-crossing second zero-basis solution is analytic throughout the left half-plane. -/
theorem gaussNegativeCrossingSecond_analyticOnNhd_left
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (gaussNegativeCrossingSecond H a b c) gaussNegativeHalfPlane := by
  have hcNat : ∀ n : ℕ, c ≠ -(n : ℂ) := by
    intro n heq
    apply hc (-(n : ℤ))
    exact heq.trans (by simp)
  have hCNat : ∀ n : ℕ, (2 - c) ≠ -(n : ℂ) := two_sub_parameter_ne_nat_neg hc
  have hchar := hH (a - c + 1) (b - c + 1) (2 - c) hCNat
  have hqSlit : AnalyticOnNhd ℂ
      (H (a - c + 1) (b - c + 1) (2 - c)) gaussSlitPlane :=
    hchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_halfPlane
  have hq : AnalyticOnNhd ℂ
      (H (a - c + 1) (b - c + 1) (2 - c)) gaussNegativeHalfPlane :=
    hqSlit.mono gaussNegativeHalfPlane_subset_gaussSlitPlane
  have hNeg : AnalyticOnNhd ℂ (fun z : ℂ => -z) gaussNegativeHalfPlane := by
    fun_prop
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => Complex.log (-z)) gaussNegativeHalfPlane :=
    hNeg.clog gaussNegativeHalfPlane_subset_slitPlane
  have hexponent : AnalyticOnNhd ℂ
      (fun z => Complex.log (-z) * (1 - c)) gaussNegativeHalfPlane :=
    hlog.mul analyticOnNhd_const
  have hexp : AnalyticOnNhd ℂ
      (fun z => Complex.exp (Complex.log (-z) * (1 - c))) gaussNegativeHalfPlane :=
    hexponent.cexp
  have hphase : AnalyticOnNhd ℂ
      (fun _ : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)))
      gaussNegativeHalfPlane := analyticOnNhd_const
  change AnalyticOnNhd ℂ
    (fun z => Complex.exp (Complex.log (-z) * (1 - c)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)) *
        H (a - c + 1) (b - c + 1) (2 - c) z) gaussNegativeHalfPlane
  exact (hexp.mul hphase).mul hq

private def gaussNegativeHalfPlaneUpper : Set ℂ :=
  gaussNegativeHalfPlane ∩ {z | 0 < z.im}

private theorem gaussNegativeHalfPlaneUpper_isOpen : IsOpen gaussNegativeHalfPlaneUpper :=
  gaussNegativeHalfPlane_isOpen.inter (isOpen_Ioi.preimage Complex.continuous_im)

/-- The branch-crossing second solution solves the original Gauss equation on the full left
half-plane, including the negative real axis. -/
theorem gaussNegativeCrossingSecond_holomorphicOperator_eq_zero_left
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussNegativeHalfPlane,
      gaussHolomorphicOperator a b c (gaussNegativeCrossingSecond H a b c) z = 0 := by
  let f : ℂ → ℂ := gaussNegativeCrossingSecond H a b c
  have hf : AnalyticOnNhd ℂ f gaussNegativeHalfPlane := by
    simpa [f] using gaussNegativeCrossingSecond_analyticOnNhd_left hH a b c hc
  have hf₁ := hf.deriv
  have hf₂ := hf₁.deriv
  have hres : AnalyticOnNhd ℂ (fun z => gaussHolomorphicOperator a b c f z)
      gaussNegativeHalfPlane := by
    intro z hz
    have hfz := hf z hz
    have hf₁z := hf₁ z hz
    have hf₂z := hf₂ z hz
    dsimp [gaussHolomorphicOperator]
    fun_prop
  have hcC : ∀ n : ℤ, c ≠ (n : ℂ) := hc
  have hzero := gauss_local_basis_zero hH a b c hcC
  have hFplusODE : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 := by
    intro z hz
    exact (hzero.2.2.1 z hz).2.1
  have hresUpper : ∀ z ∈ gaussNegativeHalfPlaneUpper,
      gaussHolomorphicOperator a b c f z = 0 := by
    intro z hz
    have hEqOn : Set.EqOn f (gaussFPlus H a b c) gaussNegativeHalfPlaneUpper := by
      intro w hw
      dsimp [f]
      exact gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos a b c w hw.2
    have hEq₀ := hEqOn hz
    have hEq₁ := hEqOn.deriv gaussNegativeHalfPlaneUpper_isOpen hz
    have hEq₂ := (hEqOn.deriv gaussNegativeHalfPlaneUpper_isOpen).deriv
      gaussNegativeHalfPlaneUpper_isOpen hz
    have hODE := hFplusODE z (Or.inl (ne_of_gt hz.2))
    change z * (1 - z) * deriv (deriv (gaussFPlus H a b c)) z +
      (c - (a + b + 1) * z) * deriv (gaussFPlus H a b c) z -
        a * b * gaussFPlus H a b c z = 0 at hODE
    change z * (1 - z) * deriv (deriv f) z +
      (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0
    rw [hEq₀, hEq₁, hEq₂]
    exact hODE
  have hbase : ((-1 : ℂ) + Complex.I) ∈ gaussNegativeHalfPlaneUpper := by
    norm_num [gaussNegativeHalfPlaneUpper, gaussNegativeHalfPlane]
  have hzeroNear :
      (fun z => gaussHolomorphicOperator a b c f z) =ᶠ[𝓝 ((-1 : ℂ) + Complex.I)]
        (fun _ => 0) := by
    filter_upwards [gaussNegativeHalfPlaneUpper_isOpen.mem_nhds hbase] with z hz
    exact hresUpper z hz
  have hpre : IsPreconnected gaussNegativeHalfPlane :=
    (convex_halfSpace_re_lt 0).isPreconnected
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hres
    (by fun_prop) hpre hbase.1 hzeroNear
  intro z hz
  exact hEq hz

end DOZZ.Proofs
