/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationSource
public import DOZZ.Hypergeom.ODE.SeriesEquation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected

/-! The family characterization `IsGaussHypergeometricFamily` supplies a holomorphic first-order
Gauss-system lift on the entire slit plane, including the negative real axis. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

theorem gaussSlitPlane_isOpen : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private theorem gaussSlitPlane_isPreconnected_for_familySystem :
    IsPreconnected gaussSlitPlane := by
  have hstar : StarConvex ℝ (0 : ℂ) gaussSlitPlane := by
    intro z hz s t hs ht hst
    change z.im ≠ 0 ∨ z.re < 1 at hz
    change (s • (0 : ℂ) + t • z).im ≠ 0 ∨ (s • (0 : ℂ) + t • z).re < 1
    rcases hz with him | hre
    · by_cases ht0 : t = 0
      · right
        rw [ht0]
        simp
      · left
        have htpos : 0 < t := by
          by_contra hnot
          have htneg : t ≤ 0 := le_of_not_gt hnot
          exact ht0 (le_antisymm htneg ht)
        have himag : (s • (0 : ℂ) + t • z).im = t * z.im := by
          rw [smul_zero, zero_add, Complex.smul_im, smul_eq_mul]
        rw [himag]
        exact mul_ne_zero htpos.ne' him
    · right
      rw [smul_zero, zero_add, Complex.smul_re, smul_eq_mul]
      have ht1 : t ≤ 1 := by linarith
      by_cases hzneg : z.re < 0
      · calc
          t * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hzneg.le
          _ < 1 := by norm_num
      · have hzpos : 0 ≤ z.re := le_of_not_gt hzneg
        calc
          t * z.re ≤ 1 * z.re := mul_le_mul_of_nonneg_right ht1 hzpos
          _ = z.re := one_mul _
          _ < 1 := hre
  have hzero : (0 : ℂ) ∈ gaussSlitPlane := by simp [gaussSlitPlane]
  exact hstar.isPathConnected hzero |>.isConnected.isPreconnected

/-- The scalar equation forced by the characterization holds throughout the complete
Gauss slit plane, not only away from its negative-real cut. -/
theorem gauss_family_holomorphicOperator_eq_zero_on_slit
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ z ∈ gaussSlitPlane, gaussHolomorphicOperator a b c (H a b c) z = 0 := by
  let f : ℂ → ℂ := H a b c
  have hchar : IsGaussHypergeometric a b c f := by
    simpa [f] using hH a b c hc
  have hf : AnalyticOnNhd ℂ f gaussSlitPlane :=
    hchar.1.analyticOnNhd gaussSlitPlane_isOpen
  have hf' : AnalyticOnNhd ℂ (deriv f) gaussSlitPlane := hf.deriv
  have hf'' : AnalyticOnNhd ℂ (deriv (deriv f)) gaussSlitPlane := hf'.deriv
  have hres : AnalyticOnNhd ℂ
      (fun z => gaussHolomorphicOperator a b c f z) gaussSlitPlane := by
    intro z hz
    have hfz := hf z hz
    have hf'z := hf' z hz
    have hf''z := hf'' z hz
    dsimp [gaussHolomorphicOperator]
    fun_prop
  have hresZeroDisk : ∀ z : ℂ, ‖z‖ < 1 →
      gaussHolomorphicOperator a b c f z = 0 := by
    intro z hz
    have hseries := ordinaryHypergeometric_gaussEquation_on_unitDisk a b c hc z hz
    have hEq : f z = ordinaryHypergeometric a b c z := hchar.2 z hz
    have hEq' : deriv f z = deriv (ordinaryHypergeometric a b c) z := by
      have hEqOn : Metric.ball (0 : ℂ) 1 |>.EqOn f (ordinaryHypergeometric a b c) := by
        intro w hw
        have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
        exact hchar.2 w hw'
      have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact hEqOn.deriv Metric.isOpen_ball hzball
    have hEq'' : deriv (deriv f) z =
        deriv (deriv (ordinaryHypergeometric a b c)) z := by
      have hEqOn : Metric.ball (0 : ℂ) 1 |>.EqOn f (ordinaryHypergeometric a b c) := by
        intro w hw
        have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
        exact hchar.2 w hw'
      have hEqOn' := hEqOn.deriv Metric.isOpen_ball
      have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact hEqOn'.deriv Metric.isOpen_ball hzball
    unfold gaussHolomorphicOperator
    rw [hEq, hEq', hEq'']
    simpa [gaussHolomorphicOperator] using hseries
  have hnear : (fun z => gaussHolomorphicOperator a b c f z) =ᶠ[𝓝 (0 : ℂ)]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hresZeroDisk z hz'
  have hzero : Set.EqOn (fun z => gaussHolomorphicOperator a b c f z)
      (fun _ => (0 : ℂ)) gaussSlitPlane :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hres (by fun_prop)
      gaussSlitPlane_isPreconnected_for_familySystem (by simp [gaussSlitPlane]) hnear
  intro z hz
  exact hzero hz

/-- Every characterized Gauss family gives a holomorphic state `(H,H')` that solves the
first-order Gauss system at each regular point of the slit plane. -/
theorem IsGaussHypergeometricFamily.state_hasDerivAt_gaussSystem
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : z ∈ gaussSlitPlane) (hzreg : z ∈ gaussRegularPlane) :
    HasDerivAt
      (fun w => (H a b c w, deriv (fun u => H a b c u) w))
      (gaussSystemOperator a b c z
        (H a b c z, deriv (fun u => H a b c u) z)) z := by
  let f : ℂ → ℂ := H a b c
  have hchar : IsGaussHypergeometric a b c f := by
    simpa [f] using hH a b c hc
  have hf : AnalyticOnNhd ℂ f gaussSlitPlane :=
    hchar.1.analyticOnNhd gaussSlitPlane_isOpen
  have hf' : AnalyticOnNhd ℂ (deriv f) gaussSlitPlane := hf.deriv
  have hfirst : HasDerivAt f (deriv f z) z := (hf z hz).differentiableAt.hasDerivAt
  have hsecond : HasDerivAt (deriv f) (deriv (deriv f) z) z :=
    (hf' z hz).differentiableAt.hasDerivAt
  have hpair : HasDerivAt (fun w => (f w, deriv f w))
      (deriv f z, deriv (deriv f) z) z := hfirst.prodMk hsecond
  have hscalar := gauss_family_holomorphicOperator_eq_zero_on_slit
    hH a b c hc z hz
  have hsystem :=
    (gaussHolomorphicOperator_eq_zero_iff_system_residual_eq_zero
      a b c f hzreg.1 hzreg.2).mp hscalar
  have hvec : gaussSystemOperator a b c z (f z, deriv f z) =
      (deriv f z, deriv (deriv f) z) := by
    rw [gaussSystemOperator_apply]
    simp [hsystem]
  apply hpair.congr_deriv hvec.symm

end DOZZ.Proofs
