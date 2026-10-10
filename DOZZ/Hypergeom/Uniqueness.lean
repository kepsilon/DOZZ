/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected

/-! Uniqueness of the principal continuation on its slit carrier. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

private theorem gaussSlitPlane_isPreconnected : IsPreconnected gaussSlitPlane := by
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

/-- Uniqueness on the slit plane `gaussSlitPlane`, without constraining off-slit values. -/
theorem IsGaussHypergeometric.eqOn {a b c : ℂ} {F G : ℂ → ℂ}
    (hF : IsGaussHypergeometric a b c F) (hG : IsGaussHypergeometric a b c G) :
    EqOn F G gaussSlitPlane := by
  have hopen : IsOpen gaussSlitPlane := by
    change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z : ℂ | z.re < 1})
    exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
      (isOpen_Iio.preimage Complex.continuous_re)
  have hFA : AnalyticOnNhd ℂ F gaussSlitPlane := hF.1.analyticOnNhd hopen
  have hGA : AnalyticOnNhd ℂ G gaussSlitPlane := hG.1.analyticOnNhd hopen
  have hnear : F =ᶠ[𝓝 (0 : ℂ)] G := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (hF.2 z hz').trans (hG.2 z hz').symm
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hFA hGA
    gaussSlitPlane_isPreconnected (by simp [gaussSlitPlane]) hnear

end DOZZ.Proofs
