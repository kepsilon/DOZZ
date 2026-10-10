/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Local value and derivative data of the ordinary hypergeometric series. -/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- The ordinary Gauss series has positive convergence radius whenever its denominator parameter
is not a nonpositive integer. -/
theorem ordinaryHypergeometricSeries_radius_pos (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    0 < (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ n : ℕ, a = -(n : ℂ)
  · obtain ⟨n, hn⟩ := ha
    have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
      rw [hn]
      exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ b c
    rw [htop]
    exact ENNReal.zero_lt_top
  · by_cases hb : ∃ n : ℕ, b = -(n : ℂ)
    · obtain ⟨n, hn⟩ := hb
      have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
        rw [ordinaryHypergeometricSeries_symm, hn]
        exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ a c
      rw [htop]
      exact ENNReal.zero_lt_top
    · have ha' : ∀ n : ℕ, (n : ℂ) ≠ -a := by
        intro n hn
        apply ha
        refine ⟨n, ?_⟩
        calc
          a = -(-a) := by ring
          _ = -(n : ℂ) := by rw [← hn]
      have hb' : ∀ n : ℕ, (n : ℂ) ≠ -b := by
        intro n hn
        apply hb
        refine ⟨n, ?_⟩
        calc
          b = -(-b) := by ring
          _ = -(n : ℂ) := by rw [← hn]
      have hc' : ∀ n : ℕ, (n : ℂ) ≠ -c := by
        intro n hn
        apply hc n
        calc
          c = -(-c) := by ring
          _ = -(n : ℂ) := by rw [← hn]
      rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c (fun n => ⟨ha' n, hb' n, hc' n⟩)]
      norm_num

/-- The ordinary Gauss power series converges throughout the open unit disk whenever its
denominator parameter is not a nonpositive integer. Terminating numerator parameters have
infinite radius; otherwise the radius is exactly one. -/
theorem ordinaryHypergeometricSeries_one_le_radius (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ n : ℕ, a = -(n : ℂ)
  · obtain ⟨n, hn⟩ := ha
    have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
      rw [hn]
      exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ b c
    rw [htop]
    exact le_top
  · by_cases hb : ∃ n : ℕ, b = -(n : ℂ)
    · obtain ⟨n, hn⟩ := hb
      have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
        rw [ordinaryHypergeometricSeries_symm, hn]
        exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ a c
      rw [htop]
      exact le_top
    · have ha' : ∀ n : ℕ, (n : ℂ) ≠ -a := by
        intro n hn
        apply ha
        refine ⟨n, ?_⟩
        calc
          a = -(-a) := by ring
          _ = -(n : ℂ) := by rw [← hn]
      have hb' : ∀ n : ℕ, (n : ℂ) ≠ -b := by
        intro n hn
        apply hb
        refine ⟨n, ?_⟩
        calc
          b = -(-b) := by ring
          _ = -(n : ℂ) := by rw [← hn]
      have hc' : ∀ n : ℕ, (n : ℂ) ≠ -c := by
        intro n hn
        apply hc n
        calc
          c = -(-c) := by ring
          _ = -(n : ℂ) := by rw [← hn]
      rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c
        (fun n => ⟨ha' n, hb' n, hc' n⟩)]

/-- A characterized family has the source series value and derivative at the origin. -/
theorem gauss_family_hasDerivAt_zero {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    HasDerivAt (H a b c) (a * b / c) 0 := by
  have hchar : IsGaussHypergeometric a b c (H a b c) := hH a b c hc
  have hradius := ordinaryHypergeometricSeries_radius_pos a b c hc
  have hsum : ordinaryHypergeometric a b c =
      (ordinaryHypergeometricSeries ℂ a b c).sum := by
    funext z
    rw [ordinaryHypergeometric_eq_tsum]
    exact (ordinaryHypergeometric_sum_eq a b c z).symm
  have hpower : HasFPowerSeriesAt (ordinaryHypergeometric a b c)
      (ordinaryHypergeometricSeries ℂ a b c) 0 := by
    rw [hsum]
    exact (ordinaryHypergeometricSeries ℂ a b c).hasFPowerSeriesOnBall hradius |>.hasFPowerSeriesAt
  have hderiv : HasDerivAt (ordinaryHypergeometric a b c)
      ((ordinaryHypergeometricSeries ℂ a b c) 1 fun _ => (1 : ℂ)) 0 :=
    hpower.hasDerivAt
  have hcoeff : (ordinaryHypergeometricSeries ℂ a b c) 1 (fun _ => (1 : ℂ)) = a * b / c := by
    rw [ordinaryHypergeometricSeries_apply_eq]
    simp
    ring
  rw [hcoeff] at hderiv
  have hnear : H a b c =ᶠ[𝓝 (0 : ℂ)] ordinaryHypergeometric a b c := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hchar.2 z hz'
  exact hderiv.congr_of_eventuallyEq hnear

end DOZZ.Proofs
