/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PinEnvelopeMoment

/-! Uniform Gaussian correction moments over the compact insertion-center geometry. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Compact exterior centers give uniform pin variance and inverse-variance bounds. -/
theorem compact_pin_parameters (K : Set ℂ) (hK : IsCompact K)
    (hz : ∀ z ∈ K, 2 ≤ ‖z‖) (γ : ℝ) :
    ∃ v a : ℝ, 0 ≤ v ∧ 0 ≤ a ∧ ∀ z ∈ K,
      2 * Real.log ‖z‖ ≤ v ∧ |γ| / (2 * Real.log ‖z‖) ≤ a := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨0, 0, le_rfl, le_rfl, by simp [he]⟩
  obtain ⟨zmax, hzmax, hmax⟩ := hK.exists_isMaxOn hn continuous_norm.continuousOn
  refine ⟨2 * Real.log ‖zmax‖, |γ| / (2 * Real.log 2),
    (offCenter_pin_variance_pos zmax (hz zmax hzmax)).le,
    div_nonneg (abs_nonneg γ) (by positivity), ?_⟩
  intro z hzk
  have hlog2 : Real.log 2 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) (hz z hzk)
  have hlogmax : Real.log ‖z‖ ≤ Real.log ‖zmax‖ :=
    Real.log_le_log (by linarith [hz z hzk]) (hmax hzk)
  exact ⟨by linarith, div_le_div_of_nonneg_left (abs_nonneg γ)
    (by positivity) (by linarith)⟩

/-- The correction envelope has every nonnegative moment uniformly over compact centers,
even for correlated Gaussian pins with the prescribed variance. -/
theorem compact_pin_envelope_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Set ℂ) (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    (γ r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ N Nbar : Ω → ℝ,
      HasGaussianLaw N P → HasGaussianLaw Nbar P →
      (∫ ω, N ω ∂P) = 0 → (∫ ω, Nbar ω ∂P) = 0 →
      variance N P = 2 * Real.log ‖z‖ → variance Nbar P = 2 * Real.log ‖z‖ →
      (∫⁻ ω, ENNReal.ofReal (pinCorrectionEnvelope z γ (N ω) (Nbar ω) *
        Real.exp (pinCorrectionEnvelope z γ (N ω) (Nbar ω))) ^ r ∂P) ≤
        ENNReal.ofReal C := by
  obtain ⟨v, a, _, _, hb⟩ := compact_pin_parameters K hK hz γ
  let C := Real.exp ((2*r) * γ ^ 2) *
    (2 * (Real.exp (v * (2 * ((2*r) * a)) ^ 2 / 2) +
      Real.exp (v * (2 * ((2*r) * a)) ^ 2 / 2)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z hzk N Nbar hN hNb hmN hmNb hvN hvNb
  have h := pin_envelope_power_moment P N Nbar hN hNb hmN hmNb v
    (by rw [hvN]; exact (hb z hzk).1) (by rw [hvNb]; exact (hb z hzk).1)
    z γ a r (hz z hzk) (hb z hzk).2 hr
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
  exact h



end DOZZ.Proofs
