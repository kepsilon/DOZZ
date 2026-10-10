/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedCutoffVolumeLaw
public import DOZZ.Correlations.Tails.ExponentialParameterTest
public import DOZZ.Correlations.Tails.BoundedPinCoefficient
public import DOZZ.Correlations.Tails.TranslatedField

/-! Equality in law of actual cutoff GMC tests after the pin copy. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The deterministic test correction cancels the pin-dependent Wick correction. -/
theorem copied_wick_weight_factor
    (g γ v L r N Nbar U c : ℝ) :
    (g * Real.exp (γ^2 * (L-v))) * Real.exp
      (γ*(Nbar+U+c*(Nbar-N))-γ^2/2*(r+2*L)) =
      Real.exp (γ*Nbar-γ^2*v) * (g * Real.exp (γ*c*(Nbar-N))) *
        Real.exp (γ*U-γ^2/2*r) := by
  rw [mul_assoc, ← Real.exp_add]
  rw [mul_comm (Real.exp (γ*Nbar-γ^2*v)), mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring_nf

/-- For every nonnegative compact test in the strict local chart, actual source cutoff
GMC tests have the copied scalar-times-random-weight cutoff law. -/
theorem copied_test_cutoff_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ r ρ : ℝ) (hρ : 0 ≤ ρ)
    (hr : ρ + Real.exp (-r) ≤ 1)
    (g G : BoundedContinuousFunction ℂ ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hgs : ∀ x, g x ≠ 0 → ‖x‖ ≤ ρ)
    (hG : ∀ y, G y = g (y-z) * Real.exp ((γ^2+4)*Real.log (normPlus y))) :
    P.map (fun ω => Real.exp (-γ^2*Real.log ‖z‖) * ∫ y, G y ∂regularizedGMC P Xc γ r ω) =
      (P.prod P).map (fun q => Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖) *
        ∫ x, g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))
          ∂regularizedGMC P (fun ω x t => Xc ω (z+x) t-Xc ω z 0) γ r q.1) := by
  let w := exponentialParameterTest g (boundedPinCoefficient z)
    (γ^2*(2*Real.log ‖z‖))
  have hw (x : ℂ) : w x = g x * Real.exp (γ^2*(Real.log (normPlus (z+x))-Real.log ‖z‖)) := by
    by_cases hx : g x = 0
    · change g x * Real.exp _ = _
      simp only [hx, zero_mul]
    · have hn : ‖x‖ ≤ 1 := by linarith [hgs x hx, Real.exp_pos (-r)]
      have hh := norm_sub_norm_le z (z+x)
      simp only [sub_add_cancel_left, norm_neg] at hh
      have hnorm : 1 ≤ ‖z+x‖ := by linarith
      change g x * Real.exp (boundedPinCoefficient z x * _) = _
      rw [bounded_pin_coefficient_eq z x hz hn,
        show normPlus (z+x) = ‖z+x‖ by unfold normPlus; exact max_eq_right hnorm]
      congr 2
      unfold localPinCoefficient
      have hl : Real.log ‖z‖ ≠ 0 := ne_of_gt (by
        have hv := offCenter_pin_variance_pos z hz
        linarith)
      field_simp [hl]
  have hw0 (x : ℂ) : 0 ≤ w x := by
    rw [hw]
    exact mul_nonneg (hg0 x) (Real.exp_nonneg _)
  have hws (x : ℂ) (hx : w x ≠ 0) : ‖x‖ ≤ ρ := by
    apply hgs x
    intro hzero
    exact hx (by rw [hw, hzero, zero_mul])
  have hlaw := copied_cutoff_volume_law P X Xc hX hc hm z hz γ r ρ hρ hr w hw0 hws
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hYc := translated_field_circleAverage P X Xc hX hc z
  have hlocal (x : ℂ) (hx : g x ≠ 0) : ‖x‖ + Real.exp (-r) ≤ 1 := by linarith [hgs x hx]
  have hnorm (x : ℂ) (hx : g x ≠ 0) : normPlus (z+x) = ‖z+x‖ := by
    have hn : ‖x‖ ≤ 1 := by linarith [hgs x hx, Real.exp_pos (-r)]
    have hh := norm_sub_norm_le z (z+x)
    simp only [sub_add_cancel_left, norm_neg] at hh
    unfold normPlus
    exact max_eq_right (by linarith : 1 ≤ ‖z+x‖)
  have hsrc (ω : Ω) : Real.exp (-γ^2*Real.log ‖z‖) * ∫ y, G y ∂regularizedGMC P Xc γ r ω =
      ∫ x, w x * Real.exp (γ*Xc ω (z+x) r-γ^2/2*(r+2*Real.log ‖z+x‖)) ∂volume := by
    rw [regularized_integral_volume P X Xc hX hc γ r ω G, ← integral_const_mul]
    rw [← integral_add_left_eq_self (μ := volume) _ z]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [hG (z+x), add_sub_cancel_left, hw]
      by_cases hx : g x = 0
      · simp only [hx, zero_mul, mul_zero]
      · let p : localCircle := ⟨(x,r), hlocal x hx⟩
        obtain ⟨hO, _⟩ := local_circle_second_moments P X Xc hX hc z hz p
        change (∫ ω', Xc ω' (z+x) r ^ 2 ∂P) = r+2*Real.log ‖z+x‖ at hO
        rw [hO, Real.rpow_def_of_pos (by unfold normPlus; positivity), hnorm x hx]
        simp_rw [mul_assoc]
        rw [mul_left_comm (Real.exp (-γ^2*Real.log ‖z‖)) (g x)]
        simp_rw [← Real.exp_add]
        congr 1
        ring_nf
  have htar (q : Ω × Ω) : Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖) *
      (∫ x, g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))
        ∂regularizedGMC P (fun ω x t => Xc ω (z+x) t-Xc ω z 0) γ r q.1) =
      ∫ x, w x * Real.exp
        (γ*(Xc q.2 z 0+(Xc q.1 (z+x) r-Xc q.1 z 0)+
          localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))-γ^2/2*(r+2*Real.log ‖z+x‖))
            ∂volume := by
    rw [regularized_integral_volume P _ _ hY hYc γ r q.1, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [hw]
      by_cases hx : g x = 0
      · simp only [hx, zero_mul, mul_zero]
      · let p : localCircle := ⟨(x,r), hlocal x hx⟩
        obtain ⟨_, hU⟩ := local_circle_second_moments P X Xc hX hc z hz p
        change (∫ ω', (Xc ω' (z+x) r-Xc ω' z 0) ^ 2 ∂P) = r at hU
        rw [hU, hnorm x hx, show normPlus x = 1 by
          unfold normPlus; exact max_eq_left (by linarith [hgs x hx, Real.exp_pos (-r)])]
        simp only [Real.one_rpow, mul_one]
        simpa only [mul_assoc] using (copied_wick_weight_factor (g x) γ (Real.log ‖z‖)
          (Real.log ‖z+x‖) r (Xc q.1 z 0) (Xc q.2 z 0)
            (Xc q.1 (z+x) r-Xc q.1 z 0) (localPinCoefficient z x)).symm
  simpa only [← hsrc, ← htar] using hlaw


end DOZZ.Proofs
