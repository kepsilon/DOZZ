/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.MassPerturbation
public import DOZZ.FourPoint.ReflectedOuter.InversePerturbation
public import DOZZ.FourPoint.Reflected.ChargeShift
public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
import Mathlib.Tactic

/-! # The moving inverse-moment error at the relative cutoff scale -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The moving error is bounded by `‖z‖/r` times a uniform inverse moment, at the literal
outer radius `r=‖z‖^(1-ξ)`. The estimate does not impose any upper bound on `ξ`. -/
theorem reflected_outer_moving_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hα₁ : α₁ - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ),
      0 < ‖z‖ ^ (1 - ξ) → ‖z‖ ^ (1 - ξ) ≤ 1 → ‖z‖ ≤ 1 →
      ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 →
      |gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        (∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) (M ω)) ^ (-p) ∂P).toReal| ≤
          C * (‖z‖ / ‖z‖ ^ (1 - ξ)) := by
  obtain ⟨Cs, hCs, hsb⟩ := reflected_retainedZero_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ p hp.le
  obtain ⟨Ct, _, htb⟩ := reflected_outerMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ p hp.le
  let A : ℝ := p * (1 / 4 : ℝ) ^ (-(p + 1))
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A * 4 * Cs, by positivity, ?_⟩
  intro z ξ hr hr₁ hz₁ hz
  let r : ℝ := ‖z‖ ^ (1 - ξ)
  let d : ℝ := 4 * (‖z‖ / r)
  let S : Ω → ℝ≥0∞ := fun ω => reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)
  let T : Ω → ℝ≥0∞ := fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let R : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (A * d) * S ω ^ (-p)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hm := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ₂ M hM
  have hSm : AEMeasurable S P :=
    (reflected_retainedZero_measure_measurable γ α₁ α₂ α₃ r).comp_aemeasurable hm
  have hTm : AEMeasurable T P :=
    (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable hm
  have hSt : (∫⁻ ω, S ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsb r hr₁)
  have hTt : (∫⁻ ω, T ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htb z ξ hz₁ hr₁)
  have hRb : (∫⁻ ω, R ω ∂P) ≤ ENNReal.ofReal ((A * 4 * Cs) * (‖z‖ / r)) := by
    dsimp only [R]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ENNReal.ofReal (A * d) * ENNReal.ofReal Cs := mul_le_mul' le_rfl (hsb r hr₁)
      _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hA.le hd)]; congr 1; dsimp only [d]; ring
  have hRt := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRb
  have hcomp : ∀ᵐ ω ∂P,
      T ω ^ (-p) ≤ S ω ^ (-p) + R ω ∧ S ω ^ (-p) ≤ T ω ^ (-p) + R ω := by
    filter_upwards [reflected_retainedZero_ae_positive_finite P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ r hr₁ hα₁ hα₂ hα₃,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω hpf h0 h1
    have hsfin : S ω ≠ ⊤ := ne_top_of_le_ne_top hpf.2.ne
      (reflected_retainedZero_le_full γ α₁ α₂ α₃ r (M ω))
    obtain ⟨hl, hu, hv⟩ := reflected_outerMass_relative_comparison
      γ α₁ α₂ α₃ ξ hγ hγ₂ z (M ω) hr hz h0 h1
    exact reflected_ennreal_inverse_relative_comparison p d hp hd (S ω) (T ω)
      hpf.1.ne' hsfin hl hu hv
  have hh := reflected_lintegral_toReal_difference_bound P (fun ω => T ω ^ (-p))
    (fun ω => S ω ^ (-p)) R (hTm.pow_const _) (hSm.pow_const _) hTt hSt hRt
    (hcomp.mono fun _ h => h.1) (hcomp.mono fun _ h => h.2)
  calc
    _ ≤ (∫⁻ ω, R ω ∂P).toReal := hh
    _ ≤ (A * 4 * Cs) * (‖z‖ / r) := by
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hRb
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (A * 4 * Cs) * (‖z‖ / r))] using ht

end DOZZ.Proofs
