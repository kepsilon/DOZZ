/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootedKernelBound
public import DOZZ.FourPoint.Fusion.LocalMoments
import DOZZ.GMC.SharpMoments.SeibergPieces
import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency
import DOZZ.GMC.SharpMoments.CutoffUIConvergenceAux
import DOZZ.GMC.Construction.RootedMeasureKernel

/-! # Vanishing small-ball errors for the moving rooted mass -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The small-ball error of the moving rooted kernel has a uniformly vanishing positive moment. -/
theorem fusion_rootedKernel_smallBall_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hα : γ / 2 ≤ α₁) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2))))
    (y : ℂ) (hy : y ≠ 0) :
    let ξ := γ * (Q γ - (α₁ + γ / 2)) * p - γ ^ 2 * p ^ 2 / 2
    0 < ξ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 16 →
      ∀ z : ℂ, ‖y * z‖ ≤ δ →
      (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) δ,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x *
          Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂M ω) ^ p ∂P) ≤
        C * ENNReal.ofReal (δ ^ ξ) := by
  obtain ⟨hξ, D, hD, hbound⟩ := fusion_weightedMoment_small_uniform
    P X hX γ hγ hγ2 M hM (α₁ + γ / 2) p hp hpRange
  let ξ := γ * (Q γ - (α₁ + γ / 2)) * p - γ ^ 2 * p ^ 2 / 2
  let A : ℝ≥0∞ := ENNReal.ofReal
    ((2 : ℝ) ^ |γ * α₂| * (1 + 2 / ‖y‖) ^ (γ ^ 2 / 2))
  refine ⟨hξ, A ^ p * (D + D * ENNReal.ofReal ((2 : ℝ) ^ ξ)), ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top).lt_top
      (ENNReal.add_lt_top.mpr ⟨hD, ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top⟩)
  · intro δ hδ hδ16 z hz
    have hw0 := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM (α₁ + γ / 2) 0 δ
    have hwu := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM
      (α₁ + γ / 2) (y * z) (2 * δ)
    have hae : ∀ᵐ ω ∂P, (∫⁻ x in Metric.ball (0 : ℂ) δ,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x *
          Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂M ω) ^ p ≤
        A ^ p * (weightedGmcBallMass γ (M ω) (α₁ + γ / 2) 0 δ ^ p +
          weightedGmcBallMass γ (M ω) (α₁ + γ / 2) (y * z) (2 * δ) ^ p) := by
      filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
        gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (y * z)] with ω h0 hu
      have h := ENNReal.rpow_le_rpow
        (fusion_rootedKernel_smallBall_le γ α₁ α₂ α₃ hγ hα y z hy (M ω) h0 hu δ hδ
          (by linarith) hz) hp.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le] at h
      exact h.trans (mul_le_mul' le_rfl (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1))
    have hb0 := hbound 0 (by simp) δ hδ (by linarith)
    have hbu := hbound (y * z) (by linarith) (2 * δ) (by positivity) (by linarith)
    have hr : ENNReal.ofReal ((2 * δ) ^ ξ) =
        ENNReal.ofReal ((2 : ℝ) ^ ξ) * ENNReal.ofReal (δ ^ ξ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    calc
      _ ≤ ∫⁻ ω, A ^ p * (weightedGmcBallMass γ (M ω) (α₁ + γ / 2) 0 δ ^ p +
          weightedGmcBallMass γ (M ω) (α₁ + γ / 2) (y * z) (2 * δ) ^ p) ∂P := lintegral_mono_ae hae
      _ = A ^ p * (weightedGmcBallMoment P M γ (α₁ + γ / 2) 0 δ p +
          weightedGmcBallMoment P M γ (α₁ + γ / 2) (y * z) (2 * δ) p) := by
        have hm : AEMeasurable (fun ω =>
            weightedGmcBallMass γ (M ω) (α₁ + γ / 2) 0 δ ^ p +
            weightedGmcBallMass γ (M ω) (α₁ + γ / 2) (y * z) (2 * δ) ^ p) P :=
          (hw0.pow_const p).add (hwu.pow_const p)
        rw [lintegral_const_mul'' _ hm,
          lintegral_add_left' (hw0.pow_const p)]
        rfl
      _ ≤ A ^ p * (D * ENNReal.ofReal (δ ^ ξ) + D * ENNReal.ofReal ((2 * δ) ^ ξ)) :=
        mul_le_mul' le_rfl (add_le_add hb0 hbu)
      _ = _ := by rw [hr]; ring


end DOZZ.Proofs
