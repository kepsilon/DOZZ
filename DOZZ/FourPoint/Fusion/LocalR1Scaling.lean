/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledLocalRooting
public import DOZZ.FourPoint.Fusion.ScaledTimeConvergence
public import DOZZ.FourPoint.Fusion.Parameters

/-! # Scaling the local pure derivative contribution through the time integral -/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

noncomputable def fusionLocalR1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2 *
    (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) *
      (∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![t * z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
        (∫ x in Metric.ball (0 : ℂ) (1 / 2),
          (gammaHalfKernel γ α₁ α₂ α₃ (t * z) x : ℂ) / (x - t * z) ^ 2 ∂M ω) ∂P))

/-- Time scaling cancels the complex phase and leaves the real weight `t^(κ-2)`. -/
theorem fusion_time_scaling_factor (κ : ℝ) (t : ℝ) (ht : 0 < t) (z : ℂ) (hz : z ≠ 0) :
    z ^ 2 * (‖(t : ℂ) * z‖ ^ κ : ℝ) / ((t : ℂ) * z) ^ 2 =
      (‖z‖ ^ κ : ℝ) * (t ^ (κ - 2) : ℝ) := by
  have hn : ‖(t : ℂ) * z‖ = t * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hp : t ^ κ = t ^ (κ - 2) * t ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hn, Real.mul_rpow ht.le (norm_nonneg _), hp]
  push_cast
  field_simp [hz, Complex.ofReal_ne_zero.mpr ht.ne']

/-- The exact local `r₁` contribution is the uniformly dominated scaled time integral. -/
theorem fusionLocalR1_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hβ : γ ^ 2 / 2 < γ * α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    fusionLocalR1 P M γ α₁ α₂ α₃ p z =
      ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
        (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ) *
        (∫ t in Icc (0 : ℝ) 1, ((1 - t) * t ^ (γ ^ 2 / 2 - γ * α₁) : ℝ) *
          (∫ y : ℂ, planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
            (fusionScaledFactor P M γ α₁ α₂ α₃ (-p - 1) y ((t : ℂ) * z) : ℂ))) := by
  let κ := γ * (Q γ - α₁)
  have hκ := fusion_exponent_eq γ α₁ hγ.ne'
  have hpoint : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1),
      z ^ 2 * ((1 - t : ℝ) *
        (∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![t * z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
          (∫ x in Metric.ball (0 : ℂ) (1 / 2),
            (gammaHalfKernel γ α₁ α₂ α₃ (t * z) x : ℂ) / (x - t * z) ^ 2 ∂M ω) ∂P)) =
      (‖z‖ ^ κ : ℝ) * (((1 - t) * t ^ (γ ^ 2 / 2 - γ * α₁) : ℝ) *
        (∫ y : ℂ, planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
          (fusionScaledFactor P M γ α₁ α₂ α₃ (-p - 1) y ((t : ℂ) * z) : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz
    have htz4 : ‖(t : ℂ) * z‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      calc
        t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ 1 / 4 := by simpa only [one_mul] using hz4
    rw [fusion_localR1_rooting P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃
      (-p - 1) (by linarith) ((t : ℂ) * z) htz htz4,
      fusion_localR1_reference_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) ((t : ℂ) * z) htz,
      ← hκ]
    have hfac := fusion_time_scaling_factor κ t htpos z hz
    have he : κ - 2 = γ ^ 2 / 2 - γ * α₁ := by dsimp only [κ]; linarith only [hκ]
    rw [he] at hfac
    push_cast
    calc
      _ = (z ^ 2 * (‖(t : ℂ) * z‖ ^ κ : ℝ) / ((t : ℂ) * z) ^ 2) *
          ((1 - (t : ℂ)) * (∫ y : ℂ, planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
            (fusionScaledFactor P M γ α₁ α₂ α₃ (-p - 1) y ((t : ℂ) * z) : ℂ))) := by ring
      _ = _ := by rw [hfac]; ring
  unfold fusionLocalR1
  rw [mul_assoc, ← integral_const_mul, integral_congr_ae hpoint, integral_const_mul, ← mul_assoc]

end DOZZ.Proofs
