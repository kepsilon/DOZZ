/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.RootedAnnulus
public import DOZZ.GMC.SharpMoments.LocationTransfer
import Mathlib.Tactic

/-! # Uniform rooted inverse moments at the freezing rate -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Uniformly for roots inside the deleted disk, the inverse moment of the actual retained
zero mass has the local freezing power. No restriction on `ξ` enters this estimate. -/
theorem reflected_retainedZero_rooted_inverse_freezing
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ)
    (hreflect : Q γ - α₁ < γ / 2) (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r : ℝ, 0 < r → r < ε₀ →
      ∀ u : ℂ, ‖u‖ ≤ r →
        (∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ r
          (gmcRootedMeasure γ u (M ω))) ^
            (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P) ≤
          ENNReal.ofReal (C * r ^ ((α₁ + γ / 2 - Q γ) ^ 2 / 2)) := by
  let q : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1
  let δ : ℝ := (α₁ + γ / 2 - Q γ) ^ 2 / 2
  let c : ℝ := Real.exp (-γ ^ 2 * Real.log 2) *
    ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hq : 0 < q := (reflected_freezing_margins γ α₁ α₂ α₃ hγ hα₁ hreflect hs).2.1
  obtain ⟨C, ε₀, hC, hε₀, hb⟩ := reflected_freezing_local_input
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hreflect hs hX hM
  refine ⟨c ^ (-q) * C, ε₀, mul_pos (Real.rpow_pos_of_pos hc _) hC, hε₀, ?_⟩
  intro r hr hr₀ u hu
  have hlow (ω : Ω) := reflected_retainedZero_rooted_freezing_lower γ α₁ α₂ α₃ r (M ω) u hr hu
  have hpoint (ω : Ω) :
      (reflectedRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω))) ^ (-q) ≤
        ENNReal.ofReal (c ^ (-q)) * (freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 r (1 / 2)) ^ (-q) := by
    have h := ennreal_rpow_antitone_of_nonpos (hlow ω) (neg_nonpos.mpr hq.le)
    rw [ennreal_mul_rpow_of_ne_zero_ne_top _ _ (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, ENNReal.ofReal_rpow_of_pos hc] at h
    exact h
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (c ^ (-q)) *
        (freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 r (1 / 2)) ^ (-q) ∂P :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (c ^ (-q)) *
        (∫⁻ ω, (freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 r (1 / 2)) ^ (-q) ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c ^ (-q)) * ENNReal.ofReal (C * r ^ δ) :=
      mul_le_mul' le_rfl (hb r hr hr₀)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hc _).le]
      congr 1
      ring

end DOZZ.Proofs
