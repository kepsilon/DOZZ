/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.MovingMassPieces
public import DOZZ.FourPoint.Fusion.RootOnlyPieces
/-! # Finiteness of both rooted interpolation endpoints near the collision -/
@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- Local positive moments and exterior domination make this rooted endpoint finite. -/
theorem fusionMovingMass_finite_near {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2))))
    (y z : ℂ) (hy : y ≠ 0) (hz : ‖z‖ ≤ 1 / 16) (hyz : ‖y * z‖ ≤ 1 / 32) :
    ∀ᵐ ω ∂P, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ≠ ⊤ := by
  obtain ⟨_, C, hC, hb⟩ := fusion_rootedKernel_smallBall_moment P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ p hα hp hp1 hpRange y hy
  have hbad : ∀ᵐ ω ∂P, fusionMovingBadMass γ α₁ α₂ α₃ y z (1 / 16) (M ω) ≠ ⊤ :=
    fusion_mass_finite_of_moment (fusionMovingBadMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z (1 / 16))
      hp (lt_of_le_of_lt (hb (1 / 16) (by norm_num) le_rfl z (by linarith))
        (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top))
  have hgood0 : ∀ᵐ ω ∂P, fusionMovingGoodMass γ α₁ α₂ α₃ y 0 (1 / 16) (M ω) ≠ ⊤ := by
    filter_upwards [fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃] with ω hω
    exact (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (by
      simpa only [fusionMovingKernel, mul_zero] using hω)).ne
  filter_upwards [hbad, hgood0] with ω hωb hωg
  have hg := fusionMovingGoodMass_le γ α₁ α₂ α₃ y z (1 / 16) (by norm_num) hz
    (by convert hyz using 1; norm_num) (by linarith) (M ω)
  rw [fusionMovingMass_split]
  exact ENNReal.add_ne_top.mpr ⟨hωb, ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωg) hg⟩
/-- Local positive moments and exterior domination make this rooted endpoint finite. -/
theorem fusionRootOnlyMass_finite_near {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2))))
    (y z : ℂ) (hy : y ≠ 0) (hz : ‖z‖ ≤ 1 / 16) (hyz : ‖y * z‖ ≤ 1 / 32) :
    ∀ᵐ ω ∂P, fusionRootOnlyMass γ α₁ α₂ α₃ y z (M ω) ≠ ⊤ := by
  obtain ⟨_, C, hC, hb⟩ := fusion_rootOnlyKernel_smallBall_moment P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ p hα hp hp1 hpRange y hy
  have hbad : ∀ᵐ ω ∂P, fusionRootOnlyBadMass γ α₁ α₂ α₃ y z (1 / 16) (M ω) ≠ ⊤ :=
    fusion_mass_finite_of_moment (fusionRootOnlyBadMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z (1 / 16))
      hp (lt_of_le_of_lt (hb (1 / 16) (by norm_num) le_rfl z (by linarith))
        (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top))
  have hgood0 : ∀ᵐ ω ∂P, fusionRootOnlyGoodMass γ α₁ α₂ α₃ y 0 (1 / 16) (M ω) ≠ ⊤ := by
    filter_upwards [fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃] with ω hω
    exact (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (by
      simpa only [fusionRootOnlyKernel, mul_zero] using hω)).ne
  filter_upwards [hbad, hgood0] with ω hωb hωg
  have hg := fusionRootOnlyGoodMass_le γ α₁ α₂ α₃ y z (1 / 16) (by norm_num) hz
    (by convert hyz using 1; norm_num) (by linarith) (M ω)
  rw [fusionRootOnlyMass_split]
  exact ENNReal.add_ne_top.mpr ⟨hωb, ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωg) hg⟩
end DOZZ.Proofs
