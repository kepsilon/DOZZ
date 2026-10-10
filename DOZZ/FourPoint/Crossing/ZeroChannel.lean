/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.CollisionFourPoint
public import DOZZ.Hypergeom.ClassificationPhysicalNormalization
import Mathlib.Tactic

/-! # The normalization part of physical diagonal classification

The only premise beyond the strict Seiberg domain is the literal half-charge
conclusion of the BPZ theorem `DOZZ.degenerateFourPoint_BPZ`. The generic Gauss classification
and the collision limit supply the normalized physical representation.
-/

public section
open MeasureTheory Filter Topology
namespace DOZZ.Proofs

/-- The half-charge specialization of physical classification follows from the
literal BPZ conclusion; its probabilistic normalization has no remaining input. -/
theorem gammaHalf_zero_channel_of_gauss_solution {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ a b c : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (hs : 2 * Q γ + γ / 2 < a + b + c)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hT : IsRealGaussSolution (gaussParameterA γ (γ / 2) a b c)
      (gaussParameterB γ (γ / 2) a b c) (gaussParameterC γ (γ / 2) a)
      (fun z => fourPointT P M γ μ (-γ / 2) a b c z)) :
    let A := gaussParameterA γ (γ / 2) a b c
    let B := gaussParameterB γ (γ / 2) a b c
    let C := gaussParameterC γ (γ / 2) a
    ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) a b c z =
      structureConstant P M γ μ (a - γ / 2) b c *
        (‖gaussFMinus H A B C z‖ ^ 2 + gaussCoefficientRatio A B C * ‖gaussFPlus H A B C z‖ ^ 2) := by
  have hs0 : 2 * Q γ < a + b + c - γ / 2 := by linarith only [hs]
  have haF : a - γ / 2 < Q γ := by linarith only [ha, hγ]
  have hzero := fourPointT_zero_eq_structureConstant P X M γ μ (γ / 2) a b c
    hγ hγ2 hμ haF hb hc hs0 hX hM
  have hlim := gammaHalf_fourPoint_collision_limit P X M γ μ a b c
    hγ hγ2 hμ ha hb hc hs0 hX hM
  have hcont : ContinuousAt (fun z => fourPointT P M γ μ (-γ / 2) a b c z) 0 := by
    exact continuousAt_of_tendsto_nhds hlim
  have hnorm := real_gauss_solution_physical_normalization hH γ (γ / 2) a b c
    hγ hγ2 (Or.inl rfl) hs ha hb hc
    (fun z => fourPointT P M γ μ (-γ / 2) a b c z) hT hcont
  dsimp only
  intro z hz
  have hzrep := hnorm z hz
  simp only [neg_div] at hzrep ⊢
  rw [hzero] at hzrep
  exact hzrep

end DOZZ.Proofs
