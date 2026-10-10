/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.FullTimeSplit
public import DOZZ.FourPoint.Fusion.ExteriorTimeError
public import DOZZ.FourPoint.Fusion.LocalTaylorSum
/-! # The full signed one-rooted Taylor limit -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- Adding the quadratic exterior errors preserves the exact local coefficient. -/
theorem fusionFullOneRooted_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ => gammaHalfOneRootedTerm P M γ α₁ α₂ α₃ p z /
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ)) (nhdsWithin 0 {0}ᶜ)
      (nhds ((-p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p : ℝ) : ℂ)) := by
  let κ := γ * (Q γ - α₁)
  let E1 := fusionPureSpatial P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ
  let E2 := fusionMixedSpatial P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ
  let R1 := fun z : ℂ => ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2 *
    (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * E1 ((t : ℂ) * z))
  let R2 := fun z : ℂ => ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z *
    (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * E2 ((t : ℂ) * z))
  have hκ : κ < 2 := (fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁).2.2.2.2.2
  obtain ⟨C1, hC1, hb1⟩ := fusion_exteriorR1_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  obtain ⟨C2, hC2, hb2⟩ := fusion_exteriorR2_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have hR1 : IsComplexLittleOAtZero κ R1 := fusion_quadratic_time_error E1 _ κ C1 hC1.le hκ
    (fun z hz hz4 => (hb1 z hz hz4).2)
  have hR2 : IsComplexLittleOAtZero κ R2 := fusion_mixed_quadratic_time_error E2 _ κ C2 hC2.le hκ
    (fun z hz hz4 => (hb2 z hz hz4).2)
  have h1 := fusion_normalized_tendsto_of_littleO κ R1 hR1
  have h2 := fusion_normalized_tendsto_of_littleO κ R2 hR2
  have hl := fusionLocalOneRooted_normalized_tendsto P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp
  have h := ((hl.add h1).add h2).add h1.star
  simp only [add_zero, star_zero] at h
  apply h.congr'
  have hz4 : ∀ᶠ z : ℂ in nhdsWithin 0 {0}ᶜ, ‖z‖ ≤ 1 / 4 := by
    have h : ∀ᶠ z : ℂ in nhds 0, ‖z‖ < 1 / 4 :=
      (continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)
    exact (h.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
  filter_upwards [hz4, self_mem_nhdsWithin] with z hz4 hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
  have hs1 := fusionRootedR1_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp z hz0 hz4
  have hs2 := fusionRootedR2_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp z hz0 hz4
  change gammaHalfRootedR1 P M γ α₁ α₂ α₃ p z = fusionLocalR1 P M γ α₁ α₂ α₃ p z + R1 z at hs1
  change gammaHalfRootedR2 P M γ α₁ α₂ α₃ p z = fusionLocalR2 P M γ α₁ α₂ α₃ p z + R2 z at hs2
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  dsimp only [κ]
  simp only [gammaHalfOneRootedTerm, gammaHalfRootedR3, hs1, hs2, star_add,
    star_div₀, hreal]
  ring
end DOZZ.Proofs
