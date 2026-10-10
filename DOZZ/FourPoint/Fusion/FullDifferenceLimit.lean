/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.LocalDifferenceLimit
public import DOZZ.FourPoint.Fusion.ExteriorDifferenceLimit
public import DOZZ.FourPoint.Fusion.DifferenceTimeSplit
public import DOZZ.FourPoint.Fusion.MassExpectationInterpolation
/-! # The complete signed KRV inverse-moment limit -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- Local scaling and the negligible exterior error give the full inverse-expectation coefficient. -/
theorem fusion_massDifference_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 + 1 / γ < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ =>
      ((∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p) ∂P).toReal -
        (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal) /
          ‖z‖ ^ (γ * (Q γ - α₁))) (nhdsWithin 0 {0}ᶜ)
      (nhds (-p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p)) := by
  obtain ⟨_, _, _, _, hκ⟩ := fusion_difference_parameters γ α₁ hγ hlo hα₁
  have hl := fusion_localDifference_normalized_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  have hr := fusion_exteriorDifference_normalized_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp _ hκ
  have h := (tendsto_const_nhds (x := -p)).mul (hl.add hr)
  simp only [add_zero] at h
  apply h.congr'
  have hz4 : ∀ᶠ z : ℂ in nhdsWithin 0 {0}ᶜ, ‖z‖ ≤ 1 / 4 :=
    (((continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp : ‖(0 : ℂ)‖ < (1 / 4 : ℝ))).filter_mono
      nhdsWithin_le_nhds).mono fun _ h => h.le
  filter_upwards [hz4, self_mem_nhdsWithin] with z hz4 hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
  rw [fusion_mass_expectation_interpolation P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp z hz0 hz4,
    fusion_difference_time_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp z hz0 hz4]
  ring
end DOZZ.Proofs
