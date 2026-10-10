/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.FullDifferenceLimit
public import DOZZ.FourPoint.Fusion.Coefficient
public import DOZZ.FourPoint.FourPointTZeroEqStructureConstant
/-! # The restricted gamma-half KRV fusion asymptotic -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs
/-- Restricted fusion of [KRV-local]: signed rooting and scaling give the collision asymptotic on
the restricted range. -/
theorem gammaHalf_KRV_restricted_fusion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγsq : γ ^ 2 < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 + 1 / γ < α₁) (hαhi : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let κ := γ * (Q γ - α₁)
    ∃ r : ℂ → ℝ,
      (∀ z, fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              (‖z‖ ^ κ : ℝ) + r z) ∧
        Tendsto (fun z => r z / ‖z‖ ^ κ)
          (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  intro κ
  have hγ2 : γ < 2 := by nlinarith
  let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  let B := 2 * μ ^ (-p) / γ * Real.Gamma p
  let C := (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
    structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃
  let F := fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃
  let C₀ := structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃
  have hp : 0 ≤ p := (div_pos (by linarith) hγ).le
  have hse : fourPointSExp γ (-γ / 2) α₁ α₂ α₃ = p := by
    unfold fourPointSExp p
    congr 1
    ring
  have hzero : F 0 = C₀ := by
    simpa only [F, C₀, neg_div] using fourPointT_zero_eq_structureConstant P X M γ μ (γ / 2) α₁ α₂ α₃
      hγ hγ2 hμ (by unfold Q; linarith) hα₂ hα₃ (by linarith) hX hM
  have hnorm := (tendsto_const_nhds (x := B)).mul
    (fusion_massDifference_normalized_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hαlo hαhi hα₂ hα₃ p hp)
  have hcoef : B * (-p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p) = C :=
    fusion_normalized_rootedCoefficient P X hX γ hγ hγ2 M hM μ α₁ α₂ α₃ hμ hs
  rw [hcoef] at hnorm
  have hlim : Tendsto (fun z : ℂ => (F z - C₀) / ‖z‖ ^ κ)
      (nhdsWithin 0 {0}ᶜ) (nhds C) := by
    apply hnorm.congr'
    apply Eventually.of_forall
    intro z
    rw [← hzero]
    simp only [F, fourPointT, hse, ENNReal.rpow_eq_pow]
    change B * (_ / ‖z‖ ^ κ) = (B * _ - B * _) / ‖z‖ ^ κ
    ring
  refine ⟨fun z => F z - C₀ - C * ‖z‖ ^ κ, ?_, ?_⟩
  · intro z
    change F z = C₀ + C * ‖z‖ ^ κ + (F z - C₀ - C * ‖z‖ ^ κ)
    ring
  · have h := hlim.sub (tendsto_const_nhds (x := C))
    simp only [sub_self] at h
    have hsfilter : {z : ℂ | z ≠ 0} = {0}ᶜ := by ext z; simp
    rw [hsfilter]
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
    simp only [sub_div, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _).ne']
end DOZZ.Proofs
