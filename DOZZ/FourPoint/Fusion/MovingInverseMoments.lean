/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingMassConvergence
public import DOZZ.FourPoint.Fusion.RootedLowerBound
import DOZZ.GMC.SharpMoments.MomentConvergence

/-! # Convergence of the inverse moments of the moving rooted mass -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- All inverse orders are uniformly bounded, including a larger order for Vitali. -/
theorem fusionMovingMass_inverse_moment_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ y z : ℂ, ‖z‖ ≤ 1 →
      (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := fusion_rootedMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ s hs
  refine ⟨C, hC, ?_⟩
  intro y z hz
  have he : (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P) =
      ∫⁻ ω, coulombMass γ (gmcRootedMeasure γ (y * z) (M ω))
        ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P := by
    apply lintegral_congr_ae
    filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z]
      with ω hω
    rw [hω]
  rw [he]
  apply hbound
  intro j
  fin_cases j
  · exact hz
  · norm_num
  · norm_num

/-- Vitali gives inverse-moment expectation convergence along every sequence approaching zero. -/
theorem fusionMovingMass_inverse_expectation_seq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2))))
    (y : ℂ) (hy : y ≠ 0) (z : ℕ → ℂ) (hz : Tendsto z atTop (nhds 0))
    (s : ℝ) (hs : s < 0) :
    Tendsto (fun n => ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y (z n) (M ω) ^ s ∂P)
      atTop (nhds (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) ^ s ∂P)) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨C, hC, hbound⟩ := fusionMovingMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ (2 * s) (by linarith)
  have hn : ∀ᶠ n in atTop, ‖z n‖ ≤ 1 := by
    have h : Tendsto (fun n => ‖z n‖) atTop (nhds 0) := by
      simpa only [Function.comp_def, norm_zero] using continuous_norm.continuousAt.tendsto.comp hz
    exact (h.eventually_lt_const zero_lt_one).mono fun _ h => h.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hn
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω => fusionMovingMass γ α₁ α₂ α₃ y (z (n + N)) (M ω)
  let g : Ω → ℝ≥0∞ := fun ω => fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω)
  have hf : ∀ n, AEMeasurable (f n) P := fun n =>
    fusionMovingMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y (z (n + N))
  have hg : AEMeasurable g P := fusionMovingMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y 0
  have hgb : ∫⁻ ω, g ω ^ (2 * s) ∂P ≤ C := hbound y 0 (by simp)
  have hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤ := by
    simpa only [g, fusionMovingMass, fusionMovingKernel, mul_zero] using
      (fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃).mono
        fun _ h => h.ne
  have hfb : ∀ n, ∫⁻ ω, f n ω ^ (2 * s) ∂P ≤ C := fun n =>
    hbound y (z (n + N)) (hN _ (Nat.le_add_left N n))
  have hconv := fusionMovingMass_tendstoInMeasure_seq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p
    hα hα₁ hα₂ hα₃ hp hp1 hpRange y hy (fun n => z (n + N))
    (hz.comp (tendsto_add_atTop_nat N))
  have hfp : ∀ n, ∀ᵐ ω ∂P, f n ω ^ s ≠ ⊤ := fun n =>
    momentConv_ae_rpow_ne_top_of_neg P (f n) (hf n) hs (by linarith) hC.ne (hfb n)
  have hgp : ∀ᵐ ω ∂P, g ω ^ s ≠ ⊤ :=
    momentConv_ae_rpow_ne_top_of_neg P g hg hs (by linarith) hC.ne hgb
  have hratio : 1 < (2 * s) / s := by rw [mul_div_cancel_right₀ _ hs.ne]; norm_num
  have hlim := momentConv_tendsto_of_rpow_ne_top P f g hf hgfin hconv hs.ne hratio hC.ne hfb hfp hgp
  exact (tendsto_add_atTop_iff_nat N).mp hlim

end DOZZ.Proofs
