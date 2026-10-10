/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ConvexMass
public import DOZZ.FourPoint.Fusion.InterpolationFiniteness
public import DOZZ.FourPoint.Fusion.InverseExpectation
/-! # Vitali convergence for the KRV interpolation segment -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs
noncomputable def fusionInterpolatedMass (γ α₁ α₂ α₃ t : ℝ) (y z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal t * fusionMovingMass γ α₁ α₂ α₃ y z μ +
    ENNReal.ofReal (1 - t) * fusionRootOnlyMass γ α₁ α₂ α₃ y z μ
/-- The larger inverse order is uniform over the complete interpolation segment. -/
theorem fusionInterpolatedMass_inverse_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ y z : ℂ, ‖z‖ ≤ 1 →
      (∫⁻ ω, fusionInterpolatedMass γ α₁ α₂ α₃ t y z (M ω) ^ s ∂P) ≤ C := by
  obtain ⟨C1, hC1, hb1⟩ := fusionMovingMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs
  obtain ⟨C2, hC2, hb2⟩ := fusionRootOnlyMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs
  refine ⟨C1 + C2, ENNReal.add_lt_top.mpr ⟨hC1, hC2⟩, ?_⟩
  intro t ht y z hz
  calc
    _ ≤ ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s +
        fusionRootOnlyMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P :=
      lintegral_mono fun ω => fusion_convexMass_inverse_bound _ _ t s ht hs
    _ = _ := lintegral_add_left' ((fusionMovingMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z).pow_const s) _
    _ ≤ C1 + C2 := add_le_add (hb1 y z hz) (hb2 y z hz)
/-- The two rooted endpoints converge to the same mass; uniform larger inverse moments give
Vitali convergence of their interpolated inverse expectation. -/
theorem fusionInterpolatedMass_inverse_expectation_seq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (y : ℂ) (hy : y ≠ 0) (z : ℕ → ℂ) (hz : Tendsto z atTop (nhds 0))
    (s : ℝ) (hs : s < 0) :
    Tendsto (fun n => ∫⁻ ω, fusionInterpolatedMass γ α₁ α₂ α₃ t y (z n) (M ω) ^ s ∂P)
      atTop (nhds (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) ^ s ∂P)) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨p, hp, hp1, hpR⟩ := fusion_small_moment_order γ α₁ hγ hα₁
  obtain ⟨C, hC, hb⟩ := fusionInterpolatedMass_inverse_uniform P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (2 * s) (by linarith)
  have hn : ∀ᶠ n in atTop, ‖z n‖ ≤ 1 / 16 ∧ ‖y * z n‖ ≤ 1 / 32 := by
    have h1 : Tendsto (fun n => ‖z n‖) atTop (nhds 0) := by
      simpa only [Function.comp_def, norm_zero] using continuous_norm.continuousAt.tendsto.comp hz
    have h2 : Tendsto (fun n => ‖y * z n‖) atTop (nhds 0) := by
      have hc : Continuous (fun w : ℂ => ‖y * w‖) := by fun_prop
      simpa only [Function.comp_def, mul_zero, norm_zero] using hc.continuousAt.tendsto.comp hz
    exact ((h1.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 16)).and
      (h2.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 32))).mono fun _ h => ⟨h.1.le, h.2.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hn
  let a := fun n ω => fusionMovingMass γ α₁ α₂ α₃ y (z (n + N)) (M ω)
  let b := fun n ω => fusionRootOnlyMass γ α₁ α₂ α₃ y (z (n + N)) (M ω)
  let f := fun n ω => fusionInterpolatedMass γ α₁ α₂ α₃ t y (z (n + N)) (M ω)
  let g := fun ω => fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω)
  have ham : ∀ n, AEMeasurable (a n) P := fun n => fusionMovingMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y _
  have hbm : ∀ n, AEMeasurable (b n) P := fun n => fusionRootOnlyMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y _
  have hfm : ∀ n, AEMeasurable (f n) P := fun n => (ham n).const_mul _ |>.add ((hbm n).const_mul _)
  have hgm : AEMeasurable g P := fusionMovingMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y 0
  have haf : ∀ n, ∀ᵐ ω ∂P, a n ω ≠ ⊤ := fun n => fusionMovingMass_finite_near P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p
    hα hα₁ hα₂ hα₃ hp hp1 hpR y _ hy (hN _ (Nat.le_add_left N n)).1 (hN _ (Nat.le_add_left N n)).2
  have hbf : ∀ n, ∀ᵐ ω ∂P, b n ω ≠ ⊤ := fun n => fusionRootOnlyMass_finite_near P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p
    hα hα₁ hα₂ hα₃ hp hp1 hpR y _ hy (hN _ (Nat.le_add_left N n)).1 (hN _ (Nat.le_add_left N n)).2
  have hac := fusionMovingMass_tendstoInMeasure_seq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p
    hα hα₁ hα₂ hα₃ hp hp1 hpR y hy (fun n => z (n + N)) (hz.comp (tendsto_add_atTop_nat N))
  have hbc : TendstoInMeasure P (fun n ω => (b n ω).toReal) atTop (fun ω => (g ω).toReal) := by
    simpa only [b, g, fusionRootOnlyMass, fusionRootOnlyKernel, fusionMovingMass, fusionMovingKernel, mul_zero] using
      fusionRootOnlyMass_tendstoInMeasure_seq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p
        hα hα₁ hα₂ hα₃ hp hp1 hpR y hy (fun n => z (n + N)) (hz.comp (tendsto_add_atTop_nat N))
  have hc := fusion_convexMass_tendstoInMeasure P a b g ham hbm haf hbf hac hbc t ht
  have hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤ := by
    simpa only [g, fusionMovingMass, fusionMovingKernel, mul_zero] using
      (fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃).mono fun _ h => h.ne
  have hfb : ∀ n, ∫⁻ ω, f n ω ^ (2 * s) ∂P ≤ C := fun n => hb t ht y _ (by linarith [(hN _ (Nat.le_add_left N n)).1])
  have hgb : ∫⁻ ω, g ω ^ (2 * s) ∂P ≤ C := by
    have h := hb t ht y 0 (by simp)
    have he : fusionInterpolatedMass γ α₁ α₂ α₃ t y 0 = fusionMovingMass γ α₁ α₂ α₃ y 0 := by
      funext μ
      unfold fusionInterpolatedMass fusionRootOnlyMass fusionRootOnlyKernel fusionMovingMass fusionMovingKernel
      simp only [mul_zero]
      rw [← add_mul, ← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr ht.2)]
      simp
    simpa only [he] using h
  have hfp : ∀ n, ∀ᵐ ω ∂P, f n ω ^ s ≠ ⊤ := fun n =>
    momentConv_ae_rpow_ne_top_of_neg P (f n) (hfm n) hs (by linarith) hC.ne (hfb n)
  have hgp := momentConv_ae_rpow_ne_top_of_neg P g hgm hs (by linarith) hC.ne hgb
  have hr : 1 < (2 * s) / s := by rw [mul_div_cancel_right₀ _ hs.ne]; norm_num
  exact (tendsto_add_atTop_iff_nat N).mp
    (momentConv_tendsto_of_rpow_ne_top P f g hfm hgfin hc hs.ne hr hC.ne hfb hfp hgp)
end DOZZ.Proofs
