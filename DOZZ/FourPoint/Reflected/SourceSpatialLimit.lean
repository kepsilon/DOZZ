/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SpatialGuard
/-! Spatial cutoff removal for the supplied ordinary GMC, with no extra moment assumption. -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- On a retained open domain containing the fixed guard, compact reflected-kernel tests
converge at every inverse order for the actual supplied GMC. -/
theorem reflected_source_spatial_inverse_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1)
    (U : Set ℂ) (hU : IsOpen U) (hroots : U ⊆ ({0, 1} : Set ℂ)ᶜ)
    (hDU : Metric.closedBall (3 : ℂ) (1/8) ⊆ U) :
    ∃ g : ℕ → BoundedContinuousFunction ℂ ℝ,
      (∀ n, EqOn (g n) (gammaHalfKernel γ α₁ α₂ α₃ z)
        (Metric.closedBall (3 : ℂ) (1/8))) ∧
      (∀ n, IsCompact (tsupport (g n : ℂ → ℝ))) ∧
      (∀ n, tsupport (g n : ℂ → ℝ) ⊆ U) ∧
      (∀ n x, 0 ≤ g n x) ∧
      ∀ q : ℝ, 0 ≤ q →
        Tendsto (fun n => ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (g n x) ∂M ω)^(-q) ∂P)
          atTop (𝓝 (∫⁻ ω, (∫⁻ x in U,
            ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P)) := by
  obtain ⟨g, hgD, hgc, hgU, hgn, hlim⟩ :=
    reflected_spatial_kernel_inverse_approximation γ α₁ α₂ α₃ z U hU hroots
      (Metric.closedBall (3 : ℂ) (1/8)) (isCompact_closedBall _ _) hDU
  refine ⟨g, hgD, hgc, hgU, hgn, ?_⟩
  intro q hq
  obtain ⟨M', hM', _, heq⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ₂ M hM
  have hinj : Function.Injective (![z, 0, 1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hcharges : ∀ i : Fin 3, (![-γ/2, α₁, α₂] : Fin 3 → ℝ) i < Q γ := by
    intro i
    fin_cases i
    · have hQ : 0 < Q γ := by unfold Q; positivity
      change -γ/2 < Q γ
      linarith
    · exact hα₁
    · exact hα₂
  have hfin : ∀ᵐ ω ∂P, (∫⁻ x in U,
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M' ω) ≠ ⊤ := by
    filter_upwards [heq,
      reflected_coulombMass_ae_finite P X hX γ hγ hγ₂ M hM
        ![z, 0, 1] hinj ![-γ/2, α₁, α₂] α₃ hcharges hα₃,
      gammaHalfMass_eq_coulombMass_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ z]
      with ω he hf hk
    rw [← he]
    exact ne_top_of_le_ne_top (hk.trans_lt hf).ne (setLIntegral_le_lintegral _ _)
  have hguard : (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M' ω)^(-q) ∂P) ≠ ⊤ := by
    have he : (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M' ω)^(-q) ∂P) =
        ∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      rw [← hω]
    rw [he]
    exact (reflected_spatial_guard_inverse_finite P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq z hz).ne
  have ht := hlim P M' hM' hfin q hq hguard
  have hn (n : ℕ) : (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (g n x) ∂M' ω)^(-q) ∂P) =
      ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (g n x) ∂M ω)^(-q) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [heq] with ω hω
    rw [← hω]
  have hu : (∫⁻ ω, (∫⁻ x in U,
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M' ω)^(-q) ∂P) =
      ∫⁻ ω, (∫⁻ x in U, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [heq] with ω hω
    rw [← hω]
  simpa only [hn, hu] using ht

end DOZZ.Proofs
