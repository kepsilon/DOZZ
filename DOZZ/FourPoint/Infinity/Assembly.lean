/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Infinity.MovingMoment
public import DOZZ.FourPoint.Infinity.CanonicalMoment
public import DOZZ.FourPoint.Infinity.Normalization
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The normalized finite correlation converges to its moment formula
[KRV, (expression3pointstruct)]. -/
theorem structureConstant_infinity_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto
      (fun z : ℂ => ‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re) *
        threePointFiniteCorrelation P M γ μ α₁ α₂ α₃ z)
      (Filter.cocompact ℂ)
      (nhds (structureConstant P M γ μ α₁ α₂ α₃)) := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hdiff : Tendsto (fun z : ℂ => (1 : ℂ) - z⁻¹) (cocompact ℂ) (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℂ))).sub hinv
  have hr : Tendsto (fun z : ℂ => ‖1 - z⁻¹‖ ^ (-(α₂ * α₃))) (cocompact ℂ) (𝓝 1) := by
    simpa only [norm_one, Real.one_rpow] using hdiff.norm.rpow_const
      (p := -(α₂ * α₃)) (Or.inl (norm_ne_zero_iff.mpr one_ne_zero))
  have heq := infinity_canonical_moment_eq P X M γ α₁ α₂ α₃ (-sExp γ α₁ α₂ α₃)
    hγ hγ₂ hX hM
  have hm : Tendsto (fun z : ℂ => (∫⁻ ω,
      (coulombMass γ (M ω) ![α₃, α₂] ![z⁻¹, 1] α₁) ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal)
      (cocompact ℂ) (𝓝 (∫⁻ ω, (rho γ (M ω) α₁ α₂ α₃) ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal) := by
    simpa only [Function.comp_def, heq] using
      (infinity_moving_moment_continuousAt_zero P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hα₂ hα₃
        hs hX hM).tendsto.comp hinv
  have hlim := ((tendsto_const_nhds (x :=
      2 / μ ^ (sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃))).mul hr).mul hm
  simp only [mul_one] at hlim
  have hnorm : Tendsto (fun z : ℂ => ‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re) *
      threePointFiniteCorrelation P M γ μ α₁ α₂ α₃ z) (cocompact ℂ)
      (𝓝 ((2 / μ ^ (sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃)) *
        (∫⁻ ω, (rho γ (M ω) α₁ α₂ α₃) ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal)) := by
    apply hlim.congr'
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
    exact (infinity_normalized_correlation_eq P X M γ μ α₁ α₂ α₃ hγ hγ₂ hμ.le hX hM z hz0).symm
  simpa only [structureConstant, Real.rpow_neg hμ.le, div_eq_mul_inv, ENNReal.rpow_eq_pow]
    using hnorm

end DOZZ.Proofs
