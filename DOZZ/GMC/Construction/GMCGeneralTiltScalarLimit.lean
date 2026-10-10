/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTilt
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Measurable factorization inputs for the general GMC Cameron--Martin identity. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem regularized_testIntegral_raw_measurable_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hμ : Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => regularizedGMC P Xc γ r ω)) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =ᵐ[P] g := by
  let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
  have hfinite := regularizedGMC_finite_ae P X hX Xc hXc γ r
  let pos : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂μ ω
  let neg : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂μ ω
  have hpos : Measurable[equatorGFFRawDistributionSigma X] pos := by
    dsimp [pos]
    exact (Measure.measurable_lintegral
      (BoundedContinuousFunction.measurable_coe_ennreal_comp f.nnrealPart)).comp hμ
  have hneg : Measurable[equatorGFFRawDistributionSigma X] neg := by
    dsimp [neg]
    exact (Measure.measurable_lintegral
      (BoundedContinuousFunction.measurable_coe_ennreal_comp (-f).nnrealPart)).comp hμ
  have hproxy : Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => (pos ω).toReal - (neg ω).toReal) := by
    fun_prop
  have heq :
      (fun ω => ∫ x, f x ∂μ ω) =ᵐ[P]
        fun ω => (pos ω).toReal - (neg ω).toReal := by
    filter_upwards [hfinite] with ω hω
    rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub (μ := μ ω) f]
    rw [← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f.nnrealPart (μ ω)]
    rw [← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral (-f).nnrealPart (μ ω)]
  exact ⟨_, hproxy, heq⟩

/-- A bounded-continuous test integral of an `IsGMCOf` limit has a raw-measurable version when its
cutoff random measures are raw-measurable. The version is the limit of measurable proxies for a
subsequence of cutoff integrals. -/
theorem equatorGFF_GMC_testIntegral_raw_measurable_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : Ω → Measure ℂ)
    (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω))
    (hCut : ∀ r,
      Measurable[equatorGFFRawDistributionSigma X]
        (fun ω => regularizedGMC P Xc γ r ω))
    (f : BoundedContinuousFunction ℂ ℝ) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] g := by
  have hconvNat : TendstoInMeasure P
      (fun n : ℕ => fun ω => ∫ x, f x ∂regularizedGMC P Xc γ (n : ℝ) ω) atTop
      (fun ω => ∫ x, f x ∂M ω) :=
    (hconv f).comp tendsto_natCast_atTop_atTop
  obtain ⟨ns, hns, hnsAE⟩ := hconvNat.exists_seq_tendsto_ae
  have hseq : ∀ n, ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ (ns n : ℝ) ω) =ᵐ[P] g := by
    intro n
    exact regularized_testIntegral_raw_measurable_proxy P X hX Xc hXc γ (ns n : ℝ) f
      (hCut (ns n : ℝ))
  choose g hgmeas hgae using hseq
  let gLim : Ω → ℝ := fun ω => limUnder atTop (fun n => g n ω)
  have hgLim : Measurable[equatorGFFRawDistributionSigma X] gLim := by
    let : MeasurableSpace Ω := equatorGFFRawDistributionSigma X
    exact (StronglyMeasurable.limUnder (l := atTop)
      (fun n => (hgmeas n).stronglyMeasurable)).measurable
  have hAEproxy : ∀ᵐ ω ∂P, ∀ n,
      (∫ x, f x ∂regularizedGMC P Xc γ (ns n : ℝ) ω) = g n ω :=
    ae_all_iff.mpr hgae
  have hEq : (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] gLim := by
    filter_upwards [hnsAE, hAEproxy] with ω hω hωeq
    have hT : Tendsto (fun n => g n ω) atTop
        (𝓝 (∫ x, f x ∂M ω)) :=
      (hω.congr' (Filter.Eventually.of_forall hωeq))
    change (∫ x, f x ∂M ω) = limUnder atTop (fun n => g n ω)
    exact hT.limUnder_eq.symm
  exact ⟨gLim, hgLim, hEq⟩

end DOZZ.Proofs
