/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ActualPrefactorUniform
public import DOZZ.Brownian.Reflection.Moments

/-! Uniform moments of the actual independent pin times reflection mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem prefactored_reflection_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (K : Set ℂ) (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    (γ b R ν₁ ν₂ : ℝ) (hγ : 0 < γ) (hb : 0 ≤ b)
    (hR : 0 < R) (hRbulk : R < 4/γ^2) (hν₁ : 0 < ν₁)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ f : ℝ, 0 ≤ f → f ≤ b →
      ∀ ν : ℝ, ν₁ ≤ ν → ν ≤ ν₂ → ∀ r : ℝ, 0 < r → r ≤ R →
      ∀ B : Ω → BrownianPath × BrownianPath,
        IsTwoSidedConditionedBrownianProcess P B ν → IndepFun B Z P →
        (∫⁻ q : Ω × Ω, (ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
          Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*twoSidedReflectionMass γ B Z q.1)^r
          ∂P.prod P) ≤ C := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨L,hL,hPin⟩ := actual_prefactor_moment_uniform P X Xc hX hc K hK hz γ b R hb hR
  obtain ⟨D,hD,hRef⟩ := twoSidedReflectionMass_rpow_lintegral_le_compact P γ ν₁ ν₂ R
    hγ hν₁ hR hRbulk Z hZ
  refine ⟨D*L,ENNReal.mul_lt_top hD hL,?_⟩
  intro z hzk f hf hfb ν hνlo hνhi r hr hrR B hB hInd
  let S := fun ω => ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
    Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))
  have hSm : Measurable S := by
    have hp : Measurable (fun ω => Xc ω z 0) :=
      (hc.1 0).comp (measurable_id.prodMk measurable_const)
    exact (((hp.const_mul γ).sub_const _).exp.const_mul _).ennreal_ofReal
  have hJm := twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z
    (aemeasurable_of_twoSidedConditioned hB) hZ
  have hJbound := hRef ν hνlo hνhi r hr.le hrR B hB hInd
  change (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^ r ∂P) ≤ D at hJbound
  calc
    _ = ∫⁻ q : Ω × Ω, twoSidedReflectionMass γ B Z q.1 ^ r * S q.2 ^ r ∂P.prod P := by
      apply lintegral_congr
      intro q
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,mul_comm]
    _ = (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^ r ∂P) * ∫⁻ ω, S ω ^ r ∂P :=
      lintegral_prod_mul (hJm.pow_const r) (hSm.aemeasurable.pow_const r)
    _ ≤ D*L := mul_le_mul' hJbound (hPin z hzk f hf hfb r hr hrR)


end DOZZ.Proofs
