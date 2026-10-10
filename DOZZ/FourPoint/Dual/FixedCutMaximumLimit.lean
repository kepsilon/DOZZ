/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceParetoCutLimit
public import DOZZ.FourPoint.Dual.SourceParetoCutIncrement
public import DOZZ.FourPoint.Dual.SourceMaximumPareto
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.FourPoint.Reflected.RestartedWilliams
public import DOZZ.FourPoint.Dual.RadialFirstOrder
import Mathlib.Tactic
/-! The Williams reference-maximum expectation has its normalized source limit. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual independent Pareto maximum, full reflection mass, retained source mass and
radial restart scale give the required leading coefficient for each fixed radial buffer. -/
theorem dual_source_cut_maximum_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h c₀ : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+2/γ < α₁+α₂+α₃)
    (hshifted : 2*Q γ-α₁-2/γ < Q γ)
    (hslack : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
    let D := fun z : ℂ => ∫ v : Ω × (ℝ × Ω),
      (((dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        dual_radial_scale γ ν h Xc z v.1*(Real.exp (γ*v.2.1)*(twoSidedReflectionCutMass γ c₀ B Z v.2.2).toReal))^(-p)-
        (dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal ^(-p))
        ∂P.prod ((brownianMaximumReferenceLaw ν).prod P)
    Tendsto (fun z => D z/‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionCutMass γ c₀ B Z ω ^a ∂P).toReal)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  obtain ⟨A, _, hA, _, hB, _, _, _, _, _⟩ :=
    DOZZ.equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ₂ hX hM
  let W := P.map (fun ω => radialPositiveHalf (A ω))
  have hW : IsBrownianReal (fun t p => p t) W :=
    radialPositiveHalf_map_isBrownian P A hA hB
  have hSm : AEMeasurable (fun ω => (twoSidedReflectionCutMass γ c₀ B Z ω).toReal) P :=
    (twoSidedReflectionCutMass_aemeasurable P γ c₀ B Z
      (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1.2.2.2.1
        hData.2.1.2.2.2.2.1).ennreal_toReal
  have ht := dual_source_pareto_cut_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    α₁ α₂ α₃ ξ h c₀ hα₁ hreflect hα₂ hα₃ hh hs hshifted hslack hξ hξ1 B Z hData
  apply ht.congr'
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖(0 : ℂ)‖) :=
    (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))]
    with z hz0 hz
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hInt := (dual_source_pareto_cut_increment_error P X hX γ hγ hγ₂ M hM Xc hc
    α₁ α₂ α₃ ξ h p c₀ hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1 B Z hData z hz0 hz1 hz.le).1
  have he := dual_source_fixed_maximum_increment_eq_pareto P X hX γ hγ hγ₂ M hM Xc hc
    α₁ α₂ α₃ ξ h p hα₁ hα₂ hα₃ hh hp hξ hξ1
    (fun ω => (twoSidedReflectionCutMass γ c₀ B Z ω).toReal) hSm (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    W hW z hz0 hz1 hz.le hInt
  rw [he]

end DOZZ.Proofs
