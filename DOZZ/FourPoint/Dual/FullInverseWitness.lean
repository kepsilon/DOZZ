/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceFullInverseLimit
public import DOZZ.FourPoint.Dual.Window
public import DOZZ.FourPoint.Reflected.SourceLateralWitness
public import DOZZ.Brownian.Lateral.GlobalIndependence
import Mathlib.Tactic
/-! The corrected near-Q window has a common source witness for actual full fusion. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Choose the complete reflection family and original source lateral projection before
specializing the parameter; the actual full stochastic fusion limit holds on that witness. -/
theorem dual_source_full_inverse_fusion_witness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ α₁ α₂ α₃ η ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hη : 0 < η) (hη₂ : η < γ / 2) (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hαlo : Q γ - η < α₁) (hαhi : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hslack₁ : (4 / γ) * (Q γ - α₁) < ξ)
    (hslack₂ : (4 / γ) * (Q γ - α₁) <
      (1 - ξ) * (4 - γ * α₁ - 2 * γ * η))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α₁ (B α₁) Z ∧
        let ν := Q γ-α₁
        let a := 2*ν/γ
        let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
        Tendsto (fun z : ℂ =>
          ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-p) ∂P).toReal-
            (∫⁻ ω, coulombMass γ (M ω) ![-2/γ,α₁,α₂] ![0,0,1] α₃^(-p) ∂P).toReal)/
              ‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
          (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
            (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃^(-(p+a)) ∂P).toReal*
            (∫⁻ ω, twoSidedReflectionMass γ (B α₁) Z ω^a ∂P).toReal)) := by
  obtain ⟨Xc, B, hc, hm, hcont, hSource, hZ, hB⟩ :=
    reflected_regular_source_reflection_family P X hX γ hγ hγ₂ M hM
  let Z := fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)
  have hData : IsReflectionData P γ α₁ (B α₁) Z := hB α₁ hαhi
  have hiZ : IndepFun (originRadialPath Xc) Z P :=
    lateralProjectedGMC_indep P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  obtain ⟨hν, hreflect, hκ, hκ1, houter, hα2, hαup, hβ, hν2, hfirst⟩ :=
    dual_window_margins γ α₁ η ξ hγ hγ₂ hη hη₂ hξ₂ hαlo hαhi hslack₁ hslack₂
  have hshift := (dual_window_reflected_triple γ α₁ α₂ α₃ η hγ hγ₂ hη₂ hαlo
    hαhi hα₂ hα₃ hs).1
  have hfirst' : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2 := by linarith only [hfirst]
  refine ⟨B, Z, hSource, hData, ?_⟩
  exact dual_source_full_inverse_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc hm hcont
    α₁ α₂ α₃ ξ hαhi hreflect hα₂ hα₃ hs hshift hfirst' hξ hξ₂
    (sub_pos.mp hβ) hslack₁ houter (B α₁) Z hData hiZ (Filter.Eventually.of_forall (fun _ => rfl))

end DOZZ.Proofs
