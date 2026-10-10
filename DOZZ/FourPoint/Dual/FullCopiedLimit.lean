/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.FullSeparatedLimit
import Mathlib.Tactic
/-! Actual lateral decoupling is negligible at the prescribed dual fusion exponent. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The supplied chaos admits independent lateral copies whose actual signed separated-mass
error is little-o at every exponent below `ξ`. Their radial removal and independence are
proved on the same eventual family of source carriers. -/
theorem dual_full_copied_inverse_littleO
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun v : ℂ × ℝ => Xc ω v.1 v.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q h ξ κ : ℝ) (hq : 0 < q)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ*α₁ < 4) (hslack : κ < (1-ξ)*(4-γ*α₁)) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : κ < ξ) :
    ∃ N : ℂ → Ω → Measure ℂ,
      (∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), Measurable (N z) ∧
        IndepFun (originRadialPath Xc) (N z) P ∧
        (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N z ω K < ⊤) ∧
        N z =ᵐ[P] (fun ω => (M ω).withDensity
          (lateralRadialWeight γ (originRadialPath Xc ω)))) ∧
      Tendsto (fun z : ℂ =>
        ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P).toReal-
         (dualCopiedSeparatedInverseMoment P Xc (N z) γ α₁ α₂ α₃ q z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal)/‖z‖^κ)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  obtain ⟨N, hN, hcopy⟩ := dual_source_decoupling_littleO P X Xc hX hc hm hcont
    γ hγ hγ₂ M hM α₁ α₂ α₃ q h ξ κ hq hξ hξ1 hκ
  have hfull := dual_full_separated_inverse_littleO P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q ξ κ h hq hα₁ hα₂ hα₃ hβ hξ hξ1 hslack
  refine ⟨N, hN, ?_⟩
  have ht := hfull.add hcopy
  simp only [zero_add] at ht
  apply ht.congr'
  exact Eventually.of_forall fun z => by dsimp only; ring

end DOZZ.Proofs
