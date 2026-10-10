/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.ConstantCarrier
public import DOZZ.FourPoint.Dual.SourceCopiedOuterLaw
import Mathlib.Tactic
/-! A single copied carrier preserves the entire radial path and the actual fusion error. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The supplied chaos admits independent lateral copies whose actual signed separated-mass
error is little-o at every exponent below `ξ`. Their radial removal and independence are
proved on the same eventual family of source carriers. The joint law retains the full
radial path, including the future increment and terminal likelihood simultaneously. -/
theorem dual_full_copied_path_law_carrier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun v : ℂ × ℝ => Xc ω v.1 v.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q h ξ κ : ℝ) (hq : 0 < q)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ*α₁ < 4) (hslack : κ < (1-ξ)*(4-γ*α₁)) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : κ < ξ) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      (∀ β₁ β₂ β₃ ξ' : ℝ, ∀ z : ℂ, ‖z‖ < ‖z‖^(1-ξ') →
        P.map (fun ω => (originRadialPath Xc ω,
          dualOuterMass γ β₁ β₂ β₃ (M ω) z ξ')) =
          (P.prod P).map (fun ω : Ω × Ω =>
            (originRadialPath Xc ω.1,
              ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ')),
                ENNReal.ofReal (dualFusionKernel γ β₁ β₂ β₃ z x)*
                  ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x)
                    ∂N ω.2))) ∧
      Tendsto (fun z : ℂ =>
        ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P).toReal-
         (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal)/‖z‖^κ)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hNm, hi, hfin, heq, hlaw⟩ := dual_source_copied_outer_joint_law
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  obtain ⟨N₀, _, _, _, heq₀, ht⟩ := dual_full_copied_constant_carrier
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM α₁ α₂ α₃ q h ξ κ
      hq hα₁ hα₂ hα₃ hβ hslack hξ hξ1 hκ
  refine ⟨N, hNm, hi, hfin, heq, hlaw, ?_⟩
  have hAr := originRadialPath_aemeasurable P X Xc hc hcont
  apply ht.congr
  intro z
  have he := dual_copied_inverse_moment_congr P Xc hAr N₀ N
    (heq₀.trans heq.symm) γ α₁ α₂ α₃ q z (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))
  rw [he]

end DOZZ.Proofs
