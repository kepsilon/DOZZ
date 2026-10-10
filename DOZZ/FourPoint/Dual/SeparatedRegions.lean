/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SeparatedRegions
public import DOZZ.FourPoint.Dual.SourceFullComparison
import Mathlib.Tactic
/-! Literal separated inner and outer regions for conditional lateral comparison. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The full source comparison on the literal separated disk and exterior has an explicit
factor tending to one with their relative radius. -/
theorem dual_source_separated_regions_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (hr1 : r ≤ 1) (hsep : s/r ≤ 1/2)
    (q : ℝ) (hq : 0 < q) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity
        (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      let J := fun (U : Set ℂ) (p : TwoSidedPath × Ω) => ∫⁻ x in U,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
      let original := ∫⁻ ω,
        ((∫⁻ x in reflected_innerRegion s, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)+
         (∫⁻ x in reflected_outerRegion r, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω))^(-q) ∂P
      let copied := ∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J (reflected_innerRegion s) (p.1, p.2.1)+J (reflected_outerRegion r) (p.1, p.2.2))^(-q) ∂(P.map (originRadialPath Xc)).prod (P.prod P)
      let m := ENNReal.ofReal (Real.exp (γ^2*(3*(s/r))/2*(q^2+q)))
      original ≤ m*copied ∧ copied ≤ m*original := by
  obtain ⟨hU₀, hU₁, hroot₀, hroot₁, hpart₀, hpart₁, hn₀, hn₁, hD⟩ :=
    reflected_separated_region_geometry s r hs hr hr1 hsep
  have hb := dual_source_full_lateral_comparison P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    α₁ α₂ α₃ z hz (reflected_innerRegion s) (reflected_outerRegion r)
    hU₀ hU₁ hroot₀ hroot₁ (Metric.ball 0 r) Metric.isOpen_ball.measurableSet hpart₀ hpart₁
    (s/r) r (s/r) (div_pos hs hr).le hsep hr (div_pos hs hr) hn₀ hn₁ hD q hq
  have he : 2*(s/r)+s/r = 3*(s/r) := by ring
  simpa only [he] using hb

end DOZZ.Proofs
