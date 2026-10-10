/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceBufferRate
public import DOZZ.FourPoint.Reflected.Decorrelation
/-! The actual error from the full source moment to the copied moment combines the buffer and
decorrelation rates. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_source_full_copied_littleO
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (hwhole : ∀ (f : ℂ → ℝ≥0∞), Measurable f →
      ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (originRadialPath Xc ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) ∂P) =
      ∫⁻ ω, G (originRadialPath Xc ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ
          (originRadialPath Xc ω.1) x) ∂N ω.2) ∂P.prod P)
    (hNa : ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
      (fun ω => (N ω).restrict (originLateralChart ρ)))
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hreflect : Q γ-α₁ < γ/2) (hs : 2*Q γ+γ/2 < α₁+α₂+α₃)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hnear : γ*(Q γ-α₁) < ξ)
    (hfreeze : γ*(Q γ-α₁) < (1-ξ)*(γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2)) (hh : 0 ≤ h) :
    let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
    IsComplexLittleOAtZero (γ*(Q γ-α₁)) (fun z : ℂ =>
      ((gammaHalfMoment P M γ α₁ α₂ α₃ p z-
        (reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) p).toReal : ℝ) : ℂ)) := by
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  obtain ⟨_,_,herror⟩ := reflected_source_decorrelation_error_on_carrier
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM N hN hfin hwhole hNa
    α₁ α₂ α₃ p ξ (γ*(Q γ-α₁)) hp hξ hξ1 hnear
  have hb := reflected_source_buffer_inverse_littleO P X M γ α₁ α₂ α₃ ξ h
    hγ hγ₂ hα₁ hα₂ hα₃ hreflect hs hξ hξ1 hnear hfreeze hh hX hM
  have he := DOZZ.Proofs.IsComplexLittleOAtZero.add hb (herror h hh).2
  convert he using 1
  funext z
  simp only [Complex.ofReal_sub]
  ring

end DOZZ.Proofs
