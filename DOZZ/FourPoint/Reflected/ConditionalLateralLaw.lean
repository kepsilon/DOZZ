/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.LateralCompactComparison
public import DOZZ.Brownian.Lateral.CircleRegularization
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! # Actual radial conditioning at all lateral cutoff coordinates -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Conditioning on the entire source radial path retains the same independent lateral cutoff
law. This is a joint-law identity, valid for every measurable nonnegative observable. -/
theorem reflected_lateral_cutoff_radial_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : TwoSidedPath × C(OriginLateralCutoffDomain ρ, ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (originRadialPath Xc ω, originLateralCutoffPath Xc ρ ω) ∂P) =
      ∫⁻ a, ∫⁻ y, F (a, y) ∂P.map (originLateralCutoffPath Xc ρ)
        ∂P.map (originRadialPath Xc) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hY := originLateralCutoffPath_aemeasurable P Xc hm hcont ρ hρ
  have hi := originRadialPath_lateralCutoffPath_indepFun P X Xc hX hc hm hcont ρ hρ
  have hj : P.map (fun ω => (originRadialPath Xc ω, originLateralCutoffPath Xc ρ ω)) =
      (P.map (originRadialPath Xc)).prod (P.map (originLateralCutoffPath Xc ρ)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hA hY).mp hi
  calc
    (∫⁻ ω, F (originRadialPath Xc ω, originLateralCutoffPath Xc ρ ω) ∂P) =
        ∫⁻ p, F p ∂P.map (fun ω => (originRadialPath Xc ω, originLateralCutoffPath Xc ρ ω)) :=
      (lintegral_map' hF.aemeasurable (hA.prodMk hY)).symm
    _ = ∫⁻ p, F p ∂(P.map (originRadialPath Xc)).prod
        (P.map (originLateralCutoffPath Xc ρ)) := by rw [hj]
    _ = _ := lintegral_prod _ hF.aemeasurable

end DOZZ.Proofs
