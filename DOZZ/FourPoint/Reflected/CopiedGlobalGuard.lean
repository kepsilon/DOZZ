/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalCompactMass
public import DOZZ.FourPoint.Reflected.SourceSpatialLimit
/-! The genuine radial reinsertion law transfers the actual exterior guard moments. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The global carrier's proved full observable law transports the source guard bound
`reflected_spatial_guard_inverse_finite` to the iterated conditional model. No copied
negative-moment hypothesis is required. -/
theorem reflected_copied_global_guard_inverse_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (hlaw : ∀ (f : ℂ → ℝ≥0∞), Measurable f →
      ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (originRadialPath Xc ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) ∂P) =
      ∫⁻ ω, G (originRadialPath Xc ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ
          (originRadialPath Xc ω.1) x) ∂N ω.2) ∂P.prod P)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫⁻ a, ∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω)^(-q)
      ∂P ∂P.map (originRadialPath Xc)) < ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  let D := Metric.closedBall (3 : ℂ) (1/8)
  let k : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)
  have hk : Measurable k := (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hD : MeasurableSet D := measurableSet_closedBall
  have hD0 : D ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hx0
    subst x
    norm_num [D, Metric.mem_closedBall, dist_eq_norm] at hx
  have he (μ : Measure ℂ) : (∫⁻ x in ({0} : Set ℂ)ᶜ, D.indicator k x ∂μ) =
      ∫⁻ x in D, k x ∂μ := by
    rw [setLIntegral_indicator hD, inter_eq_left.mpr hD0]
  have hw (a : TwoSidedPath) (μ : Measure ℂ) :
      (∫⁻ x in ({0} : Set ℂ)ᶜ, D.indicator k x*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ) =
      ∫⁻ x in D, k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ := by
    have hp : (fun x => D.indicator k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) =
        D.indicator (fun x => k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) := by
      funext x
      by_cases hx : x ∈ D <;> simp [hx]
    rw [hp, setLIntegral_indicator hD, inter_eq_left.mpr hD0]
  have hL := hlaw (D.indicator k) (hk.indicator hD)
    (fun p => p.2^(-q)) (measurable_snd.pow_const (-q))
  have hI := reflected_global_mass_iterated P (originRadialPath Xc)
    (originRadialPath_aemeasurable P X Xc hc hcont) γ N hN hfin
    (D.indicator k) (hk.indicator hD) (-q)
  simp only [he, hw] at hL hI
  rw [← hI, ← hL]
  exact reflected_spatial_guard_inverse_finite P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq z hz

end DOZZ.Proofs
