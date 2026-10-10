/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.DecorrelationCarrier
public import DOZZ.FourPoint.Reflected.ComparisonError
public import DOZZ.FourPoint.Reflected.OuterInverseGuard
import Mathlib.Tactic
/-! Signed decorrelation error for the literal separated source and copied masses. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Inverse moment of the sum of the literal inner and exterior source masses. -/
noncomputable def reflected_source_separatedMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (s r q : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ x in reflected_innerRegion s,
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)+
    (∫⁻ x in reflected_outerRegion r,
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω))^(-q) ∂P

/-- The same moment with two independent lateral copies and one common radial path. -/
noncomputable def reflected_copied_separatedMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (N : Ω → Measure ℂ)
    (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (s r q : ℝ) : ℝ≥0∞ :=
  let J := fun (U : Set ℂ) (p : TwoSidedPath × Ω) => ∫⁻ x in U,
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
  ∫⁻ p : TwoSidedPath × (Ω × Ω),
    (J (reflected_innerRegion s) (p.1,p.2.1)+
     J (reflected_outerRegion r) (p.1,p.2.2))^(-q)
    ∂(P.map (originRadialPath Xc)).prod (P.prod P)

/-- A specified actual source carrier gives a uniform finite error bound. No copied moment
bound is assumed: the copied moment's finiteness follows from the source comparison. -/
theorem reflected_source_separated_moment_error
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
    (α₁ α₂ α₃ q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ s : ℝ),
      ‖z‖ ≤ 1 → ‖z‖ < ‖z‖^(1-ξ) →
      0 < ‖z‖^(1-ξ) → ‖z‖^(1-ξ) ≤ 1 →
      0 < s → s/‖z‖^(1-ξ) ≤ 1/2 →
      let original := reflected_source_separatedMoment P M γ α₁ α₂ α₃ z s (‖z‖^(1-ξ)) q
      let copied := reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z s (‖z‖^(1-ξ)) q
      let m := Real.exp (γ^2*(3*(s/‖z‖^(1-ξ)))/2*(q^2+q))
      original ≠ ⊤ ∧ copied ≠ ⊤ ∧
        |original.toReal-copied.toReal| ≤ (m-1)*m*C := by
  obtain ⟨C,hC,hCbound⟩ := reflected_outerMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq.le
  refine ⟨C,hC,?_⟩
  intro z ξ s hz hzsep hr hr1 hs hsep
  let r := ‖z‖^(1-ξ)
  obtain ⟨hU₀,hU₁,hroot₀,hroot₁,hpart₀,hpart₁,hn₀,hn₁,hD⟩ :=
    reflected_separated_region_geometry s r hs hr hr1 hsep
  have hb := reflected_source_full_lateral_comparison_on_carrier
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM N hN hfin hwhole hNa
    α₁ α₂ α₃ z hz (reflected_innerRegion s) (reflected_outerRegion r)
    hU₀ hU₁ hroot₀ hroot₁ (Metric.ball 0 r) Metric.isOpen_ball.measurableSet
    hpart₀ hpart₁ (s/r) r (s/r) (div_pos hs hr).le hsep hr (div_pos hs hr)
    hn₀ hn₁ hD q hq
  have he : 2*(s/r)+s/r = 3*(s/r) := by ring
  simp only [he] at hb
  let original := reflected_source_separatedMoment P M γ α₁ α₂ α₃ z s r q
  let copied := reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z s r q
  let m := Real.exp (γ^2*(3*(s/r))/2*(q^2+q))
  change original ≤ ENNReal.ofReal m*copied ∧ copied ≤ ENNReal.ofReal m*original at hb
  have ho : original ≤ ENNReal.ofReal C := by
    calc
      _ ≤ ∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [reflected_source_outerMass_eq_comparison_region
          P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ ξ z hzsep] with ω hω
        rw [hω]
        exact ennreal_rpow_antitone_of_nonpos (le_add_left le_rfl) (neg_nonpos.mpr hq.le)
      _ ≤ _ := hCbound z ξ hz hr1
  have hoFin : original ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ho
  have hm1 : 1 ≤ m := Real.one_le_exp (by
    exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg γ)
      (mul_nonneg (by norm_num) (div_pos hs hr).le)) (by norm_num))
      (add_nonneg (sq_nonneg q) hq.le))
  obtain ⟨hcFin,herr⟩ := reflected_moment_comparison_error original copied m hm1 hoFin hb.1 hb.2
  have hoReal : original.toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top ho
  refine ⟨hoFin,hcFin,herr.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hoReal (mul_nonneg (sub_nonneg.mpr hm1) (zero_le_one.trans hm1))

end DOZZ.Proofs
