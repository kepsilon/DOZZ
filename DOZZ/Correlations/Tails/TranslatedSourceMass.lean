/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TranslatedField
public import DOZZ.Correlations.Tails.TranslatedSingularMass
public import DOZZ.Brownian.Lateral.GlobalIndependence

/-! Literal singular masses and the source lateral projection for the realized translated field. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem localSingularMass_restrict_ball
    {Ω : Type*} (M : Ω → Measure ℂ) (F : ℂ → ℝ) (z : ℂ) (γ α : ℝ) (ω : Ω) :
    localSingularMass (fun ω => (M ω).restrict (Metric.ball z 1)) F z γ α ω =
      localSingularMass M F z γ α ω := by
  classical
  change (∫⁻ x, (Metric.ball z 1).indicator
      (fun x => ENNReal.ofReal (F x) * (ENNReal.ofReal ‖x-z‖).rpow (-γ*α)) x
        ∂(M ω).restrict (Metric.ball z 1)) =
    ∫⁻ x, (Metric.ball z 1).indicator
      (fun x => ENNReal.ofReal (F x) * (ENNReal.ofReal ‖x-z‖).rpow (-γ*α)) x ∂M ω
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet,
    lintegral_indicator Metric.isOpen_ball.measurableSet,
    Measure.restrict_restrict Metric.isOpen_ball.measurableSet, inter_self]

/-- The full translated equator GMC gives exactly the transported singular mass. -/
theorem translated_source_singular_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (F : ℂ → ℝ) (hF : Measurable F) (hF0 : ∀ w, 0 ≤ F w) :
    ∀ᵐ ω ∂P, localSingularMass N
      (fun x => F (z+x) * Real.exp (-(γ ^ 2 + 4) * Real.log (normPlus (z+x))))
      0 γ α ω = ENNReal.ofReal (Real.exp (-γ * Xc ω z 0)) *
        localSingularMass M F z γ α ω := by
  filter_upwards [translated_source_gmc_restriction P X Xc hX hc z hz γ hγ hγ2 M hM N hN]
    with ω hω
  rw [← localSingularMass_restrict_ball N _ 0 γ α ω]
  change (∫⁻ x, _ ∂(N ω).restrict (Metric.ball 0 1)) = _
  rw [hω]
  exact transferred_singular_mass M F hF hF0 z γ α (Xc ω z 0) ω



end DOZZ.Proofs
