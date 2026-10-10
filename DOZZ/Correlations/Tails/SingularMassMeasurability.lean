/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.LocalSingularMass
public import DOZZ.Brownian.Lateral.RadialProjection

/-! Measurability of the literal extended-real singular insertion mass. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem localSingularMass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (F : ℂ → ℝ) (hF : Measurable F) (z : ℂ) (α : ℝ) :
    AEMeasurable (localSingularMass M F z γ α) P := by
  classical
  have hf : Measurable (fun x : ℂ => if x ∈ Metric.ball z 1 then
      ENNReal.ofReal (F x) * (ENNReal.ofReal ‖x-z‖).rpow (-γ*α) else 0) := by
    apply Measurable.ite Metric.isOpen_ball.measurableSet
    · exact (ENNReal.measurable_ofReal.comp hF).mul
        (ENNReal.continuous_rpow_const.measurable.comp
          (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable (fun x : ℂ => ‖x-z‖))))
    · exact measurable_const
  exact (Measure.measurable_lintegral hf).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)


end DOZZ.Proofs
