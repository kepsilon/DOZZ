/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.UnpinnedMeasureIdentification
public import DOZZ.Statements.Correlations.LocalSingularMass

/-! Exact translated singular-mass identity, including the Gaussian pin and reference weight. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Pin removal transports the literal singular mass, including its infinite value at the center. -/
theorem transferred_singular_mass
    {Ω : Type*} (M : Ω → Measure ℂ) (F : ℂ → ℝ) (hF : Measurable F)
    (hF0 : ∀ w, 0 ≤ F w) (z : ℂ) (γ α N : ℝ) (ω : Ω) :
    localSingularMass (fun ω => transferredMeasure (M ω) z γ N)
      (fun x => F (z+x) * Real.exp (-(γ ^ 2 + 4) * Real.log (normPlus (z+x))))
      0 γ α ω = ENNReal.ofReal (Real.exp (-γ * N)) * localSingularMass M F z γ α ω := by
  classical
  let H : ℂ → ℝ≥0∞ := fun x => if x ∈ Metric.ball 0 1 then
    ENNReal.ofReal (F (z+x) * Real.exp (-(γ ^ 2 + 4) * Real.log (normPlus (z+x)))) *
      ENNReal.rpow (ENNReal.ofReal ‖x-0‖) (-γ * α) else 0
  have hH : Measurable H := by
    have hN : Measurable (fun x : ℂ => normPlus (z+x)) := by
      unfold normPlus
      fun_prop
    dsimp [H]
    exact Measurable.ite Metric.isOpen_ball.measurableSet
      ((ENNReal.measurable_ofReal.comp
        ((hF.comp (measurable_const.add measurable_id)).mul
          ((measurable_const.mul (Real.measurable_log.comp hN)).exp))).mul
        (ENNReal.continuous_rpow_const.measurable |>.comp (by fun_prop))) measurable_const
  have hd : Measurable (fun w : ℂ => ENNReal.ofReal
      (Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)))) := by
    unfold normPlus
    fun_prop
  have htrans : Measurable (fun w : ℂ => w-z) := by fun_prop
  have hHt : Measurable (fun w : ℂ => H (w-z)) := hH.comp htrans
  change (∫⁻ x, H x ∂transferredMeasure (M ω) z γ N) = _
  rw [transferredMeasure, lintegral_map hH htrans,
    lintegral_withDensity_eq_lintegral_mul _ hd hHt,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  rw [localSingularMass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ Metric.ball z 1
  · have hx : w-z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
    rw [Set.indicator_of_mem hw]
    simp only [Pi.mul_apply, H, ite_eq_left hx, ite_eq_left hw, sub_zero, add_sub_cancel]
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_mul (hF0 w)]
    have he : ENNReal.ofReal (Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) *
        ENNReal.ofReal (Real.exp (-(γ ^ 2 + 4) * Real.log (normPlus w))) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      have hz : (γ ^ 2 + 4) * Real.log (normPlus w) +
          -(γ ^ 2 + 4) * Real.log (normPlus w) = 0 := by ring
      rw [hz, Real.exp_zero, ENNReal.ofReal_one]
    calc
      _ = ENNReal.ofReal (Real.exp (-γ*N)) * ENNReal.ofReal (F w) *
          (ENNReal.ofReal (Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) *
            ENNReal.ofReal (Real.exp (-(γ ^ 2 + 4) * Real.log (normPlus w)))) *
          ENNReal.rpow (ENNReal.ofReal ‖w-z‖) (-γ*α) := by ring
      _ = _ := by rw [he, mul_one]; ring
  · rw [Set.indicator_of_notMem hw]
    simp only [ite_eq_right hw, mul_zero]

/-- The constructed translated unpinned GMC gives the same singular-mass identity almost surely. -/
theorem unpinned_singular_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ α : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (Metric.ball 0 1) (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ N)
    (F : ℂ → ℝ) (hF : Measurable F) (hF0 : ∀ w, 0 ≤ F w) :
    ∀ᵐ ω ∂P, localSingularMass N
      (fun x => F (z+x) * Real.exp (-(γ ^ 2 + 4) * Real.log (normPlus (z+x))))
      0 γ α ω = ENNReal.ofReal (Real.exp (-γ * Xc ω z 0)) * localSingularMass M F z γ α ω := by
  filter_upwards [unpinned_source_measure_identity P X Xc hX hc z hz γ M hM N hN]
    with ω hω
  change (∫⁻ x, _ ∂N ω) = _
  rw [hω]
  exact transferred_singular_mass M F hF hF0 z γ α (Xc ω z 0) ω


end DOZZ.Proofs
