/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.PlaneMassCode
public import DOZZ.FourPoint.Reflected.PastPlaneWeight
public import DOZZ.FourPoint.Reflected.SeparatedRegions
/-! A measurable retained outer mass on the complete stopped-past carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

noncomputable def reflectedPastOuterMassCode (γ α₁ α₂ α₃ r : ℝ) (z : ℂ)
    (p : (BrownianPath × BrownianPath) × Measure ℂ) : ℝ≥0∞ :=
  reflectedPuncturedMassCode (fun q : (BrownianPath × BrownianPath) × ℂ =>
    (reflected_outerRegion r).indicator (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflectedPastPlaneWeight γ q.1 x)) q.2) p

theorem reflected_pastOuterMassCode_measurable (γ α₁ α₂ α₃ r : ℝ) (z : ℂ) :
    Measurable (reflectedPastOuterMassCode γ α₁ α₂ α₃ r z) := by
  apply reflected_puncturedMassCode_measurable
  have hU : MeasurableSet (reflected_outerRegion r) :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_insert.mpr (measurableSet_singleton (1 : ℂ)) : MeasurableSet ({0,1} : Set ℂ)).compl
  have hF := ((reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).comp measurable_snd).ennreal_ofReal.mul
    (reflected_pastPlaneWeight_measurable γ).ennreal_ofReal
  exact Measurable.ite (hU.preimage measurable_snd) hF measurable_const

/-- On the retained exterior, stopping the inward path at the restart leaves its mass
unchanged, including the complete exterior half of the radial path. -/
theorem reflected_pastOuterMassCode_eq (γ α₁ α₂ α₃ r : ℝ) (z : ℂ) (a : TwoSidedPath)
    (T : ℝ≥0) (μ : Measure ℂ) (hr : 0 < r) (hT : Real.exp (-(T : ℝ)) ≤ r)
    (hfin : ∀ K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → μ K < ⊤) :
    reflectedPastOuterMassCode γ α₁ α₂ α₃ r z
      ((stopBrownianPath (radialPositiveHalf a) T,radialNegativeHalf a),μ) =
      ∫⁻ x in reflected_outerRegion r, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ := by
  have hU : MeasurableSet (reflected_outerRegion r) :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_insert.mpr (measurableSet_singleton (1 : ℂ)) : MeasurableSet ({0,1} : Set ℂ)).compl
  have hU0 : reflected_outerRegion r ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    have hn : 0 < ‖x‖ := hr.trans hx.1
    simpa only [mem_compl_iff,mem_singleton_iff] using norm_pos_iff.mp hn
  rw [reflectedPastOuterMassCode,reflected_puncturedMassCode_eq _ _ _ hfin]
  dsimp only [Prod.fst,Prod.snd]
  rw [setLIntegral_indicator hU,inter_eq_left.mpr hU0]
  apply setLIntegral_congr_fun hU
  intro x hx
  have hl := Real.log_le_log (Real.exp_pos (-(T : ℝ))) (hT.trans hx.1.le)
  rw [Real.log_exp] at hl
  beta_reduce
  rw [reflected_pastPlaneWeight_eq γ a T x (by linarith only [hl])]

end DOZZ.Proofs
