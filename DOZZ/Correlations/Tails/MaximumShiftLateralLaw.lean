/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralTranslation
public import DOZZ.Brownian.Williams.MaximumGeometry

/-! Shifting the stationary lateral chaos to the actual Brownian maximum. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Translation to the maximum retains the lateral law and independence of the entire
Brownian path. The maximum time is only AE measurable; a measurable representative is used
in the random-translation theorem `DOZZ.lateralGMC_random_translation` and then replaced by the
literal time on one event. -/
theorem maximum_shift_lateral_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → BrownianPath)
    (hD : AEMeasurable D P) (hB : IsBrownianReal (fun t p => p t) (P.map D))
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun D Z P) (ν : ℝ) (hν : 0 < ν) :
    AEMeasurable (fun ω => (Z ω).map
      (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ))) P ∧
      P.map (fun ω => (Z ω).map
        (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ))) = P.map Z ∧
      IndepFun D (fun ω => (Z ω).map
        (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ))) P := by
  have ht : AEMeasurable (fun p : BrownianPath =>
      -(driftedBrownianMaximumTime ν p : ℝ)) (P.map D) :=
    (NNReal.continuous_coe.measurable.comp_aemeasurable
      (aemeasurable_driftedBrownianMaximumTime (P.map D) hB ν hν)).neg
  let T := ht.mk (fun p : BrownianPath => -(driftedBrownianMaximumTime ν p : ℝ))
  have hT : Measurable T := ht.measurable_mk
  have hshift : (fun ω => (Z ω).map
      (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ))) =ᵐ[P]
      (fun ω => (Z ω).map (fun s => s + T (D ω))) := by
    filter_upwards [ae_of_ae_map hD ht.ae_eq_mk] with ω hω
    change -(driftedBrownianMaximumTime ν (D ω) : ℝ) = T (D ω) at hω
    simp only [sub_eq_add_neg, ← hω]
  obtain ⟨hm, hlaw, hi⟩ := lateralGMC_random_translation P γ Z hZ D hD hInd T hT
  exact ⟨hm.congr hshift.symm, (Measure.map_congr hshift).trans hlaw,
    hi.congr (Filter.EventuallyEq.refl _ _) hshift.symm⟩


end DOZZ.Proofs
