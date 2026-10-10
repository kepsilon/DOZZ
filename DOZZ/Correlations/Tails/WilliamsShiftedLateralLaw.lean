/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.MaximumShiftLateralLaw
public import DOZZ.Correlations.Tails.WilliamsAuxiliaryLaw

/-! The full Williams product law after shifting the lateral chaos to the maximum. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The marked Williams paths and the lateral chaos centered at the actual maximum have
the product law of an exponential level, two independent conditioned copies (the past
truncated at its last exit from that level), and the original lateral law. -/
theorem williams_shifted_lateral_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → BrownianPath)
    (hD : AEMeasurable D P) (hB : IsBrownianReal (fun t p => p t) (P.map D))
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun D Z P) (ν : ℝ) (hν : 0 < ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) :
    P.map (fun ω => (williamsReversedMark ν (D ω),
      (Z ω).map (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ)))) =
      ((((brownianMaximumReferenceLaw ν).prod Qν).map
        (fun v => (v.1, negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
          (P.map Z) := by
  let : IsProbabilityMeasure P := hZ.2.2.1
  let Y := fun ω => (Z ω).map
    (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ))
  obtain ⟨hY, hYlaw, hDY⟩ := maximum_shift_lateral_law P D hD hB γ Z hZ hInd ν hν
  have hW := williamsReversedMark_aemeasurable (P.map D) hB ν hν
  have hWD : AEMeasurable ((williamsReversedMark ν) ∘ D) P := hW.comp_aemeasurable hD
  have hWY : IndepFun ((williamsReversedMark ν) ∘ D) Y P :=
    hDY.comp₀ hD hY hW measurable_id.aemeasurable
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hWD hY).mp hWY
  change P.map (fun ω => (williamsReversedMark ν (D ω), Y ω)) =
    (P.map ((williamsReversedMark ν) ∘ D)).prod (P.map Y) at hmap
  rw [hmap, hYlaw, ← AEMeasurable.map_map_of_aemeasurable hW hD]
  have hlaw := williams_reversed_joint_law (P.map D) hB ν hν Qν hQν
  change (P.map D).map (williamsReversedMark ν) = _ at hlaw
  rw [hlaw]


end DOZZ.Proofs
