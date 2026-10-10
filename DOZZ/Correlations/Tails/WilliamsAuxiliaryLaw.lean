/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsReversedPrefix
public import DOZZ.Brownian.Lateral.RadialWindowUniform

/-! Williams splitting retains the independent auxiliary chaos, including its complete law. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The maximum, reversed lifetime-marked prefix and conditioned future of one Brownian path. -/
noncomputable def williamsReversedMark (ν : ℝ) (p : BrownianPath) :
    (ℝ × StoppedBrownianPath) × BrownianPath :=
  (reverseMarkedSegment
    (driftedBrownianMaximum ν p, brownianPreMaximumSegment ν p),
      brownianPostMaximumPath ν p)

theorem williamsReversedMark_aemeasurable
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) : AEMeasurable (williamsReversedMark ν) P :=
  (measurable_reverseMarkedSegment.comp_aemeasurable
    ((aemeasurable_driftedBrownianMaximum P hB ν hν).prodMk
      (aemeasurable_brownianPreMaximumSegment P hB ν hν))).prodMk
        (aemeasurable_brownianPostMaximumPath P hB ν hν)

/-- The exponential maximum and two conditioned halves in Williams' split retain independence
from any auxiliary variable independent of the entire source radial path. The first conditioned
half is stopped at its last exit from the sampled level; no independence of that stopped half
from its lifetime or level is asserted. -/
theorem radial_williams_auxiliary_law
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (V : Ω → E) (hV : AEMeasurable V P) (hInd : IndepFun A V P)
    (ν : ℝ) (hν : 0 < ν) (Q : Measure BrownianPath)
    (hQ : IsNegativeConditionedBrownianLaw ν Q) :
    P.map (fun ω =>
      (williamsReversedMark ν (radialPositiveHalf (A ω)), V ω)) =
      ((((brownianMaximumReferenceLaw ν).prod Q).map
        (fun z => (z.1, negativeConditionedLastExitSegment z.1 z.2))).prod Q).prod
          (P.map V) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let D : Ω → BrownianPath := fun ω => radialPositiveHalf (A ω)
  have hD : AEMeasurable D P := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hDB := radialPositiveHalf_map_isBrownian P A hA hB
  have hW := williamsReversedMark_aemeasurable (P.map D) hDB ν hν
  have hDV : IndepFun D V P := hInd.comp continuous_radialPositiveHalf.measurable measurable_id
  have hWV : IndepFun ((williamsReversedMark ν) ∘ D) V P :=
    hDV.comp₀ hD hV hW measurable_id.aemeasurable
  have hWD : AEMeasurable ((williamsReversedMark ν) ∘ D) P := hW.comp_aemeasurable hD
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hWD hV).mp hWV
  change P.map (fun ω => (williamsReversedMark ν (radialPositiveHalf (A ω)), V ω)) =
    (P.map ((williamsReversedMark ν) ∘ D)).prod (P.map V) at hmap
  rw [hmap, ← AEMeasurable.map_map_of_aemeasurable hW hD]
  have hlaw := williams_reversed_joint_law (P.map D) hDB ν hν Q hQ
  change (P.map D).map (williamsReversedMark ν) = _ at hlaw
  rw [hlaw]


end DOZZ.Proofs
