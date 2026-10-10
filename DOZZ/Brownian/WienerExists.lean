/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.Assembly
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import DOZZ.GFFStructure.CircleCovariance
public import DOZZ.Brownian.Barrier.ZeroDrift
public import DOZZ.Brownian.RogersPitmanInput

/-!
# A Wiener path law from the concrete equator GFF

The concrete scale-space white noise carries the equator GFF. Its continuous circle averages at
the origin give a real Brownian motion, which is pushed onto the continuous-path carrier
`BrownianPath`. The product of three copies supplies the independent coordinates for the
Rogers--Pitman map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The concrete equator GFF supplies an unconditional Wiener probability law on paths. -/
theorem exists_wienerPathMeasure :
    ∃ W : Measure BrownianPath, IsProbabilityMeasure W ∧
      IsBrownianReal (fun (t : ℝ≥0) (p : BrownianPath) => p t) W := by
  let P := GaussianFields.scaleSpaceWhiteNoiseMeasure 2
  have hX := isEquatorGFF_equatorGFFDistribution
  let _ := hX.1
  obtain ⟨Xc, hc⟩ := exists_equatorGFF_circle_average_witness equatorGFFDistribution hX
  obtain ⟨Y, hY, _, hYcont, _⟩ :=
    exists_continuous_circleAverage P equatorGFFDistribution Xc hX hc
  have hB := (circleAverage_origin_brownian P equatorGFFDistribution Y hX hY hYcont).1
  let B := fun (t : ℝ≥0) ω => Y ω 0 (t : ℝ)
  have hBm : AEMeasurable (brownianContinuousPath B) P :=
    aemeasurable_brownianContinuousPath hB
  refine ⟨P.map (brownianContinuousPath B),
    (Measure.isProbabilityMeasure_map_iff hBm).mpr inferInstance, ?_⟩
  exact brownianContinuousPath_isBrownian hB

/-- A fixed representative of the proved Wiener path law. -/
noncomputable def wienerPathMeasure : Measure BrownianPath :=
  Classical.choose exists_wienerPathMeasure

instance isProbabilityMeasure_wienerPathMeasure : IsProbabilityMeasure wienerPathMeasure :=
  (Classical.choose_spec exists_wienerPathMeasure).1

/-- The canonical path evaluations under the chosen Wiener law are Brownian. -/
theorem wienerPathMeasure_isBrownian :
    IsBrownianReal (fun (t : ℝ≥0) (p : BrownianPath) => p t) wienerPathMeasure :=
  (Classical.choose_spec exists_wienerPathMeasure).2

/-- The three-coordinate probability space for the unconditional radial construction. -/
noncomputable def wienerTripleMeasure : Measure BrownianTriple :=
  brownianTripleMeasure wienerPathMeasure

instance isProbabilityMeasure_wienerTripleMeasure : IsProbabilityMeasure wienerTripleMeasure :=
  inferInstanceAs (IsProbabilityMeasure (brownianTripleMeasure wienerPathMeasure))

/-- Each of the three coordinate processes is a continuous real Brownian motion. -/
theorem wienerTriple_coordinate_isBrownian (i : Fin 3) :
    IsBrownianReal (fun (t : ℝ≥0) (V : BrownianTriple) => (V i) t) wienerTripleMeasure :=
  brownianTriple_coordinate_isBrownian wienerPathMeasure wienerPathMeasure_isBrownian i

/-- The coordinate paths are mutually independent as whole random continuous paths. -/
theorem wienerTriple_coordinatePaths_independent :
    iIndepFun (fun i : Fin 3 => fun V : BrownianTriple => V i) wienerTripleMeasure :=
  brownianTriple_coordinatePaths_independent wienerPathMeasure

/-- The three canonical path coordinates have precisely the chosen Wiener marginal law. -/
theorem wienerTriple_coordinatePath_hasLaw (i : Fin 3) :
    HasLaw (fun V : BrownianTriple => V i) wienerPathMeasure wienerTripleMeasure :=
  brownianTriple_coordinatePath_hasLaw wienerPathMeasure i

/-- All three coordinates start from zero on a single full-probability event. -/
theorem wienerTriple_zero_ae :
    ∀ᵐ V ∂wienerTripleMeasure, ∀ i : Fin 3, V i 0 = 0 := by
  apply ae_all_iff.mpr
  intro i
  exact (wienerTriple_coordinate_isBrownian i).eval_zero_ae_eq_zero

/-- Applying the radial map now gives an unconditional continuous-path probability candidate.
Its entrance FDD characterization is a separate analytic identification. -/
noncomputable def rogersPitmanWienerMeasure (μ : ℝ) : Measure BrownianPath :=
  rogersPitmanEntranceMeasure μ wienerPathMeasure

instance isProbabilityMeasure_rogersPitmanWienerMeasure (μ : ℝ) :
    IsProbabilityMeasure (rogersPitmanWienerMeasure μ) :=
  inferInstanceAs (IsProbabilityMeasure (rogersPitmanEntranceMeasure μ wienerPathMeasure))

/-- Reflection of the unconditional radial construction. -/
noncomputable def negativeRogersPitmanWienerMeasure (μ : ℝ) : Measure BrownianPath :=
  negativeRogersPitmanEntranceMeasure μ wienerPathMeasure

instance isProbabilityMeasure_negativeRogersPitmanWienerMeasure (μ : ℝ) :
    IsProbabilityMeasure (negativeRogersPitmanWienerMeasure μ) :=
  inferInstanceAs
    (IsProbabilityMeasure (negativeRogersPitmanEntranceMeasure μ wienerPathMeasure))

/-- The actual radial path candidate starts at zero. -/
theorem rogersPitmanWienerMeasure_zero_ae (μ : ℝ) :
    ∀ᵐ p ∂rogersPitmanWienerMeasure μ, p 0 = 0 := by
  apply (ae_map_iff (measurable_rogersPitmanPath μ).aemeasurable
    ((measurableSet_singleton (0 : ℝ)).preimage (ContinuousMap.measurable_eval 0))).mpr
  exact wienerTriple_zero_ae.mono fun V hV => rogersPitmanPath_zero μ V hV

/-- The reflected radial candidate starts at the same singular entrance point. -/
theorem negativeRogersPitmanWienerMeasure_zero_ae (μ : ℝ) :
    ∀ᵐ p ∂negativeRogersPitmanWienerMeasure μ, p 0 = 0 := by
  apply (ae_map_iff (measurable_negativeRogersPitmanPath μ).aemeasurable
    ((measurableSet_singleton (0 : ℝ)).preimage (ContinuousMap.measurable_eval 0))).mpr
  exact wienerTriple_zero_ae.mono fun V hV => negativeRogersPitmanPath_zero μ V hV

/-- Fixed-time coordinate evaluations have the product of three centered Gaussian laws. -/
theorem wienerTriple_eval_hasLaw (t : ℝ≥0) :
    HasLaw (fun V : BrownianTriple => fun i : Fin 3 => V i t)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)) wienerTripleMeasure := by
  have hindep := wienerTriple_coordinatePaths_independent.comp
    (fun _ p => p t) (fun _ => ContinuousMap.measurable_eval t)
  exact hindep.hasLaw_pi (fun i => (wienerTriple_coordinate_isBrownian i).hasLaw_eval t)

/-- The drifted Gaussian coordinates at a fixed time remain mutually independent. -/
theorem wienerTriple_drifted_eval_hasLaw (a : ℝ) (t : ℝ≥0) :
    HasLaw (fun V : BrownianTriple => fun i : Fin 3 =>
      V i t + (if i = 0 then a * (t : ℝ) else 0))
      (Measure.pi (fun i : Fin 3 => gaussianReal (if i = 0 then a * (t : ℝ) else 0) t))
      wienerTripleMeasure := by
  have hindep := wienerTriple_coordinatePaths_independent.comp
    (fun i p => p t + (if i = 0 then a * (t : ℝ) else 0))
    (fun _ => (ContinuousMap.measurable_eval t).add_const _)
  apply hindep.hasLaw_pi
  intro i
  simpa only [zero_add, Function.comp_def] using gaussianReal_add_const
    ((wienerTriple_coordinate_isBrownian i).hasLaw_eval t)
    (if i = 0 then a * (t : ℝ) else 0)


/-- The unconditional radial evaluation has an explicit Gaussian-norm pushforward law.
Identifying this pushforward with the entrance density is the analytic spherical-integration step. -/
theorem rogersPitmanWienerMeasure_eval_map (a : ℝ) (t : ℝ≥0) :
    (rogersPitmanWienerMeasure a).map (fun p => p t) =
      (Measure.pi (fun i : Fin 3 => gaussianReal
        (if i = 0 then a * (t : ℝ) else 0) t)).map
          (fun z => ‖WithLp.toLp 2 z‖) := by
  rw [rogersPitmanWienerMeasure, rogersPitmanEntranceMeasure,
    Measure.map_map (ContinuousMap.measurable_eval t) (measurable_rogersPitmanPath a)]
  have hnorm : Measurable (fun z : Fin 3 → ℝ => ‖WithLp.toLp 2 z‖) :=
    (PiLp.continuous_toLp 2 _).norm.measurable
  have hmap := (wienerTriple_drifted_eval_hasLaw a t).map_eq
  have hinput : Measurable (fun V : BrownianTriple => fun i : Fin 3 =>
      V i t + (if i = 0 then a * (t : ℝ) else 0)) :=
    measurable_pi_iff.mpr fun i =>
      ((ContinuousMap.measurable_eval t).comp (measurable_pi_apply i)).add_const _
  calc
    _ = (wienerTripleMeasure.map (fun V => fun i =>
        V i t + (if i = 0 then a * (t : ℝ) else 0))).map
          (fun z => ‖WithLp.toLp 2 z‖) := by
      symm
      exact Measure.map_map hnorm
        hinput
    _ = _ := by rw [hmap]

end DOZZ.Proofs
