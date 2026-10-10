/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.RadialWindowUniform
public import DOZZ.Brownian.Lateral.BrownianWindowExponential
public import DOZZ.Correlations.Tails.WilliamsPolarMassLaw
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.FourPoint.Reflected.MaximumParetoLaw

/-! Deterministic restart and Williams' law for the actual source lateral projection. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Restarting an actual continuous inward Brownian half preserves its full path law. -/
theorem reflected_restarted_radial_path_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → TwoSidedPath)
    (hA : AEMeasurable A P) (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (T : ℝ≥0) :
    P.map (fun ω => brownianShiftPath T (radialPositiveHalf (A ω))) =
      P.map (fun ω => radialPositiveHalf (A ω)) := by
  have hD := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hs : Measurable (brownianShiftPath T) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have he := (AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hD).symm.trans
    (brownianPath_deterministic_shift_map _
      (radialPositiveHalf_map_isBrownian P A hA hB) T)
  simpa only [Function.comp_def] using he

/-- The genuine restarted source path and source lateral projection obey the full Williams
polar-mass law. The maximum of that restarted path also has its exact Pareto law. -/
theorem reflected_source_restarted_williams_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ν : ℝ) (hν : 0 < ν) (Qν : Measure BrownianPath)
    (hQν : IsNegativeConditionedBrownianLaw ν Qν) (T : ℝ≥0) :
    ∃ A : Ω → TwoSidedPath,
      (∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
        ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) ∧
      AEMeasurable A P ∧
      let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
      let Z := fun ω => lateralProjectedGMC γ (A ω) (M ω)
      AEMeasurable D P ∧ IsBrownianReal (fun t p => p t) (P.map D) ∧
      IndepFun D Z P ∧
      P.map (fun ω => Real.exp (γ * driftedBrownianMaximum ν (D ω))) =
        paretoMeasure 1 (2 * ν / γ) ∧
      P.map (fun ω => ∫⁻ t, (if 0 < t then ENNReal.ofReal
        (Real.exp (γ * (D ω (Real.toNNReal t) - ν * t))) else 0) ∂Z ω) =
        (((((brownianMaximumReferenceLaw ν).prod Qν).map
          (fun v => (v.1, negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
            (P.map Z)).map (williamsMassFunctional γ) := by
  obtain ⟨A, hAc, hA, _, hB, _, _, hZ, hi, hlat⟩ :=
    DOZZ.equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ₂ hX hM
  let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
  let Z := fun ω => lateralProjectedGMC γ (A ω) (M ω)
  have hs : Measurable (fun a => brownianShiftPath T (radialPositiveHalf a)) :=
    continuous_brownianShiftPath.measurable.comp
      (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hD : AEMeasurable D P := hs.comp_aemeasurable hA
  have hlaw := reflected_restarted_radial_path_law P A hA hB T
  have hDb : IsBrownianReal (fun t p => p t) (P.map D) := by
    rw [show P.map D = P.map (fun ω => radialPositiveHalf (A ω)) from hlaw]
    exact radialPositiveHalf_map_isBrownian P A hA hB
  have hDZ : IndepFun D Z P := hi.comp₀ hA hZ hs.aemeasurable measurable_id.aemeasurable
  have hmax := reflected_brownian_maximum_pareto_law (P.map D) hDb γ ν hγ hν
  have hm := ((aemeasurable_driftedBrownianMaximum (P.map D) hDb ν hν).const_mul γ).exp
  have hmax' : P.map (fun ω => Real.exp (γ * driftedBrownianMaximum ν (D ω))) =
      paretoMeasure 1 (2 * ν / γ) := by
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable hm hD).symm.trans hmax
  exact ⟨A, hAc, hA, hD, hDb, hDZ, hmax',
    williams_polar_mass_law P D hD hDb γ Z hlat hDZ ν hν Qν hQν⟩

end DOZZ.Proofs
