/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.StoppedMassMeasurability
public import DOZZ.Correlations.Tails.WilliamsShiftedLateralLaw
public import DOZZ.Brownian.Lateral.IntervalMoments

/-! The exact exponential-maximum last-cut law for the canonical inward polar mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The measurable exponential-height times stopped reflection-mass functional. -/
noncomputable def williamsMassFunctional (γ : ℝ)
    (z : ((ℝ × StoppedBrownianPath) × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * z.1.1.1)) *
    stoppedReflectionMassCode γ ((z.1.1.2.1, (z.1.2,z.1.1.2.2)),z.2)

theorem measurable_williamsMassFunctional (γ : ℝ) :
    Measurable (williamsMassFunctional γ) := by
  apply ((measurable_fst.fst.fst.const_mul γ).exp.ennreal_ofReal).mul
  exact (measurable_stoppedReflectionMassCode γ).comp
    ((measurable_fst.fst.snd.fst.prodMk
      (measurable_fst.snd.prodMk measurable_fst.fst.snd.snd)).prodMk measurable_snd)

/-- On the conditioned-copy model the measurable functional is exactly `exp(γ m) J_m`,
with `J_m` the last-exit truncated reflection mass `DOZZ.twoSidedReflectionCutMass`. -/
theorem williamsMassFunctional_lastExit
    (γ m : ℝ) (qplus qminus : BrownianPath) (Z : Measure ℝ)
    (hfin : ∀ a b : ℝ, Z (Icc a b) < ⊤) :
    williamsMassFunctional γ
      (((m,negativeConditionedLastExitSegment m qminus),qplus),Z) =
        ENNReal.ofReal (Real.exp (γ*m)) * twoSidedReflectionCutMass γ m
          (fun _ : Unit => (qplus,qminus)) (fun _ : Unit => Z) () := by
  change ENNReal.ofReal (Real.exp (γ*m)) * stoppedReflectionMassCode γ
    ((negativeLastExitTime qminus m,
      (qplus,stopBrownianPath qminus (negativeLastExitTime qminus m))),Z) = _
  rw [stoppedReflectionMassCode_eq γ _ _ _ hfin,
    stopped_reflection_mass_lastExit]

/-- The inward polar mass has the exponential-level Williams law of its last-exit truncated
conditioned reflection mass. All integrals retain their extended-real values. -/
theorem williams_polar_mass_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → BrownianPath)
    (hD : AEMeasurable D P) (hB : IsBrownianReal (fun t p => p t) (P.map D))
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun D Z P) (ν : ℝ) (hν : 0 < ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) :
    P.map (fun ω => ∫⁻ t, (if 0 < t then ENNReal.ofReal
      (Real.exp (γ * (D ω (Real.toNNReal t) - ν * t))) else 0) ∂Z ω) =
      (((((brownianMaximumReferenceLaw ν).prod Qν).map
        (fun v => (v.1, negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
          (P.map Z)).map (williamsMassFunctional γ) := by
  let Y := fun ω => (Z ω).map
    (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ))
  have hY := (maximum_shift_lateral_law P D hD hB γ Z hZ hInd ν hν).1
  have hW := (williamsReversedMark_aemeasurable (P.map D) hB ν hν).comp_aemeasurable hD
  have hpair : AEMeasurable (fun ω => (williamsReversedMark ν (D ω),Y ω)) P :=
    hW.prodMk hY
  have heq : (fun ω => ∫⁻ t, (if 0 < t then ENNReal.ofReal
      (Real.exp (γ * (D ω (Real.toNNReal t) - ν * t))) else 0) ∂Z ω) =ᵐ[P]
      (fun ω => williamsMassFunctional γ (williamsReversedMark ν (D ω),Y ω)) := by
    filter_upwards [hZ.2.2.2.2.1, lateralGMC_singleton_ae P γ Z hZ 0] with ω hfin hzero
    have hYfin (a b : ℝ) : Y ω (Icc a b) < ⊤ := by
      have hm : Measurable (fun s : ℝ => s - (driftedBrownianMaximumTime ν (D ω) : ℝ)) := by fun_prop
      rw [show Y ω = (Z ω).map (fun s => s - (driftedBrownianMaximumTime ν (D ω) : ℝ)) from rfl,
        Measure.map_apply hm measurableSet_Icc]
      apply lt_of_le_of_lt (measure_mono ?_) (hfin
        (a + (driftedBrownianMaximumTime ν (D ω) : ℝ))
        (b + (driftedBrownianMaximumTime ν (D ω) : ℝ)))
      intro s hs
      change a ≤ s - (driftedBrownianMaximumTime ν (D ω) : ℝ) ∧
        s - (driftedBrownianMaximumTime ν (D ω) : ℝ) ≤ b at hs
      exact ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    rw [williams_polar_split γ ν (D ω) (Z ω) hzero]
    change _ = ENNReal.ofReal (Real.exp (γ * driftedBrownianMaximum ν (D ω))) *
      stoppedReflectionMassCode γ
        ((driftedBrownianMaximumTime ν (D ω),williamsSplitPaths ν (D ω)),Y ω)
    rw [stoppedReflectionMassCode_eq γ _ _ _ hYfin]
  rw [Measure.map_congr heq]
  change P.map ((williamsMassFunctional γ) ∘
    (fun ω => (williamsReversedMark ν (D ω),Y ω))) = _
  rw [← AEMeasurable.map_map_of_aemeasurable
    (measurable_williamsMassFunctional γ).aemeasurable hpair]
  have hlaw := williams_shifted_lateral_joint_law P D hD hB γ Z hZ hInd ν hν Qν hQν
  change P.map (fun ω => (williamsReversedMark ν (D ω),Y ω)) = _ at hlaw
  rw [hlaw]


end DOZZ.Proofs
