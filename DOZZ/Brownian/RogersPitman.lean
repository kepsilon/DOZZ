/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPath
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The Rogers--Pitman radial path map

This module implements the pathwise part of the conditioned entrance construction: from three
continuous coordinate paths `V`, form `t ↦ |V_t + μ t e₁|`. Continuity is built into the
resulting `BrownianPath`; no extension of the conditioned finite-dimensional laws is involved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Three continuous real paths, viewed as the coordinates of a vector path in `ℝ³`. -/
abbrev BrownianTriple := Fin 3 → BrownianPath

/-- The product of three copies of a one-dimensional path law. -/
noncomputable def brownianTripleMeasure (W : Measure BrownianPath) : Measure BrownianTriple :=
  Measure.pi fun _ : Fin 3 => W

instance isProbabilityMeasure_brownianTripleMeasure (W : Measure BrownianPath)
    [IsProbabilityMeasure W] : IsProbabilityMeasure (brownianTripleMeasure W) := by
  unfold brownianTripleMeasure
  infer_instance

/-- The drifted vector at time `t`, with drift in the first coordinate. -/
def rogersPitmanVectorAt (μ : ℝ) (V : BrownianTriple) (t : ℝ≥0) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    V i t + (if i = 0 then μ * (t : ℝ) else 0))

/-- The continuous Rogers--Pitman radial path `t ↦ |V_t + μ t e₁|`. -/
noncomputable def rogersPitmanPath (μ : ℝ) (V : BrownianTriple) : BrownianPath :=
  ⟨fun t => ‖rogersPitmanVectorAt μ V t‖, by
    apply Continuous.norm
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    split_ifs <;> fun_prop⟩

theorem measurable_rogersPitmanPath (μ : ℝ) :
    Measurable (fun V : BrownianTriple => rogersPitmanPath μ V) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun V : BrownianTriple => ‖rogersPitmanVectorAt μ V t‖)
  apply Measurable.norm
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  have h_eval : Measurable (fun V : BrownianTriple => (V i) t) :=
    (ContinuousMap.measurable_eval t).comp (measurable_pi_apply i)
  split_ifs <;> exact h_eval.add_const _

theorem rogersPitmanPath_nonneg (μ : ℝ) (V : BrownianTriple) (t : ℝ≥0) :
    0 ≤ rogersPitmanPath μ V t := by
  change 0 ≤ ‖rogersPitmanVectorAt μ V t‖
  exact norm_nonneg _

theorem rogersPitmanPath_zero (μ : ℝ) (V : BrownianTriple)
    (hV : ∀ i, V i 0 = 0) :
    rogersPitmanPath μ V 0 = 0 := by
  change ‖rogersPitmanVectorAt μ V 0‖ = 0
  apply norm_eq_zero.mpr
  ext i
  simp [rogersPitmanVectorAt, hV]


/-- The probability candidate for the positive conditioned entrance path, obtained by mapping the
product of three Brownian path laws through the radial construction. -/
noncomputable def rogersPitmanEntranceMeasure (μ : ℝ) (W : Measure BrownianPath) :
    Measure BrownianPath :=
  (brownianTripleMeasure W).map (rogersPitmanPath μ)

instance isProbabilityMeasure_rogersPitmanEntranceMeasure (μ : ℝ)
    (W : Measure BrownianPath) [IsProbabilityMeasure W] :
    IsProbabilityMeasure (rogersPitmanEntranceMeasure μ W) := by
  unfold rogersPitmanEntranceMeasure
  infer_instance

/-- The negative conditioned path is the negative of the positive radial entrance path. -/
noncomputable def negativeRogersPitmanPath (μ : ℝ) (V : BrownianTriple) : BrownianPath :=
  -(rogersPitmanPath μ V)

theorem measurable_negativeRogersPitmanPath (μ : ℝ) :
    Measurable (fun V : BrownianTriple => negativeRogersPitmanPath μ V) := by
  exact (measurable_rogersPitmanPath μ).neg

/-- The negative entrance candidate is the pushforward under `-R`. -/
noncomputable def negativeRogersPitmanEntranceMeasure (μ : ℝ) (W : Measure BrownianPath) :
    Measure BrownianPath :=
  (brownianTripleMeasure W).map (negativeRogersPitmanPath μ)

instance isProbabilityMeasure_negativeRogersPitmanEntranceMeasure (μ : ℝ)
    (W : Measure BrownianPath) [IsProbabilityMeasure W] :
    IsProbabilityMeasure (negativeRogersPitmanEntranceMeasure μ W) := by
  unfold negativeRogersPitmanEntranceMeasure
  infer_instance

theorem negativeRogersPitmanPath_zero (μ : ℝ) (V : BrownianTriple)
    (hV : ∀ i, V i 0 = 0) :
    negativeRogersPitmanPath μ V 0 = 0 := by
  simp [negativeRogersPitmanPath, rogersPitmanPath_zero μ V hV]

end DOZZ.Proofs

end
