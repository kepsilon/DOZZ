/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.RogersPitman
public import Mathlib.Probability.Independence.Basic

/-!
# Independent Brownian coordinates for the Rogers--Pitman map

Given a continuous-path Brownian law, its three-fold product supplies three independent Brownian
coordinate paths. The radial Rogers--Pitman map itself is defined in `RogersPitman.lean`; this
module verifies the probabilistic input without using an extension theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The `i`th coordinate path under the three-fold product law has the original Brownian path
law. -/
theorem brownianTriple_coordinatePath_hasLaw
    (W : Measure BrownianPath) [IsProbabilityMeasure W] (i : Fin 3) :
    HasLaw (fun V : BrownianTriple => V i) W (brownianTripleMeasure W) := by
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  rw [brownianTripleMeasure, Measure.pi_map_eval]
  simp

/-- The coordinate paths in the three-fold product are mutually independent. -/
theorem brownianTriple_coordinatePaths_independent
    (W : Measure BrownianPath) [IsProbabilityMeasure W] :
    iIndepFun (fun i : Fin 3 => fun V : BrownianTriple => V i)
      (brownianTripleMeasure W) := by
  rw [brownianTripleMeasure]
  exact iIndepFun_pi (fun _ => (measurable_id : Measurable (id : BrownianPath → BrownianPath)).aemeasurable)

/-- Each coordinate process in the product construction is a Brownian motion with continuous
paths. Its finite-dimensional laws follow by transporting Mathlib's Brownian law along the
coordinate projection, while path continuity is part of the `BrownianPath` carrier. -/
theorem brownianTriple_coordinate_isBrownian
    (W : Measure BrownianPath) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun (t : ℝ≥0) (p : BrownianPath) => p t) W) (i : Fin 3) :
    IsBrownianReal (fun (t : ℝ≥0) (V : BrownianTriple) => (V i) t) (brownianTripleMeasure W) := by
  refine { toIsPreBrownianReal := ?_, cont := ?_ }
  · refine ⟨?_⟩
    intro I
    exact (hW.toIsPreBrownianReal.hasLaw I).comp (brownianTriple_coordinatePath_hasLaw W i)
  · exact ae_of_all _ fun V => (V i).continuous


end DOZZ.Proofs

end
