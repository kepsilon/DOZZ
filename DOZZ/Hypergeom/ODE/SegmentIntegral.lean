/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.DiskPrimitive
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Segment integral formula for the normalized disk primitive. -/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem normalizedDiskPrimitive_sub_center_eq_segmentIntegral
    {c z : ℂ} {r : ℝ} {f : ℂ → E} {y : E}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    normalizedDiskPrimitive c r f y hf z - y =
      ∫ t in (0 : ℝ)..1, (z - c) • f (AffineMap.lineMap c z t) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let g : ℝ → ℂ := AffineMap.lineMap c z
  let F : ℝ → E := fun t => normalizedDiskPrimitive c r f y hf (g t)
  let f' : ℝ → E := fun t => (z - c) • f (g t)
  have hr : 0 < r := by
    have hdist := Metric.mem_ball.mp hz
    exact lt_of_le_of_lt (dist_nonneg) hdist
  have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hseg : MapsTo g (Icc (0 : ℝ) 1) (Metric.ball c r) :=
    (convex_ball c r).mapsTo_lineMap hc hz
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt F (f' t) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    have houter := hasDerivAt_normalizedDiskPrimitive (y := y) hf (hseg ht')
    have hcomp := houter.hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := c) (b := z))
    simpa [F, f', g, Function.comp_def, AffineMap.lineMap_apply_module] using hcomp
  have hfg : ContinuousOn f' (uIcc (0 : ℝ) 1) := by
    have hg : ContinuousOn g (uIcc (0 : ℝ) 1) :=
      AffineMap.lineMap_continuous.continuousOn
    have hfcomp : ContinuousOn (fun t => f (g t)) (uIcc (0 : ℝ) 1) :=
      hf.continuousOn.comp hg fun t ht => hseg (by
        simpa [uIcc_of_le zero_le_one] using ht)
    change ContinuousOn (fun t => (z - c) • f (g t)) (uIcc (0 : ℝ) 1)
    exact continuousOn_const.smul hfcomp
  have hint : IntervalIntegrable f' volume 0 1 := hfg.intervalIntegrable
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hF0 : F 0 = y := by
    simp [F, g, normalizedDiskPrimitive_apply_center]
  have hF1 : F 1 = normalizedDiskPrimitive c r f y hf z := by
    simp [F, g]
  calc
    normalizedDiskPrimitive c r f y hf z - y = F 1 - F 0 := by rw [hF1, hF0]
    _ = ∫ t in (0 : ℝ)..1, f' t := heq.symm
    _ = ∫ t in (0 : ℝ)..1, (z - c) • f (AffineMap.lineMap c z t) := rfl

end DOZZ.Proofs
