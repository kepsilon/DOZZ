/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernel
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Large-state limit of the last-exit avoidance probability

The deterministic-time last-exit route uses the probability of avoiding a fixed level after the
current time. This file records its large-state limit, a scalar ingredient for sending the
terminal time to infinity after the finite-grid kernel cancellation.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- From states tending to infinity, a positive-drift conditioned path avoids a fixed lower level
with probability tending to one. -/
theorem lastExitAvoidanceFactor_tendsto_one_atTop
    {ν c : ℝ} (hν : 0 < ν) :
    Tendsto (fun y : ℝ => lastExitAvoidanceFactor ν c y) atTop (𝓝 1) := by
  have hcoef : -2 * ν < 0 := by nlinarith
  have harg : Tendsto (fun y : ℝ => -2 * ν * (y - c)) atTop atBot := by
    have hmul : Tendsto (fun y : ℝ => (-2 * ν) * y) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg hcoef
    have hshift := tendsto_atBot_add_const_right _ (2 * ν * c) hmul
    convert hshift using 1
    ext y
    ring
  have harg' : Tendsto (fun y : ℝ => -2 * ν * y) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg hcoef
  have hexp : Tendsto (fun y : ℝ => Real.exp (-2 * ν * (y - c))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hexp' : Tendsto (fun y : ℝ => Real.exp (-2 * ν * y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg'
  have hnum : Tendsto (fun y : ℝ => 1 - Real.exp (-2 * ν * (y - c))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hden : Tendsto (fun y : ℝ => 1 - Real.exp (-2 * ν * y)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp'
  have hratio : Tendsto (fun y : ℝ =>
      (1 - Real.exp (-2 * ν * (y - c))) / (1 - Real.exp (-2 * ν * y)))
      atTop (𝓝 1) := by
    convert hnum.div hden (by norm_num) using 1
    simp
  have heq : (fun y : ℝ => lastExitAvoidanceFactor ν c y) =ᶠ[atTop]
      (fun y => (1 - Real.exp (-2 * ν * (y - c))) /
        (1 - Real.exp (-2 * ν * y))) := by
    filter_upwards [eventually_gt_atTop c] with y hy
    simp [lastExitAvoidanceFactor, conditionedH, hν.ne', hy]
  exact hratio.congr' heq.symm

end DOZZ.Proofs

end
