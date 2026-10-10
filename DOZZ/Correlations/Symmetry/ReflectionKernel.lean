/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.GffKernel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
@[expose] public section
namespace DOZZ.Proofs

/-- The change in the equator pinning potential under the swap of zero and one. -/
noncomputable def symmetryReflectionPotential (x : ℂ) : ℝ :=
  Real.log (normPlus (1 - x)) - Real.log (normPlus x)


/-- Reflection is involutive. -/
theorem symmetryReflection_involutive : Function.Involutive (fun x : ℂ => 1 - x) := by
  intro x
  ring

/-- The potential reverses sign under reflection. -/
theorem symmetryReflectionPotential_reflect (x : ℂ) :
    symmetryReflectionPotential (1 - x) = -symmetryReflectionPotential x := by
  unfold symmetryReflectionPotential
  rw [show (1 : ℂ) - (1 - x) = x by ring]
  ring
/-- The two compactifying norms are comparable under reflection. -/
theorem normPlus_reflection_le (x : ℂ) : normPlus (1 - x) ≤ 2 * normPlus x := by
  have h1 : 1 ≤ normPlus x := le_max_left _ _
  have hx : ‖x‖ ≤ normPlus x := le_max_right _ _
  apply max_le
  · linarith
  · have h := norm_sub_le (1 : ℂ) x
    rw [norm_one] at h
    linarith

/-- The affine re-pinning potential is continuous on the plane. -/
theorem symmetryReflectionPotential_continuous : Continuous symmetryReflectionPotential := by
  have hn : Continuous (fun x : ℂ => normPlus x) := continuous_const.max continuous_norm
  have hp (x : ℂ) : normPlus x ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)).ne'
  exact ((hn.comp (continuous_const.sub continuous_id)).log (fun x => hp (1 - x))).sub
    (hn.log hp)

/-- The change of pinning is uniformly bounded, including at infinity. -/
theorem symmetryReflectionPotential_bound (x : ℂ) :
    |symmetryReflectionPotential x| ≤ Real.log 2 := by
  have hu (y : ℂ) : symmetryReflectionPotential y ≤ Real.log 2 := by
    have hp : 0 < normPlus y := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖y‖)
    have hq : 0 < normPlus (1 - y) := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖1 - y‖)
    unfold symmetryReflectionPotential
    rw [← Real.log_div hq.ne' hp.ne']
    apply Real.log_le_log (div_pos hq hp)
    exact (div_le_iff₀ hp).mpr (normPlus_reflection_le y)
  apply abs_le.mpr
  constructor
  · have h := hu (1 - x)
    rw [symmetryReflectionPotential_reflect] at h
    linarith
  · exact hu x

/-- A bounded continuous representative of the affine pinning potential for Gaussian tilt. -/
noncomputable def symmetryReflectionPotentialBCF : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup symmetryReflectionPotential
    symmetryReflectionPotential_continuous (Real.log 2) (fun x => by
      simpa only [Real.norm_eq_abs] using symmetryReflectionPotential_bound x)
end DOZZ.Proofs
