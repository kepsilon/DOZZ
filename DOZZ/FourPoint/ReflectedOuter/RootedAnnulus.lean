/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.ZeroMass
public import DOZZ.FourPoint.Reflected.ChargeShift
public import DOZZ.FourPoint.Reflected.AnnularLower
import DOZZ.GMC.Construction.RootedMeasureKernel
import Mathlib.Tactic

/-! # Rooting inside the deleted disk retains a supercritical freezing annulus -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A root closer to zero than the integration point adds a full first charge, up to a
constant independent of either point. The strict separation excludes the totalized diagonal. -/
theorem reflected_rootDensity_charge_lower (γ : ℝ) (u x : ℂ) (hx : 0 < ‖x‖)
    (hu : ‖u‖ < ‖x‖) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
      ENNReal.ofReal ((normPlus x / ‖x‖) ^ (γ * γ)) ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) := by
  have hd : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
    intro he
    rw [he] at hu
    exact (lt_irrefl _ hu)))
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : ‖u - x‖ ≤ 2 * ‖x‖ := (norm_sub_le u x).trans (by linarith only [hu])
  have hl := Real.log_le_log hd hn
  rw [Real.log_mul (by norm_num) hx.ne'] at hl
  have hpu : 0 ≤ Real.log (normPlus u) := Real.log_nonneg (le_max_left _ _)
  have hg : Real.log (normPlus x) - Real.log ‖x‖ - Real.log 2 ≤ gffKernel u x := by
    unfold gffKernel
    linarith only [hl, hpu]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos (div_pos hp hx), Real.log_div hp.ne' hx.ne', ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hg (sq_nonneg γ)
  nlinarith only [hh]

/-- The retained rooted zero mass bounds the local annular mass at charge `α₁+γ/2`. -/
theorem reflected_retainedZero_rooted_freezing_lower (γ α₁ α₂ α₃ r : ℝ)
    (μ : Measure ℂ) (u : ℂ) (hr : 0 < r) (hu : ‖u‖ ≤ r) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2) *
      ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|))) *
      freezingAnnulusMassLocal γ (α₁ + γ / 2) μ 0 r (1 / 2) ≤
        reflectedRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u μ) := by
  let E : Set ℂ := {x | r < ‖x‖ ∧ ‖x‖ < 1 / 2}
  let D : Set ℂ := {x | r ≤ ‖x‖}
  let d : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x))
  let c : ℝ := Real.exp (-γ ^ 2 * Real.log 2) *
    ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|))
  have hE : MeasurableSet E := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hd : Measurable d := ENNReal.measurable_ofReal.comp
    ((measurable_const.mul (measurable_pointRootPotential.comp
      (measurable_const.prodMk measurable_id))).exp)
  have hpoint (x : ℂ) (hx : x ∈ E) :
      ENNReal.ofReal c * ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ + γ / 2)))) ≤
        d x * coulombWeight γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ x := by
    have hn : 0 < ‖x‖ := hr.trans hx.1
    have hx0 : x ≠ 0 := norm_pos_iff.mp hn
    have hx1 : x ≠ 1 := by
      intro he
      have hh := hx.2
      rw [he, norm_one] at hh
      norm_num at hh
    have hbase := reflected_outer_annular_kernel_lower γ (α₁ + γ) α₂ α₃ 0 x hn hx.2
      (by simp only [norm_zero]; positivity)
    rw [show α₁ + γ - γ / 2 = α₁ + γ / 2 by ring] at hbase
    have hl : ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|)) *
        ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ + γ / 2)))) ≤
          coulombWeight γ ![-γ / 2, α₁ + γ, α₂] ![0, 0, 1] α₃ x := by
      rw [gammaHalfKernel_coulombWeight γ (α₁ + γ) α₂ α₃ 0 x hx0 hx0 hx1,
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hbase
    calc
      _ = ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
          (ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|)) *
            ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ + γ / 2))))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
          coulombWeight γ ![-γ / 2, α₁ + γ, α₂] ![0, 0, 1] α₃ x := mul_le_mul' le_rfl hl
      _ = (ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
          ENNReal.ofReal ((normPlus x / ‖x‖) ^ (γ * γ))) *
            coulombWeight γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ x := by
        rw [mul_assoc, reflected_coulombWeight_charge_shift γ γ α₁ α₂ α₃ 0 x hx0]
      _ ≤ _ := mul_le_mul' (reflected_rootDensity_charge_lower γ u x hn (hu.trans_lt hx.1)) le_rfl
  have heq : freezingAnnulusMassLocal γ (α₁ + γ / 2) μ 0 r (1 / 2) =
      ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ + γ / 2)))) ∂μ := by
    simp only [freezingAnnulusMassLocal, sub_zero, E]
  rw [heq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change (∫⁻ x in E, ENNReal.ofReal c * ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ + γ / 2)))) ∂μ) ≤ _
  calc
    _ ≤ ∫⁻ x in E, d x * coulombWeight γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ x ∂μ :=
      setLIntegral_mono' hE hpoint
    _ ≤ ∫⁻ x in D, d x * coulombWeight γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ x ∂μ :=
      lintegral_mono' (Measure.restrict_mono (fun _ hx => hx.1.le) le_rfl) (fun _ => le_rfl)
    _ = _ := by
      unfold reflectedRetainedZeroMass gmcRootedMeasure
      rw [restrict_withDensity hD, coulombMass_eq_lintegral_coulombWeight,
        lintegral_withDensity_eq_lintegral_mul _ hd (measurable_coulombWeight _ _ _ _)]
      rfl

end DOZZ.Proofs
