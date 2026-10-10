/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.FourPoint.Reflected.RestartPast
public import DOZZ.FourPoint.Reflected.InnerKernelSqueeze
import Mathlib.Tactic
/-! Exact polar identification of the actual inner radial comparison mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual radial singular mass on the inner punctured disk is the literal lateral
exponential integral. This identity does not assume any independence or chaos law. -/
theorem reflected_inner_radial_polar (γ α : ℝ) (A : TwoSidedPath)
    (M : Measure ℂ) (T : ℝ≥0) :
    (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
      ENNReal.ofReal (‖x‖ ^ (-(γ * α))) ∂M) =
      ∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal
        (Real.exp (γ * (A s - (Q γ - α) * s))) ∂lateralProjectedGMC γ A M := by
  let f : ℝ → ℝ≥0∞ := fun s => if (T : ℝ) < s then
    ENNReal.ofReal (Real.exp (γ * α * s)) else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt measurable_const measurable_id)
    (((measurable_id.const_mul (γ * α)).exp).ennreal_ofReal) measurable_const
  have hi := lateralProjectedGMC_reinsert_lintegral γ A M f hf
  have hleft : (∫⁻ s, lateralForwardWeight γ A s * f s ∂lateralProjectedGMC γ A M) =
      ∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal
        (Real.exp (γ * (A s - (Q γ - α) * s))) ∂lateralProjectedGMC γ A M := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro s
    by_cases hs : (T : ℝ) < s
    · rw [indicator_of_mem (show s ∈ Ioi (T : ℝ) from hs)]
      have hsp : 0 ≤ s := T.coe_nonneg.trans hs.le
      simp only [f, ite_eq_left hs, lateralForwardWeight, abs_of_nonneg hsp]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · simp only [f, ite_eq_right hs, mul_zero, indicator_of_notMem (show s ∉ Ioi (T : ℝ) from hs)]
  have hright : (∫⁻ x, if x = 0 then 0 else f (-Real.log ‖x‖) ∂M) =
      ∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
        ENNReal.ofReal (‖x‖ ^ (-(γ * α))) ∂M := by
    have hE : MeasurableSet {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))} :=
      (measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const)
    rw [← lintegral_indicator hE]
    apply lintegral_congr
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have he : (T : ℝ) < -Real.log ‖x‖ ↔ ‖x‖ < Real.exp (-(T : ℝ)) := by
        rw [← Real.log_lt_iff_lt_exp hxp]
        constructor <;> intro hh <;> linarith
      by_cases hs : (T : ℝ) < -Real.log ‖x‖
      · rw [indicator_of_mem (show x ∈ {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))}
          from ⟨hxp, he.mp hs⟩)]
        simp only [hx, ite_false, f, ite_eq_left hs]
        rw [Real.rpow_def_of_pos hxp]
        congr 2
        ring
      · rw [indicator_of_notMem (show x ∉ {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))}
          from fun hh => hs (he.mpr hh.2))]
        simp only [hx, ite_false, f, ite_eq_right hs]
  exact hright.symm.trans (hi.symm.trans hleft)

/-- Deterministic radial restart extracts the exact scalar prefactor and translates the actual
lateral measure. The equality is samplewise and retains extended-real integrals. -/
theorem reflected_inner_polar_restart (γ ν : ℝ) (A : TwoSidedPath)
    (Z : Measure ℝ) (T : ℝ≥0) :
    (∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal (Real.exp (γ * (A s - ν * s))) ∂Z) =
      ENNReal.ofReal (Real.exp (γ * (A T - ν * T))) *
        ∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
          (γ * (brownianShiftPath T (radialPositiveHalf A) (Real.toNNReal u) - ν * u))) else 0)
            ∂Z.map (fun s => s - (T : ℝ)) := by
  let D := brownianShiftPath T (radialPositiveHalf A)
  let f : ℝ → ℝ≥0∞ := fun u => if 0 < u then ENNReal.ofReal
    (Real.exp (γ * (D (Real.toNNReal u) - ν * u))) else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt measurable_const measurable_id)
    (((D.continuous.measurable.comp measurable_real_toNNReal).sub
      (measurable_id.const_mul ν)).const_mul γ).exp.ennreal_ofReal measurable_const
  change _ = ENNReal.ofReal (Real.exp (γ * (A T - ν * T))) *
    ∫⁻ u, f u ∂Z.map (fun s => s - (T : ℝ))
  rw [lintegral_map hf (show Measurable (fun s : ℝ => s - (T : ℝ)) from
      measurable_id.sub_const _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : (T : ℝ) < s
  · rw [indicator_of_mem (show s ∈ Ioi (T : ℝ) from hs)]
    have hu : 0 < s - (T : ℝ) := sub_pos.mpr hs
    have htime : (T : ℝ) + (Real.toNNReal (s - (T : ℝ)) : ℝ) = s := by
      rw [Real.coe_toNNReal _ hu.le]
      ring
    have hval : D (Real.toNNReal (s - (T : ℝ))) = A s - A T := by
      change A ((T : ℝ) + (Real.toNNReal (s - (T : ℝ)) : ℝ)) - A T = _
      rw [htime]
    simp only [f, ite_eq_left hu, hval]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  · rw [indicator_of_notMem (show s ∉ Ioi (T : ℝ) from hs)]
    have hu : ¬0 < s - (T : ℝ) := fun h => hs (sub_pos.mp h)
    simp only [f, ite_eq_right hu, mul_zero]

/-- The actual inner kernel integral is squeezed by its radial polar mass, with both explicit
scalar factors. The bound is valid before taking any stochastic expectation. -/
theorem reflected_inner_kernel_mass_squeeze
    (γ α₁ α₂ α₃ R : ℝ) (z : ℂ) (A : TwoSidedPath) (M : Measure ℂ) (T : ℝ≥0)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hz : 0 < ‖z‖)
    (hT : Real.exp (-(T : ℝ)) < 1) (hsep : Real.exp (-(T : ℝ)) ≤ R * ‖z‖) :
    let η := Real.exp (-(T : ℝ))
    let V := ∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal
      (Real.exp (γ * (A s - (Q γ - α₁) * s))) ∂lateralProjectedGMC γ A M
    ENNReal.ofReal ((1-R) ^ (γ^2/2) * (1-η)⁻¹ ^ (-|γ*α₂|) * ‖z‖ ^ (γ^2/2)) * V ≤
      (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M) ∧
    (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M) ≤
      ENNReal.ofReal ((1+R) ^ (γ^2/2) * (1-η)⁻¹ ^ |γ*α₂| * ‖z‖ ^ (γ^2/2)) * V := by
  dsimp only
  rw [← reflected_inner_radial_polar γ α₁ A M T]
  let E : Set ℂ := {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hb (x : ℂ) (hx : x ∈ E) := reflected_inner_kernel_squeeze γ α₁ α₂ α₃ R
    (Real.exp (-(T : ℝ))) z x hR hR₁ (Real.exp_pos _).le hT hz hx.1
    (hx.2.le.trans hsep) hx.2.le
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ((1-R) ^ (γ^2/2) * (1-Real.exp (-(T : ℝ)))⁻¹ ^ (-|γ*α₂|)) *
        (‖z‖ ^ (γ^2/2) * ‖x‖ ^ (-(γ*α₁))) := by ring
      _ ≤ _ := (hb x hx).1
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((1+R) ^ (γ^2/2) * (1-Real.exp (-(T : ℝ)))⁻¹ ^ |γ*α₂|) *
        (‖z‖ ^ (γ^2/2) * ‖x‖ ^ (-(γ*α₁))) := (hb x hx).2
      _ = _ := by ring

end DOZZ.Proofs
