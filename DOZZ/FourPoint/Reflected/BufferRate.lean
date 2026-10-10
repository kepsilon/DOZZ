/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.BufferWeight
public import DOZZ.FourPoint.ReflectedOuter.Rates
import Mathlib.Tactic
/-! The literal intermediate spatial buffer has a negligible first-order expectation. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- For every fixed inner-buffer depth, the literal intermediate annulus has first-order
expectation little-o of the reflected power, under exactly the freezing slack. -/
theorem reflected_spatial_buffer_first_order_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ ξ h : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ)
    (hreflect : Q γ-α₁ < γ/2) (hs : 2*Q γ+γ/2 < α₁+α₂+α₃)
    (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hnear : γ*(Q γ-α₁) < ξ)
    (hfreeze : γ*(Q γ-α₁) < (1-ξ)*(γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsComplexLittleOAtZero (γ*(Q γ-α₁)) (fun z : ℂ =>
      (((∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^
          (-((α₁+α₂+α₃-γ/2-2*Q γ)/γ+1)) ∂P).toReal : ℝ) : ℂ)) := by
  let e : ℝ := γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2
  obtain ⟨C, ε₀, hC, hε₀, hb⟩ := reflected_buffer_weight_bound
    P X M γ α₁ α₂ α₃ (Real.exp h) hγ hγ₂ hα₁ (Real.exp_pos h).le hreflect hs hX hM
  apply reflected_outer_rate_littleO (γ*(Q γ-α₁)) ξ e 0 C _ hnear hfreeze
  filter_upwards [reflected_outer_cutoff_geometry ξ ε₀ hξ hξ₁ hε₀,
    self_mem_nhdsWithin] with z hz hz0
  let U : Set ℂ := {x | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)}
  have hU : MeasurableSet U := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hball : U ⊆ Metric.ball 0 (‖z‖^(1-ξ)) := by
    intro x hx
    simpa only [Metric.mem_ball,dist_zero_right] using hx.2
  have hsep : ∀ x ∈ U, 0 < ‖x‖ ∧ ‖z‖ ≤ Real.exp h*‖x‖ := by
    intro x hx
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    refine ⟨(mul_pos (Real.exp_pos _) hn).trans_le hx.1, ?_⟩
    have hh := mul_le_mul_of_nonneg_left hx.1 (Real.exp_pos h).le
    have he : Real.exp h*Real.exp (-h) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    simpa only [← mul_assoc,he,one_mul] using hh
  have hh := hb z ξ U hU hball hsep hz.1 hz.2.2.2.2 hz.2.2.2.1
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have hc : 0 ≤ C*(‖z‖^(1-ξ))^e := mul_nonneg hC.le (Real.rpow_nonneg hz.1.le _)
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal hc,zero_mul,zero_add,U,show γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2 = e from rfl] using ht

end DOZZ.Proofs
