/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.BufferRate
/-! Finiteness of the actual first-order buffer expectation before real conversion. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_spatial_buffer_first_order_eventually_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ ξ h : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ)
    (hreflect : Q γ-α₁ < γ/2) (hs : 2*Q γ+γ/2 < α₁+α₂+α₃)
    (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^
          (-((α₁+α₂+α₃-γ/2-2*Q γ)/γ+1)) ∂P) < ⊤ := by
  obtain ⟨C, ε₀, _, hε₀, hb⟩ := reflected_buffer_weight_bound
    P X M γ α₁ α₂ α₃ (Real.exp h) hγ hγ₂ hα₁ (Real.exp_pos h).le hreflect hs hX hM
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
  exact lt_of_le_of_lt hh ENNReal.ofReal_lt_top

end DOZZ.Proofs
