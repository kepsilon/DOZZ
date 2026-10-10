/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceBufferExpectation
public import DOZZ.FourPoint.Reflected.BufferFinite
/-! The literal full source and separated inverse moments differ by a proved little-o. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_source_buffer_inverse_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ ξ h : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hreflect : Q γ-α₁ < γ/2) (hs : 2*Q γ+γ/2 < α₁+α₂+α₃)
    (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hnear : γ*(Q γ-α₁) < ξ)
    (hfreeze : γ*(Q γ-α₁) < (1-ξ)*(γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2))
    (hh : 0 ≤ h) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
    IsComplexLittleOAtZero (γ*(Q γ-α₁)) (fun z : ℂ =>
      ((gammaHalfMoment P M γ α₁ α₂ α₃ p z-
        (reflected_source_separatedMoment P M γ α₁ α₂ α₃ z (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) p).toReal : ℝ) : ℂ)) := by
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  let E := fun z : ℂ => (∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-(p+1)) ∂P).toReal
  have hE := reflected_spatial_buffer_first_order_littleO P X M γ α₁ α₂ α₃ ξ h
    hγ hγ₂ hα₁ hreflect hs hξ hξ₁ hnear hfreeze hX hM
  have hEf := reflected_spatial_buffer_first_order_eventually_finite P X M γ α₁ α₂ α₃ ξ h
    hγ hγ₂ hα₁ hreflect hs hξ hξ₁ hX hM
  have hb : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      |gammaHalfMoment P M γ α₁ α₂ α₃ p z-
        (reflected_source_separatedMoment P M γ α₁ α₂ α₃ z (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) p).toReal| ≤ p*E z := by
    filter_upwards [reflected_outer_cutoff_geometry ξ 1 hξ hξ₁ zero_lt_one,hEf,self_mem_nhdsWithin]
      with z hz hfin hz0
    have hr := hz.1
    have hr1 : ‖z‖^(1-ξ) ≤ 1 := hz.2.2.2.2.le
    have hzr : ‖z‖ < ‖z‖^(1-ξ) := by linarith only [hr,hz.2.2.2.1]
    have hzn : ‖z‖ < 1 := hzr.trans_le hr1
    have hz1 : z ≠ 1 := by intro he; simp [he] at hzn
    have hss : 0 < Real.exp (-h)*‖z‖ := mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hz0)
    have hsr : Real.exp (-h)*‖z‖ ≤ ‖z‖^(1-ξ) :=
      (mul_le_of_le_one_left (norm_nonneg z) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh))).trans hzr.le
    exact reflected_source_buffer_inverse_error P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ ξ
      (Real.exp (-h)*‖z‖) p hp hα₁ hα₂ hα₃ z hz0 hz1 hzn.le hr1 hzr hss hsr hfin
  unfold IsComplexLittleOAtZero at hE ⊢
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] at hE
  simp only [Complex.norm_real,Real.norm_eq_abs]
  apply squeeze_zero' (Filter.Eventually.of_forall fun z =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg z) _))
  · filter_upwards [hb] with z hz
    exact div_le_div_of_nonneg_right hz (Real.rpow_nonneg (norm_nonneg z) _)
  · simpa only [p,E,mul_div_assoc,mul_zero] using hE.const_mul p

end DOZZ.Proofs
