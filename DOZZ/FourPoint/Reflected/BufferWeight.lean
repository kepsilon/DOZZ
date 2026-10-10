/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.BufferKernel
public import DOZZ.FourPoint.ReflectedOuter.DeletedDisk
public import DOZZ.FourPoint.ReflectedOuter.MassPerturbation
import Mathlib.Tactic
/-! Actual spatial buffer expectations at the reflected freezing rate. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- For a fixed buffer ratio, the actual buffer first-order expectation has the deleted-disk
freezing rate. All random estimates are supplied by the source GMC. -/
theorem reflected_buffer_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ R : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ) (hR : 0 ≤ R)
    (hreflect : Q γ-α₁ < γ/2) (hs : 2*Q γ+γ/2 < α₁+α₂+α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ (z : ℂ) (ξ : ℝ) (U : Set ℂ),
      MeasurableSet U → U ⊆ Metric.ball 0 (‖z‖^(1-ξ)) →
      (∀ x ∈ U, 0 < ‖x‖ ∧ ‖z‖ ≤ R*‖x‖) →
      0 < ‖z‖^(1-ξ) → ‖z‖^(1-ξ) < ε₀ → ‖z‖ ≤ ‖z‖^(1-ξ)/2 →
      (∫⁻ ω, (∫⁻ x in U, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^
          (-((α₁+α₂+α₃-γ/2-2*Q γ)/γ+1)) ∂P) ≤
      ENNReal.ofReal (C*(‖z‖^(1-ξ))^
        (γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2)) := by
  let q : ℝ := (α₁+α₂+α₃-γ/2-2*Q γ)/γ+1
  let e : ℝ := γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2
  let c : ℝ := (1+R)^(γ^2/2)*(1/4 : ℝ)^(-q)
  have hq : 0 < q := (reflected_freezing_margins γ α₁ α₂ α₃ hγ hα₁ hreflect hs).2.1
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨C, ε₀, hC, hε₀, hb⟩ := reflected_deleted_disk_weight_bound
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hreflect hs hX hM
  refine ⟨c*C, ε₀, mul_pos hc hC, hε₀, ?_⟩
  intro z ξ U hU hball hsep hr hr₀ hz
  let r : ℝ := ‖z‖^(1-ξ)
  have hpoint : ∀ᵐ ω ∂P,
      (∫⁻ x in U, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ≤
      ENNReal.ofReal c*((∫⁻ x in Metric.ball (0 : ℂ) r,
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂M ω)*
        reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)^(-q)) := by
    filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω h0 h1
    have hi := reflected_buffer_mass_upper γ α₁ α₂ α₃ R r hR z (M ω) U hU hball hsep
    have ht := ennreal_rpow_antitone_of_nonpos
      (reflected_outerMass_relative_comparison γ α₁ α₂ α₃ ξ hγ hγ₂ z (M ω) hr hz h0 h1).1
        (neg_nonpos.mpr hq.le)
    rw [ennreal_mul_rpow_of_ne_zero_ne_top _ _ (by norm_num : ENNReal.ofReal (1/4 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 1/4)] at ht
    have hh := mul_le_mul' hi ht
    calc
      _ ≤ _ := hh
      _ = _ := by
        dsimp only [c]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith only [hR]) _)]
        ring
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal c*((∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂M ω)*
        reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)^(-q)) ∂P := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal c*(∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂M ω)*
        reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)^(-q) ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c*ENNReal.ofReal (C*r^e) := mul_le_mul' le_rfl (hb r hr hr₀)
    _ = _ := by rw [← ENNReal.ofReal_mul hc.le]; congr 1; ring

end DOZZ.Proofs
