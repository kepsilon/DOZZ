/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceDecouplingBound
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
/-! Actual lateral decoupling is negligible at the prescribed dual fusion exponent. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The restarted inner radius divided by the retained exterior radius. -/
theorem dual_restart_radius_ratio (z : ℂ) (hz : z ≠ 0) (h ξ : ℝ) :
    (Real.exp (-h)*‖z‖)/‖z‖^(1-ξ) = Real.exp (-h)*‖z‖^ξ := by
  have hn := norm_pos_iff.mpr hz
  have hr := Real.rpow_pos_of_pos hn (1-ξ)
  have he : ‖z‖ = ‖z‖^(1-ξ)*‖z‖^ξ := by
    rw [← Real.rpow_add hn, sub_add_cancel, Real.rpow_one]
  have hratio : ‖z‖/‖z‖^(1-ξ) = ‖z‖^ξ := by
    calc
      _ = (‖z‖^(1-ξ)*‖z‖^ξ)/‖z‖^(1-ξ) := congrArg (fun y => y/‖z‖^(1-ξ)) he
      _ = _ := mul_div_cancel_left₀ _ hr.ne'
  rw [mul_div_assoc, hratio]

/-- The supplied chaos admits independent lateral copies whose actual signed separated-mass
error is little-o at every exponent below `ξ`. Their radial removal and independence are
proved on the same eventual family of source carriers. -/
theorem dual_source_decoupling_littleO
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun v : ℂ × ℝ => Xc ω v.1 v.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q h ξ κ : ℝ) (hq : 0 < q) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : κ < ξ) :
    ∃ N : ℂ → Ω → Measure ℂ,
      (∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), Measurable (N z) ∧
        IndepFun (originRadialPath Xc) (N z) P ∧
        (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N z ω K < ⊤) ∧
        N z =ᵐ[P] (fun ω => (M ω).withDensity
          (lateralRadialWeight γ (originRadialPath Xc ω)))) ∧
      Tendsto (fun z : ℂ =>
        ((dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal-
         (dualCopiedSeparatedInverseMoment P Xc (N z) γ α₁ α₂ α₃ q z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal)/‖z‖^κ)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  classical
  obtain ⟨C, hC, hbound⟩ := dual_source_decoupling_bound P X Xc hX hc hm hcont
    γ hγ hγ₂ M hM α₁ α₂ α₃ q hq
  let s := fun z : ℂ => Real.exp (-h)*‖z‖
  let r := fun z : ℂ => ‖z‖^(1-ξ)
  let d := 3*γ^2/2*(q^2+q)
  let valid := fun z : ℂ => ‖z‖ ≤ 1 ∧ 0 < s z ∧ 0 < r z ∧ r z ≤ 1 ∧
    s z/r z ≤ 1/2 ∧ d*(s z/r z) ≤ 1
  let PropN := fun z (N : Ω → Measure ℂ) => Measurable N ∧
    IndepFun (originRadialPath Xc) N P ∧
    (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
    N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
    |(dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z (s z) (r z)).toReal-
      (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z (s z) (r z)).toReal| ≤ C*(s z/r z)
  have hex : ∀ z : ℂ, ∃ N : Ω → Measure ℂ, valid z → PropN z N := by
    intro z
    by_cases hv : valid z
    · obtain ⟨N, hN⟩ := hbound z hv.1 (s z) (r z)
        hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2
      exact ⟨N, fun _ => hN⟩
    · exact ⟨fun _ => 0, fun hh => (hv hh).elim⟩
  choose N hN using hex
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hpow (v : ℝ) (hv : 0 < v) : Tendsto (fun z : ℂ => ‖z‖^v) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hv.ne'] using
      ((Real.continuous_rpow_const hv.le).tendsto (0 : ℝ)).comp hn
  have hratio : Tendsto (fun z : ℂ => s z/r z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht := (hpow ξ hξ).const_mul (Real.exp (-h))
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (dual_restart_radius_ratio z hz h ξ).symm
  have hdlim := hratio.const_mul d
  simp only [mul_zero] at hdlim
  have hv : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), valid z := by
    filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds zero_lt_one),
      (hpow (1-ξ) (sub_pos.mpr hξ1)).eventually (gt_mem_nhds zero_lt_one),
      hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
      hdlim.eventually (gt_mem_nhds zero_lt_one)] with z hz hz1 hr1 hsep ht1
    exact ⟨hz1.le, mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hz),
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _, hr1.le, hsep.le, ht1.le⟩
  refine ⟨N, ?_, ?_⟩
  · filter_upwards [hv] with z hz
    have hh := hN z hz
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
  let f := fun z : ℂ => (dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z (s z) (r z)).toReal-
    (dualCopiedSeparatedInverseMoment P Xc (N z) γ α₁ α₂ α₃ q z (s z) (r z)).toReal
  have hb : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖(f z : ℂ)‖ ≤
      (C*Real.exp (-h))*‖z‖^ξ := by
    filter_upwards [hv, self_mem_nhdsWithin] with z hz hz0
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hh := (hN z hz).2.2.2.2
    rw [show s z/r z = Real.exp (-h)*‖z‖^ξ from dual_restart_radius_ratio z hz0 h ξ] at hh
    simpa only [mul_assoc] using hh
  exact (isComplexLittleOAtZero_ofReal_iff κ f).mp
    (isComplexLittleOAtZero_of_norm_le_power hκ hb)

end DOZZ.Proofs
