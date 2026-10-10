/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.DecorrelationError
public import DOZZ.FourPoint.Reflected.Remainder
public import DOZZ.FourPoint.ReflectedOuter.Rates
import Mathlib.Tactic
/-! The actual signed decorrelation error is negligible at the reflected fusion power. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The multiplicative Kahane error has a linear bound when its exponent is at most one. -/
theorem reflected_comparison_exponential_error_bound (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (Real.exp t-1)*Real.exp t ≤ 2*Real.exp 1*t := by
  have hs : Real.exp t-1 ≤ 2*t := (le_abs_self _).trans (by
    simpa only [abs_of_nonneg ht] using Real.abs_exp_sub_one_le
      (show |t| ≤ 1 by rwa [abs_of_nonneg ht]))
  have hh := mul_le_mul hs (Real.exp_monotone ht1)
    (Real.exp_nonneg t) (mul_nonneg (by norm_num) ht)
  calc
    _ ≤ (2*t)*Real.exp 1 := hh
    _ = _ := by ring

/-- The signed error between the source and copied moments has rate `|z|^ξ`, uniformly over
nonnegative buffer depths, for one specified actual global carrier. Copied and original moments
are both finite. The only analytic hypotheses on this carrier are its proved full source law and
admissible circle-chart realizations; no decorrelation or limiting bound is assumed. -/
theorem reflected_source_decorrelation_error_on_carrier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (hwhole : ∀ (f : ℂ → ℝ≥0∞), Measurable f →
      ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (originRadialPath Xc ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) ∂P) =
      ∫⁻ ω, G (originRadialPath Xc ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ
          (originRadialPath Xc ω.1) x) ∂N ω.2) ∂P.prod P)
    (hNa : ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
      (fun ω => (N ω).restrict (originLateralChart ρ)))
    (α₁ α₂ α₃ q ξ κ : ℝ) (hq : 0 < q) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hslack : κ < ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 ≤ h →
      (∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) {z | z ≠ 0},
        let original := reflected_source_separatedMoment P M γ α₁ α₂ α₃ z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) q
        let copied := reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) q
        original ≠ ⊤ ∧ copied ≠ ⊤ ∧
          |original.toReal-copied.toReal| ≤ C*‖z‖^ξ) ∧
      IsComplexLittleOAtZero κ (fun z : ℂ =>
        ((reflected_source_separatedMoment P M γ α₁ α₂ α₃ z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) q).toReal -
         (reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) q).toReal : ℂ)) := by
  obtain ⟨C₀,hC₀,hbound⟩ := reflected_source_separated_moment_error
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM N hN hfin hwhole hNa α₁ α₂ α₃ q hq
  let A : ℝ := γ^2*3/2*(q^2+q)
  have hA : 0 < A := by dsimp only [A]; positivity
  let C : ℝ := 2*Real.exp 1*A*C₀
  have hC : 0 < C := by dsimp only [C]; positivity
  have hn : Tendsto (fun z : ℂ => ‖z‖^ξ)
      (nhdsWithin (0 : ℂ) {z | z ≠ 0}) (𝓝 0) := by
    have ht := ((Real.continuous_rpow_const hξ.le).comp continuous_norm).tendsto (0 : ℂ)
    simpa only [Function.comp_def,norm_zero,Real.zero_rpow hξ.ne'] using
      ht.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) {z | z ≠ 0}, A*‖z‖^ξ ≤ 1 := by
    have ht := hn.const_mul A
    rw [mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hz => hz.le
  refine ⟨C,hC,?_⟩
  intro h hh
  have herr : ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) {z | z ≠ 0},
      let original := reflected_source_separatedMoment P M γ α₁ α₂ α₃ z
        (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) q
      let copied := reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
        (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) q
      original ≠ ⊤ ∧ copied ≠ ⊤ ∧ |original.toReal-copied.toReal| ≤ C*‖z‖^ξ := by
    filter_upwards [reflected_outer_cutoff_geometry ξ 1 hξ hξ1 zero_lt_one,
      hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)), hsmall,
      self_mem_nhdsWithin] with z hz hp hsmallz hz0
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let r : ℝ := ‖z‖^(1-ξ)
    let s : ℝ := Real.exp (-h)*‖z‖
    have hs : 0 < s := mul_pos (Real.exp_pos _) hnz
    have he : s/r = Real.exp (-h)*‖z‖^ξ := by
      apply (div_eq_iff hz.1.ne').mpr
      have hpow : ‖z‖^ξ*‖z‖^(1-ξ) = ‖z‖ := by
        rw [← Real.rpow_add hnz,add_sub_cancel,Real.rpow_one]
      dsimp only [s,r]
      rw [mul_assoc,hpow]
    have hratio : s/r ≤ ‖z‖^ξ := by
      rw [he]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hnz.le _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh))
    have hsep : s/r ≤ 1/2 := hratio.trans hp.le
    have hzsep : ‖z‖ < ‖z‖^(1-ξ) := by linarith only [hz.1,hz.2.2.2.1]
    obtain ⟨ho,hc,herr⟩ := hbound z ξ s hz.2.2.1 hzsep hz.1 hz.2.1 hs hsep
    let t : ℝ := A*(s/r)
    have ht0 : 0 ≤ t := mul_nonneg hA.le (div_pos hs hz.1).le
    have ht : t ≤ A*‖z‖^ξ := mul_le_mul_of_nonneg_left hratio hA.le
    have ht1 : t ≤ 1 := ht.trans hsmallz
    have heq : γ^2*(3*(s/‖z‖^(1-ξ)))/2*(q^2+q) = t := by
      dsimp only [t,A,r]
      ring
    rw [heq] at herr
    refine ⟨ho,hc,herr.trans ?_⟩
    calc
      (Real.exp t-1)*Real.exp t*C₀ ≤ (2*Real.exp 1*t)*C₀ :=
        mul_le_mul_of_nonneg_right (reflected_comparison_exponential_error_bound t ht0 ht1) hC₀.le
      _ ≤ (2*Real.exp 1*(A*‖z‖^ξ))*C₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) hC₀.le
      _ = C*‖z‖^ξ := by dsimp only [C]; ring
  refine ⟨herr,isComplexLittleOAtZero_of_norm_le_power (C := C) hslack ?_⟩
  filter_upwards [herr] with z hz
  simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hz.2.2

end DOZZ.Proofs
