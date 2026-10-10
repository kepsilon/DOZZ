/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.SetMassMeasurable
public import DOZZ.GMC.Moments.SubunitSet

/-! The exact first-moment scale law rules out an atom at the inversion chart's missing point. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every finite-mass `IsGMCOf` version is almost surely atomless at the origin. The first moment
of a shrinking centered ball is its area scale times the fixed reference-ball first moment. -/
theorem gmc_atomless_at_zero_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∀ᵐ ω ∂P, M ω {0} = 0 := by
  let B : ℝ≥0∞ := gmcMassMoment P M (Metric.ball 0 (1 / 2 : ℝ)) 1
  let A : ℝ≥0∞ := ∫⁻ ω, M ω {0} ∂P
  have hBbound : B ≤ 1 + gmcReferenceMeasure Set.univ := by
    exact gmc_mass_subunit_moment_bound P X hX γ M hM
      (Metric.ball 0 (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hBref : gmcReferenceMeasure Set.univ < ⊤ :=
    gmcReferenceMeasure_univ_ne_top.lt_top
  have hBtop : B < ⊤ := by
    exact lt_of_le_of_lt hBbound (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hBref⟩)
  have hAmeas : AEMeasurable (fun ω => M ω {0}) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM {0}
      (measurableSet_singleton 0)
  have hpoint_le (c : ℝ) (hc : 0 < c) :
      A ≤ gmcMassMoment P M (Metric.ball 0 (c / 2)) 1 := by
    unfold A gmcMassMoment
    apply lintegral_mono
    intro ω
    change M ω {0} ≤ ENNReal.rpow (M ω (Metric.ball 0 (c / 2))) 1
    have hsubset : ({0} : Set ℂ) ⊆ Metric.ball 0 (c / 2) := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact Metric.mem_ball_self (show 0 < c / 2 by positivity)
    have hmass : M ω {0} ≤ M ω (Metric.ball 0 (c / 2)) := measure_mono hsubset
    exact hmass.trans_eq (ENNReal.rpow_one _).symm
  have hscale (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
      gmcMassMoment P M (Metric.ball 0 (c / 2)) 1 = ENNReal.ofReal (c ^ 2) * B := by
    have h := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
      (a := 0) (c := c) (R := (1 / 2 : ℝ)) hc hc1 (by norm_num) (by norm_num)
      (by norm_num; linarith)
      (1 : ℝ)
    rw [show c / 2 = c * (1 / 2 : ℝ) by ring]
    simpa [B] using h
  have hAleB : A ≤ B := by
    have h := hpoint_le 1 (by norm_num)
    rw [hscale 1 (by norm_num) (by norm_num)] at h
    simpa using h
  have hAtop : A < ⊤ := lt_of_le_of_lt hAleB hBtop
  have hAeq : A = 0 := by
    by_contra hAne
    have ha : 0 < A.toReal := ENNReal.toReal_pos hAne (ne_of_lt hAtop)
    have hb : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    have hab : A.toReal ≤ B.toReal := ENNReal.toReal_mono (ne_of_lt hBtop) hAleB
    let c : ℝ := A.toReal / (2 * (B.toReal + 1))
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hc1 : c ≤ 1 := by
      dsimp [c]
      have hden : 0 < 2 * (B.toReal + 1) := by positivity
      rw [div_le_one hden]
      linarith
    have hsmall := hpoint_le c hc
    rw [hscale c hc hc1] at hsmall
    have hprodtop : ENNReal.ofReal (c ^ 2) * B < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBtop
    have hreal : A.toReal ≤ c ^ 2 * B.toReal := by
      have hmono := ENNReal.toReal_mono (ne_of_lt hprodtop) hsmall
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)] at hmono
      exact hmono
    have hratio : B.toReal / (B.toReal + 1) ≤ 1 := by
      rw [div_le_one (by linarith : 0 < B.toReal + 1)]
      linarith
    have hratio0 : 0 ≤ B.toReal / (B.toReal + 1) := by positivity
    have hcb : c * B.toReal ≤ A.toReal / 2 := by
      rw [show c = A.toReal / (2 * (B.toReal + 1)) by rfl]
      calc
        A.toReal / (2 * (B.toReal + 1)) * B.toReal =
            (A.toReal / 2) * (B.toReal / (B.toReal + 1)) := by field_simp
        _ ≤ A.toReal / 2 :=
          mul_le_of_le_one_right (by positivity) hratio
    have hcSqBase : c ^ 2 ≤ c := by nlinarith [sq_nonneg c]
    have hcSq : c ^ 2 * B.toReal ≤ c * B.toReal :=
      mul_le_mul_of_nonneg_right hcSqBase hb
    linarith
  have hzero : A = 0 := hAeq
  have hmassZero : (fun ω => M ω {0}) =ᵐ[P] (fun _ => (0 : ℝ≥0∞)) :=
    (lintegral_eq_zero_iff' hAmeas).mp (by simpa [A] using hzero)
  filter_upwards [hmassZero] with ω hω
  exact hω

end DOZZ.Proofs
