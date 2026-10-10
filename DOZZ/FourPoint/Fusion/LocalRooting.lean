/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalSecondKernel
public import DOZZ.FourPoint.Fusion.RootedCoulombComplex

/-! # Rooting the local pure second derivative contribution -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The literal local `r₁` spatial integral equals its rooted reference-measure integral. -/
theorem fusion_localR1_rooting {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hβ : γ ^ 2 / 2 < γ * α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (s : ℝ) (hs : s < 0)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    (∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
      (∫ x in Metric.ball (0 : ℂ) (1 / 2),
        (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2 ∂M ω) ∂P) =
      ∫ x in Metric.ball (0 : ℂ) (1 / 2),
        (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2 *
        ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
          ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ) := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let f := fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2
  have hf : Measurable f := (Complex.measurable_ofReal.comp
    ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (measurable_const.prodMk measurable_id))).div ((measurable_id.sub_const z).pow_const 2)
  have hβ2 : γ * α₁ < 2 := by have h := (lt_div_iff₀ hγ).mp hα₁; nlinarith
  have hfi := fusion_localSecondKernel_integrable γ α₁ α₂ α₃ (by positivity) hβ hβ2 z hz
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, norm_one] at hz4
    norm_num at hz4
  have hzunit : ∀ j : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) j‖ ≤ 1 := by
    intro j
    fin_cases j
    · change ‖z‖ ≤ 1; linarith
    · simp
    · simp
  have hzinj : Function.Injective (![z, 0, 1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have ha : ∀ j : Fin 3, (![-γ / 2, α₁, α₂] : Fin 3 → ℝ) j < Q γ := by
    intro j
    fin_cases j
    · change -γ / 2 < Q γ
      unfold Q
      have : 0 < 2 / γ := by positivity
      linarith
    · change α₁ < Q γ
      unfold Q
      linarith
    · exact hα₂
  have hmfin := fusion_coulombMass_finite_ae P X hX γ hγ hγ2 M hM ![-γ / 2, α₁, α₂]
    ![z, 0, 1] hzinj α₃ ha hα₃
  have h := (fusion_rooted_coulomb_complex_integral P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] ![z, 0, 1] hzunit α₃ s hs hmfin (B.indicator f)
    (hf.indicator Metric.isOpen_ball.measurableSet) hfi).2.2.2
  have he : (fun x : ℂ => B.indicator f x *
      ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
        ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ)) =
      B.indicator (fun x => f x *
        ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
          ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ)) := by
    funext x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  rw [he, integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)] at h
  change _ = ∫ x, _ ∂volume.restrict B
  rw [gmcReferenceMeasure_restrict_unit_chart B Metric.isOpen_ball.measurableSet
    (fun x hx => by
      have hx' : ‖x‖ < 1 / 2 := by simpa only [B, Metric.mem_ball, dist_zero_right] using hx
      linarith)] at h
  simpa only [integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)] using h

end DOZZ.Proofs
