/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizedFamilyTest

/-! The localized original insertion law with the literal copied multiplier. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem localized_copied_singular_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hzk : z ∈ K) (hz : 2 ≤ ‖z‖) (F : ℂ → ℝ) (hF : F ∈ Family z)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (χ : BoundedContinuousFunction ℂ ℝ) (hχc : HasCompactSupport (χ : ℂ → ℝ))
    (hχ0 : ∀ x, 0 ≤ χ x) (hχs : tsupport (χ : ℂ → ℝ) ⊆ Metric.ball 0 (min radius 1))
    (β : ℝ) (hβ : 0 ≤ β) :
    P.map (fun ω => ∫⁻ y, ENNReal.ofReal (χ (y-z)*F y) *
      (ENNReal.ofReal ‖y-z‖)^(-β) ∂M ω) =
    (P.prod P).map (fun q => ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
      ∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x) *
        (ENNReal.ofReal ‖x‖)^(-β) ∂N q.1) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨g,hgc,hgeq,hg0,hgs⟩ := localized_translated_test
    K Family radius supBound derivBound lowerBound hFamily z hzk F hF γ χ hχc hχ0 hχs
  let C := ENNReal.ofReal (Real.exp (-γ^2*Real.log ‖z‖))
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  let A := fun ω => ∫⁻ y, ENNReal.ofReal (χ (y-z)*F y) *
    (ENNReal.ofReal ‖y-z‖)^(-β) ∂M ω
  let B := fun q : Ω × Ω => ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
    ∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x) *
      (ENNReal.ofReal ‖x‖)^(-β) ∂N q.1
  have hFn := (hFamily.2.2.2.2 z hzk F hF).2.1
  have hFm := (hFamily.2.2.2.2 z hzk F hF).1
  have hsrc (y : ℂ) : g (y-z)*Real.exp ((γ^2+4)*Real.log (normPlus y)) = χ (y-z)*F y := by
    rw [hgeq, add_sub_cancel, mul_assoc, ← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero, mul_one]
  have htgt (x : ℂ) (n nb : ℝ) :
      g x*Real.exp (γ*localPinCoefficient z x*(nb-n)) =
      Real.exp (-γ^2*Real.log ‖z‖)*(χ x*copiedMultiplier z γ n nb F x) := by
    by_cases hx : χ x = 0
    · simp only [hgeq, hx, zero_mul, mul_zero]
    · have hn : normPlus (z+x) = ‖z+x‖ := by
        have hx' := hχs (subset_tsupport (χ : ℂ → ℝ) (by simpa only [Function.mem_support] using hx))
        have hxnorm : ‖x‖ ≤ 1 := (show ‖x‖ < min radius 1 from by
          simpa only [Metric.mem_ball,dist_zero_right] using hx').le.trans (min_le_right _ _)
        have hh := norm_sub_norm_le z (z+x)
        simp only [sub_add_cancel_left,norm_neg] at hh
        unfold normPlus
        exact max_eq_right (by linarith)
      rw [hgeq, hn]
      unfold copiedMultiplier
      simp only [mul_assoc]
      rw [← Real.exp_add]
      rw [mul_comm (Real.exp (-γ^2*Real.log ‖z‖)), mul_assoc]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring_nf
  have hAm : AEMeasurable A P := by
    have hk : Measurable (fun y => ENNReal.ofReal (χ (y-z)*F y) *
        (ENNReal.ofReal ‖y-z‖)^(-β)) := by fun_prop
    exact (Measure.measurable_lintegral hk).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  have hpin : Measurable (fun ω => Xc ω z 0) :=
    (hc.1 0).comp (measurable_id.prodMk measurable_const)
  let θ : Ω × Ω → ℝ × ℝ := fun q => (Xc q.1 z 0,Xc q.2 z 0)
  have hθ : Measurable θ := (hpin.comp measurable_fst).prodMk (hpin.comp measurable_snd)
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hfst := measurePreserving_fst (μ := P) (ν := P)
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst _ hY
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst _ hY γ _ hN
  have hk : Measurable (fun p : (ℝ × ℝ) × ℂ =>
      ENNReal.ofReal (χ p.2*copiedMultiplier z γ p.1.1 p.1.2 F p.2)*
        (ENNReal.ofReal ‖p.2‖)^(-β)) := by
    unfold copiedMultiplier localPinCoefficient
    fun_prop
  have hBm : AEMeasurable B (P.prod P) :=
    ((((hpin.comp measurable_snd).const_mul γ).sub_const _).exp.ennreal_ofReal).aemeasurable.mul
      (gmc_parameter_lintegral_aemeasurable (P.prod P) _ hY' γ hγ hγ2
        (N ∘ Prod.fst) hN' θ hθ.aemeasurable _ hk)
  have hl := copied_compact_singular_law P X Xc hX hc hm z hz γ hγ hγ2
    M hM N hN g hgc hg0 hgs β hβ
  have hleft (ω : Ω) :
      C * (∫⁻ y, ENNReal.ofReal (g (y-z)) * (ENNReal.ofReal ‖y-z‖)^(-β) *
        ENNReal.ofReal (Real.exp ((γ^2+4)*Real.log (normPlus y))) ∂M ω) = C*A ω := by
    congr 1
    apply lintegral_congr
    intro y
    rw [mul_right_comm, ← ENNReal.ofReal_mul (hg0 _), hsrc]
  have hright (q : Ω × Ω) :
      ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
        (∫⁻ x, ENNReal.ofReal (g x) * (ENNReal.ofReal ‖x‖)^(-β) * ENNReal.ofReal
          (Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))) ∂N q.1) = C*B q := by
    have hi : (∫⁻ x, ENNReal.ofReal (g x) * (ENNReal.ofReal ‖x‖)^(-β) * ENNReal.ofReal
        (Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))) ∂N q.1) =
        C * ∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x) *
          (ENNReal.ofReal ‖x‖)^(-β) ∂N q.1 := by
      rw [← lintegral_const_mul' C _ hCt]
      apply lintegral_congr
      intro x
      rw [mul_right_comm, ← ENNReal.ofReal_mul (hg0 _), htgt,
        ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
    rw [hi]
    exact mul_left_comm _ _ _
  change P.map (fun ω => C * _) = (P.prod P).map (fun q => _) at hl
  simp only [hleft,hright] at hl
  have hcancel := congrArg (fun μ : Measure ℝ≥0∞ => μ.map (fun t => C⁻¹*t)) hl
  have hInv : Measurable (fun t : ℝ≥0∞ => C⁻¹*t) := measurable_const.mul measurable_id
  rw [AEMeasurable.map_map_of_aemeasurable hInv.aemeasurable (hAm.const_mul C),
    AEMeasurable.map_map_of_aemeasurable hInv.aemeasurable (hBm.const_mul C)] at hcancel
  change P.map (fun ω => C⁻¹*(C*A ω)) =
    (P.prod P).map (fun q => C⁻¹*(C*B q)) at hcancel
  simpa only [ENNReal.inv_mul_cancel_left hC0 hCt] using hcancel


end DOZZ.Proofs
