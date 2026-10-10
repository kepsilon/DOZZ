/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedCompactChaosLaw
public import DOZZ.Correlations.Tails.ParameterMassMeasurability

/-! The copied compact-chaos law in the extended-real integral representation. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem copied_compact_ennreal_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (g : BoundedContinuousFunction ℂ ℝ) (hgc : HasCompactSupport (g : ℂ → ℝ))
    (hg0 : ∀ x, 0 ≤ g x) (hgs : tsupport (g : ℂ → ℝ) ⊆ Metric.ball 0 1) :
    ∃ G : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (G : ℂ → ℝ) ∧
      (∀ y, G y = g (y-z) * Real.exp ((γ^2+4)*Real.log (normPlus y))) ∧
      P.map (fun ω => ENNReal.ofReal (Real.exp (-γ^2*Real.log ‖z‖)) *
        ∫⁻ y, ENNReal.ofReal (G y) ∂M ω) =
      (P.prod P).map (fun q => ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
        ∫⁻ x, ENNReal.ofReal (g x) * ENNReal.ofReal
          (Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))) ∂N q.1) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨G, hGc, hG, hlaw⟩ := copied_compact_chaos_law
    P X Xc hX hc hm z hz γ hγ hγ2 M hM N hN g hgc hg0 hgs
  refine ⟨G, hGc, hG, ?_⟩
  have hG0 (y : ℂ) : 0 ≤ G y := by
    rw [hG]
    exact mul_nonneg (hg0 _) (Real.exp_nonneg _)
  have hGi (ω : Ω) : Integrable (fun y => G y) (M ω) := by
    let : IsFiniteMeasure (M ω) := hM.1 ω
    exact G.integrable (μ := M ω)
  have hAm := gmc_parameter_integral_aemeasurable P X hX γ hγ hγ2 M hM
    (fun _ => ()) aemeasurable_const (fun p : Unit × ℂ => G p.2)
    (G.continuous.measurable.comp measurable_snd) (fun _ y => hG0 y) hGi
  let θ : Ω × Ω → ℝ := fun q => Xc q.2 z 0-Xc q.1 z 0
  have hθ : Measurable θ :=
    ((hc.1 0).comp (measurable_snd.prodMk measurable_const)).sub
      ((hc.1 0).comp (measurable_fst.prodMk measurable_const))
  let F : ℝ × ℂ → ℝ := fun p =>
    g p.2 * Real.exp (γ*localPinCoefficient z p.2*p.1)
  have hcoef : Measurable (localPinCoefficient z) := by
    unfold localPinCoefficient
    fun_prop
  have hF : Measurable F := (g.continuous.measurable.comp measurable_snd).mul
    ((((hcoef.comp measurable_snd).const_mul γ).mul measurable_fst).exp)
  have hF0 (t : ℝ) (x : ℂ) : 0 ≤ F (t,x) := mul_nonneg (hg0 x) (Real.exp_nonneg _)
  have hFeq (t : ℝ) (x : ℂ) : F (t,x) =
      exponentialParameterTest g (γ • boundedPinCoefficient z) t x := by
    by_cases hx : g x = 0
    · change g x * _ = g x * _
      simp only [hx, zero_mul]
    · have hs := hgs (subset_tsupport (g : ℂ → ℝ) (Function.mem_support.mpr hx))
      have hb := bounded_pin_coefficient_eq z x hz (by
        exact (show ‖x‖ < 1 from by simpa only [Metric.mem_ball, dist_zero_right] using hs).le)
      change g x * _ = g x * Real.exp ((γ * boundedPinCoefficient z x)*t)
      rw [hb]
  have hFi (q : Ω × Ω) : Integrable (fun x => F (θ q,x)) (N q.1) := by
    let : IsFiniteMeasure (N q.1) := hN.1 q.1
    simpa only [hFeq] using
      (exponentialParameterTest g (γ • boundedPinCoefficient z) (θ q)).integrable (μ := N q.1)
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hfst := measurePreserving_fst (μ := P) (ν := P)
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst _ hY
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst _ hY γ _ hN
  have hBm := gmc_parameter_integral_aemeasurable (P.prod P) _ hY'
    γ hγ hγ2 (N ∘ Prod.fst) hN' θ hθ.aemeasurable F hF hF0 hFi
  have hS : Measurable (fun q : Ω × Ω =>
      Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) :=
    (((hc.1 0).comp (measurable_snd.prodMk measurable_const)).const_mul γ).sub_const _ |>.exp
  have hA := hAm.const_mul (Real.exp (-γ^2*Real.log ‖z‖))
  have hB := hS.aemeasurable.mul hBm
  simp only [Function.comp_def, F, θ] at hB
  change AEMeasurable (fun q : Ω × Ω =>
    Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖) *
      ∫ x, g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0)) ∂N q.1)
    (P.prod P) at hB
  have hl := congrArg (fun μ : Measure ℝ => μ.map ENNReal.ofReal) hlaw
  rw [AEMeasurable.map_map_of_aemeasurable ENNReal.measurable_ofReal.aemeasurable hA,
    AEMeasurable.map_map_of_aemeasurable ENNReal.measurable_ofReal.aemeasurable hB] at hl
  convert hl using 1
  · congr 1
    funext ω
    rw [Function.comp_apply, ENNReal.ofReal_mul (Real.exp_nonneg _),
      ofReal_integral_eq_lintegral_ofReal (hGi ω) (ae_of_all _ hG0)]
  · congr 1
    funext q
    rw [Function.comp_apply, ENNReal.ofReal_mul (Real.exp_nonneg _),
      ofReal_integral_eq_lintegral_ofReal (hFi q) (ae_of_all _ (hF0 (θ q)))]
    congr 1
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_mul (hg0 x)).symm


end DOZZ.Proofs
