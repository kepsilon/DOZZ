/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizedCopiedLaw

/-! Joint measurability of the actual copied insertion error. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem copied_error_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (z : ℂ) (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (F : ℂ → ℝ) (hF : Measurable F) (α ρ : ℝ) :
    AEMeasurable (fun q : Ω × Ω =>
      ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
        ∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
          |copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x -
            F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)
      (P.prod P) := by
  let : IsProbabilityMeasure P := hX.1
  have hfst := measurePreserving_fst (μ := P) (ν := P)
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst _ hY
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst _ hY γ _ hN
  have hpin := (hc.1 0).comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : Ω => z)))
  let θ : Ω × Ω → ℝ × ℝ := fun q => (Xc q.1 z 0,Xc q.2 z 0)
  have hθ : Measurable θ := (hpin.comp measurable_fst).prodMk (hpin.comp measurable_snd)
  let k := fun p : (ℝ × ℝ) × ℂ => ENNReal.ofReal
    |copiedMultiplier z γ p.1.1 p.1.2 F p.2-F z*Real.exp (-4*Real.log ‖z‖)| *
      (ENNReal.ofReal ‖p.2‖)^(-γ*α)
  have hk : Measurable k := by
    unfold k copiedMultiplier localPinCoefficient
    fun_prop
  have hd : MeasurableSet {p : (ℝ × ℝ) × ℂ | p.2 ∈ Metric.ball (0 : ℂ) ρ} :=
    measurable_snd (Metric.isOpen_ball.measurableSet)
  have hm := gmc_parameter_lintegral_aemeasurable (P.prod P) _ hY' γ hγ hγ2
    (N ∘ Prod.fst) hN' θ hθ.aemeasurable _ (hk.indicator hd)
  have hmass : AEMeasurable (fun q : Ω × Ω =>
      ∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
        |copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x-
          F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1) (P.prod P) := by
    convert hm using 1
    funext q
    change (∫⁻ x in Metric.ball (0 : ℂ) ρ, k (θ q,x) ∂N q.1) = _
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    rfl
  exact ((((hpin.comp measurable_snd).const_mul γ).sub_const _).exp.ennreal_ofReal).aemeasurable.mul hmass


end DOZZ.Proofs
