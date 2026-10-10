/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedCompactENNRealLaw
public import DOZZ.Correlations.Tails.SingularWeightedApproximation

/-! Copying the Gaussian pin commutes with the full insertion singularity. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The singular copied law holds as an equality of extended-real laws, without an
assumption that either singular mass is finite. The compact test localizes the insertion. -/
theorem copied_compact_singular_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (g : BoundedContinuousFunction ℂ ℝ) (hgc : HasCompactSupport (g : ℂ → ℝ))
    (hg0 : ∀ x, 0 ≤ g x) (hgs : tsupport (g : ℂ → ℝ) ⊆ Metric.ball 0 1)
    (β : ℝ) (hβ : 0 ≤ β) :
    P.map (fun ω => ENNReal.ofReal (Real.exp (-γ^2*Real.log ‖z‖)) *
      ∫⁻ y, ENNReal.ofReal (g (y-z)) * (ENNReal.ofReal ‖y-z‖)^(-β) *
        ENNReal.ofReal (Real.exp ((γ^2+4)*Real.log (normPlus y))) ∂M ω) =
    (P.prod P).map (fun q => ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
      ∫⁻ x, ENNReal.ofReal (g x) * (ENNReal.ofReal ‖x‖)^(-β) * ENNReal.ofReal
        (Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))) ∂N q.1) := by
  let : IsProbabilityMeasure P := hX.1
  let : MetricSpace ℝ≥0∞ := TopologicalSpace.metrizableSpaceMetric ℝ≥0∞
  let gn := singularCompactTest g hgc β
  have hgn0 (n : ℕ) (x : ℂ) : 0 ≤ gn n x :=
    singular_compact_test_nonneg g hgc hg0 β n x
  have hgnc (n : ℕ) : HasCompactSupport (gn n : ℂ → ℝ) :=
    hgc.mul_right
  have hgns (n : ℕ) : tsupport (gn n : ℂ → ℝ) ⊆ Metric.ball 0 1 :=
    (singular_compact_test_support g hgc β n).trans hgs
  let w : ℂ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp ((γ^2+4)*Real.log (normPlus y)))
  have hw : Measurable w := by unfold w normPlus; fun_prop
  let θ : Ω × Ω → ℝ := fun q => Xc q.2 z 0-Xc q.1 z 0
  have hθ : Measurable θ :=
    ((hc.1 0).comp (measurable_snd.prodMk measurable_const)).sub
      ((hc.1 0).comp (measurable_fst.prodMk measurable_const))
  let v : ℝ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (γ*localPinCoefficient z p.2*p.1))
  have hv : Measurable v := by unfold v localPinCoefficient; fun_prop
  let C := ENNReal.ofReal (Real.exp (-γ^2*Real.log ‖z‖))
  let S : Ω × Ω → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))
  have hS : Measurable S := ENNReal.measurable_ofReal.comp
    ((((hc.1 0).comp (measurable_snd.prodMk measurable_const)).const_mul γ).sub_const _ |>.exp)
  let A : ℕ → Ω → ℝ≥0∞ := fun n ω => C * ∫⁻ y, ENNReal.ofReal (gn n (y-z)) * w y ∂M ω
  let B : ℕ → Ω × Ω → ℝ≥0∞ := fun n q => S q * ∫⁻ x, ENNReal.ofReal (gn n x) * v (θ q,x) ∂N q.1
  let Alim := fun ω => C * ∫⁻ y,
    ENNReal.ofReal (g (y-z)) * (ENNReal.ofReal ‖y-z‖)^(-β) * w y ∂M ω
  let Blim := fun q : Ω × Ω => S q * ∫⁻ x,
    ENNReal.ofReal (g x) * (ENNReal.ofReal ‖x‖)^(-β) * v (θ q,x) ∂N q.1
  have hAm (n : ℕ) : AEMeasurable (A n) P := by
    have hk := (ENNReal.measurable_ofReal.comp
      ((gn n).continuous.measurable.comp (measurable_id.sub_const z))).mul hw
    exact ((Measure.measurable_lintegral hk).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)).const_mul C
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hfst := measurePreserving_fst (μ := P) (ν := P)
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst _ hY
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst _ hY γ _ hN
  have hBm (n : ℕ) : AEMeasurable (B n) (P.prod P) := by
    have hk : Measurable (fun p : ℝ × ℂ => ENNReal.ofReal (gn n p.2) * v p) :=
      (ENNReal.measurable_ofReal.comp ((gn n).continuous.measurable.comp measurable_snd)).mul hv
    exact hS.aemeasurable.mul (gmc_parameter_lintegral_aemeasurable
      (P.prod P) _ hY' γ hγ hγ2 (N ∘ Prod.fst) hN' θ hθ.aemeasurable _ hk)
  have hAc : TendstoInMeasure P A atTop Alim := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hAm n).aestronglyMeasurable)
    exact ae_of_all _ fun ω => ENNReal.Tendsto.const_mul
      (singular_compact_weighted_lintegral_tendsto g hgc hg0 β hβ z
        w hw (fun _ => ENNReal.ofReal_ne_top) (M ω)) (Or.inr ENNReal.ofReal_ne_top)
  have hBc : TendstoInMeasure (P.prod P) B atTop Blim := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hBm n).aestronglyMeasurable)
    apply ae_of_all
    intro q
    have hvq : Measurable (fun x => v (θ q,x)) := hv.comp (measurable_const.prodMk measurable_id)
    simpa only [sub_zero] using ENNReal.Tendsto.const_mul (a := S q)
      (singular_compact_weighted_lintegral_tendsto g hgc hg0 β hβ 0
        (fun x => v (θ q,x)) hvq (fun _ => ENNReal.ofReal_ne_top) (N q.1))
      (Or.inr ENNReal.ofReal_ne_top)
  have hlaw (n : ℕ) : P.map (A n) = (P.prod P).map (B n) := by
    obtain ⟨G, _, hG, hl⟩ := copied_compact_ennreal_law
      P X Xc hX hc hm z hz γ hγ hγ2 M hM N hN (gn n) (hgnc n) (hgn0 n) (hgns n)
    have heq (y : ℂ) : ENNReal.ofReal (G y) = ENNReal.ofReal (gn n (y-z)) * w y := by
      rw [hG, ENNReal.ofReal_mul (hgn0 n (y-z))]
    simpa only [heq] using hl
  exact map_eq_of_seq_map_eq_of_tendstoInMeasure A B Alim Blim hAm hBm
    (hAc.aemeasurable hAm) (hBc.aemeasurable hBm) hlaw hAc hBc


end DOZZ.Proofs
