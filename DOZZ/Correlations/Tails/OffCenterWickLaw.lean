/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterCircleLaw
public import DOZZ.GMC.Moments.ChaosLawFDDNoAux

/-! Exact Wick integral transport from the off-center local circle field to the origin.
Nonnegative integrable spatial weights suffice; section integrability follows from the
Gaussian Wick expectation rather than being an additional hypothesis. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The scalar law of the unpinned off-center circle has the same cutoff variance as at zero. -/
theorem offCenter_unpinned_circle_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    HasLaw (fun ω => Xc ω (z + p.val.1) p.val.2 - Xc ω z 0)
      (gaussianReal 0 p.val.2.toNNReal) P := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨hG, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hg := hG.hasGaussianLaw_fun_sub (s := (z + p.val.1, p.val.2)) (t := (z, 0))
  have hmean : (∫ ω, Xc ω (z + p.val.1) p.val.2 - Xc ω z 0 ∂P) = 0 := by
    rw [integral_sub ((hc.2.1 _ _).integrable (by norm_num))
      ((hc.2.1 _ _).integrable (by norm_num)), hm, hm, sub_self]
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, hmean, ← covariance_self hg.aemeasurable,
    offCenter_unpinned_circle_covariance P X Xc hX hc z hz p p,
    local_circle_self_potential]

/-- The matching origin circle has the same scalar Gaussian law. -/
theorem origin_local_circle_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (p : localCircle) :
    HasLaw (fun ω => Xc ω p.val.1 p.val.2) (gaussianReal 0 p.val.2.toNNReal) P := by
  obtain ⟨hG, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hg := hG.hasGaussianLaw_eval p.val
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, hm, ← covariance_self hg.aemeasurable,
    origin_local_circle_covariance P X Xc hX hc p p,
    local_circle_self_potential]

/-- Finite vectors of regularized weighted local masses obey the translated origin law. -/
theorem offCenter_wick_integral_law
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    (P' : Measure Ω') (X' : Ω' → Distr) (Xc' : Ω' → ℂ → ℝ → ℝ)
    (hX' : IsEquatorGFF P' X') (hc' : IsCircleAverage P' X' Xc')
    (hm' : Measurable (fun q : Ω' × (ℂ × ℝ) => Xc' q.1 q.2.1 q.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (ν : Measure S) [IsProbabilityMeasure ν]
    (p : S → localCircle) (hp : Measurable p) (γ : ℝ)
    {m : ℕ} (w : Fin m → S → ℝ) (hw : ∀ j, Measurable (w j))
    (hw0 : ∀ j x, 0 ≤ w j x) (hwi : ∀ j, Integrable (w j) ν) :
    P.map (fun ω j => ∫ x, w j x * Real.exp
      (γ * (Xc ω (z + (p x).val.1) (p x).val.2 - Xc ω z 0) -
        γ ^ 2 / 2 * (p x).val.2.toNNReal) ∂ν) =
    P'.map (fun ω j => ∫ x, w j x * Real.exp
      (γ * Xc' ω (p x).val.1 (p x).val.2 -
        γ ^ 2 / 2 * (p x).val.2.toNNReal) ∂ν) := by
  let : IsProbabilityMeasure P := hX.1
  let : IsProbabilityMeasure P' := hX'.1
  let U : Ω → S → ℝ := fun ω x =>
    Xc ω (z + (p x).val.1) (p x).val.2 - Xc ω z 0
  let V : Ω' → S → ℝ := fun ω x => Xc' ω (p x).val.1 (p x).val.2
  let v : S → ℝ≥0 := fun x => (p x).val.2.toNNReal
  have hpv : Measurable (fun x => (p x).val) := measurable_subtype_coe.comp hp
  have hU : Measurable (fun q : Ω × S => U q.1 q.2) := by
    exact (hm.comp (measurable_fst.prodMk
      ((measurable_const.add (hpv.fst.comp measurable_snd)).prodMk
        (hpv.snd.comp measurable_snd)))).sub
      (hm.comp (measurable_fst.prodMk
        (measurable_const (a := (z, (0 : ℝ))))))
  have hV : Measurable (fun q : Ω' × S => V q.1 q.2) :=
    hm'.comp (measurable_fst.prodMk (hpv.comp measurable_snd))
  have hv : Measurable v := hpv.snd.real_toNNReal
  exact chaosLawFDD_integral_map_eq ν U V v w γ hU hV hv hw
    (fun j => ae_integrable_weighted_wick_sections ν U v (w j) γ hU hv (hw j)
      (fun x => offCenter_unpinned_circle_hasLaw P X Xc hX hc z hz (p x))
      (hw0 j) (hwi j))
    (fun j => ae_integrable_weighted_wick_sections ν V v (w j) γ hV hv (hw j)
      (fun x => origin_local_circle_hasLaw P' X' Xc' hX' hc' (p x))
      (hw0 j) (hwi j))
    (fun r xs => offCenter_unpinned_circle_fdd_law P X Xc hX hc
      P' X' Xc' hX' hc' z hz (fun i => p (xs i)))


end DOZZ.Proofs
