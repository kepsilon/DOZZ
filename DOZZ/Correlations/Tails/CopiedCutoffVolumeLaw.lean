/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.FiniteWickCopyLaw
public import DOZZ.Correlations.Tails.UnpinnedCutoffIdentity

/-! Copied-pin laws for the literal local cutoff volume integrals. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Pin copying preserves the law of every nonnegative compact local Wick integral. -/
theorem copied_cutoff_volume_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ r ρ : ℝ) (hρ : 0 ≤ ρ)
    (hr : ρ + Real.exp (-r) ≤ 1)
    (f : BoundedContinuousFunction ℂ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfs : ∀ x, f x ≠ 0 → ‖x‖ ≤ ρ) :
    P.map (fun ω => ∫ x, f x * Real.exp (γ * Xc ω (z+x) r -
      γ^2/2 * (r+2*Real.log ‖z+x‖)) ∂volume) =
    (P.prod P).map (fun q => ∫ x, f x * Real.exp
      (γ * (Xc q.2 z 0+(Xc q.1 (z+x) r-Xc q.1 z 0)+
        localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0)) -
          γ^2/2 * (r+2*Real.log ‖z+x‖)) ∂volume) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let K := Metric.closedBall (0 : ℂ) ρ
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  let ν : FiniteMeasure ℂ := ⟨volume.restrict K, ⟨by
    simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : ℂ) ρ).measure_lt_top⟩⟩
  have hr0 : 0 ≤ r := by
    have he : Real.exp (-r) ≤ 1 := by linarith
    have := Real.exp_le_one_iff.mp he
    linarith
  let p : ℂ → localCircle := fun x =>
    if hx : x ∈ K then ⟨(x,r), by
      have hn : ‖x‖ ≤ ρ := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
      dsimp
      linarith⟩
    else ⟨(0,r), by dsimp; simpa only [norm_zero, zero_add] using (by linarith : Real.exp (-r) ≤ 1)⟩
  have hp : Measurable p := by
    apply Measurable.subtype_mk
    have heq : (fun x => (p x).val) = (fun x : ℂ => if x ∈ K then (x,r) else (0,r)) := by
      funext x
      by_cases hx : x ∈ K
      · simp only [p, dite_eq_left hx, ite_eq_left hx]
      · simp only [p, dite_eq_right hx, ite_eq_right hx]
    change Measurable (fun x => (p x).val)
    rw [heq]
    exact Measurable.ite hK (measurable_id.prodMk measurable_const) measurable_const
  have hpx (x : ℂ) (hx : x ∈ K) : (p x).val = (x,r) := by simp only [p, dite_eq_left hx]
  have hweight : Integrable (f : ℂ → ℝ) (ν : Measure ℂ) := f.integrable (μ := (ν : Measure ℂ))
  have hlaw := offCenter_wick_copy_finite_law P X Xc hX hc hm z hz ν p hp γ
    (fun _ : Fin 1 => (f : ℂ → ℝ)) (fun _ => f.continuous.measurable) (fun _ => hf0)
      (fun _ => hweight)
  have hsrc : Measurable (fun ω (_ : Fin 1) => ∫ x, f x * Real.exp
      (γ * Xc ω (z+(p x).val.1) (p x).val.2 - γ^2/2 *
        ((p x).val.2+2*Real.log ‖z+(p x).val.1‖).toNNReal) ∂(ν : Measure ℂ)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hpv := measurable_subtype_coe.comp hp
    have hh : Measurable (fun q : Ω × ℂ => f q.2 * Real.exp
      (γ * Xc q.1 (z+(p q.2).val.1) (p q.2).val.2 - γ^2/2 *
        ((p q.2).val.2+2*Real.log ‖z+(p q.2).val.1‖).toNNReal)) := by
      have hx : Measurable (fun q : Ω × ℂ => Xc q.1
        (z+(p q.2).val.1) (p q.2).val.2) := hm.comp (measurable_fst.prodMk
        (((measurable_const (a := z)).add (hpv.fst.comp measurable_snd)).prodMk (hpv.snd.comp measurable_snd)))
      fun_prop
    exact hh.stronglyMeasurable.integral_prod_right.measurable
  have htar : Measurable (fun q (_ : Fin 1) => ∫ x, f x * Real.exp
      (γ * copiedCircle Xc z q (p x) - γ^2/2 *
        ((p x).val.2+2*Real.log ‖z+(p x).val.1‖).toNNReal) ∂(ν : Measure ℂ)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hpv := measurable_subtype_coe.comp hp
    have hh : Measurable (fun q : (Ω × Ω) × ℂ => f q.2 * Real.exp
      (γ * copiedCircle Xc z q.1 (p q.2) - γ^2/2 *
        ((p q.2).val.2+2*Real.log ‖z+(p q.2).val.1‖).toNNReal)) := by
      unfold copiedCircle localPinCoefficient
      have h1 (x : ℂ) (r : ℝ) : Measurable (fun q : (Ω × Ω) × ℂ => Xc q.1.1 x r) := hm.comp
        (measurable_fst.fst.prodMk (measurable_const (a := (x,r))))
      have h2 (x : ℂ) (r : ℝ) : Measurable (fun q : (Ω × Ω) × ℂ => Xc q.1.2 x r) := hm.comp
        (measurable_fst.snd.prodMk (measurable_const (a := (x,r))))
      have hloc : Measurable (fun q : (Ω × Ω) × ℂ => Xc q.1.1
        (z+(p q.2).val.1) (p q.2).val.2) := hm.comp (measurable_fst.fst.prodMk
        (((measurable_const (a := z)).add (hpv.fst.comp measurable_snd)).prodMk (hpv.snd.comp measurable_snd)))
      fun_prop
    exact hh.stronglyMeasurable.integral_prod_right.measurable
  have h := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun v => v 0)) hlaw
  rw [Measure.map_map (measurable_pi_apply 0) hsrc,
    Measure.map_map (measurable_pi_apply 0) htar] at h
  have hv (x : ℂ) (hx : x ∈ K) : 0 ≤ r+2*Real.log ‖z+x‖ := by
    have hn : ‖x‖ ≤ ρ := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hx1 : ‖x‖ ≤ 1 := by linarith [Real.exp_pos (-r)]
    have hh := norm_sub_norm_le z (z+x)
    simp only [sub_add_cancel_left, norm_neg] at hh
    have hn1 : 1 ≤ ‖z+x‖ := by linarith
    have hl := Real.log_nonneg hn1
    linarith
  have hzero (x : ℂ) (hx : x ∉ K) : f x = 0 := by
    by_contra hn
    exact hx (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hfs x hn)
  have hsrcEq (ω : Ω) : (∫ x, f x * Real.exp
      (γ*Xc ω (z+(p x).val.1) (p x).val.2 - γ^2/2 *
        ((p x).val.2+2*Real.log ‖z+(p x).val.1‖).toNNReal) ∂(ν : Measure ℂ)) =
      ∫ x, f x * Real.exp (γ*Xc ω (z+x) r-γ^2/2*(r+2*Real.log ‖z+x‖)) ∂volume := by
    change (∫ x in K, _) = _
    rw [← integral_restrict_eq_integral_of_zero_on_compl volume K hK _
      (fun x hx => by rw [hzero x hx, zero_mul])]
    apply setIntegral_congr_fun hK
    intro x hx
    dsimp only
    simp only [hpx x hx, Real.coe_toNNReal _ (hv x hx)]
  have htarEq (q : Ω × Ω) : (∫ x, f x * Real.exp
      (γ*copiedCircle Xc z q (p x)-γ^2/2 *
        ((p x).val.2+2*Real.log ‖z+(p x).val.1‖).toNNReal) ∂(ν : Measure ℂ)) =
      ∫ x, f x * Real.exp
        (γ*(Xc q.2 z 0+(Xc q.1 (z+x) r-Xc q.1 z 0)+
          localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0)) -
            γ^2/2*(r+2*Real.log ‖z+x‖)) ∂volume := by
    change (∫ x in K, _) = _
    rw [← integral_restrict_eq_integral_of_zero_on_compl volume K hK _
      (fun x hx => by rw [hzero x hx, zero_mul])]
    apply setIntegral_congr_fun hK
    intro x hx
    unfold copiedCircle
    dsimp only
    simp only [hpx x hx, Real.coe_toNNReal _ (hv x hx)]
  simpa only [Function.comp_def, hsrcEq, htarEq] using h


end DOZZ.Proofs
