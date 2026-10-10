/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitCDF
public import DOZZ.Brownian.LastExitKernelCDF
public import DOZZ.Brownian.ConditionedPastState
public import DOZZ.Brownian.LastExitDyadicMixture

/-!
# Last-exit CDF with finite past observations

The full-history avoidance identity retains every finite past cylinder. The explicit Markov
factorization integrates its final state against the Gaussian last-exit primitive.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- The scalar state kernel's avoidance integral is the explicit last-exit primitive. -/
theorem conditionedPastStateKernel_integral_avoidance (ν c dt : ℝ) (k : ℕ)
    (hν : 0 < ν) (hc : 0 < c) (hdt : 0 < dt) (x : Fin (k+1) → ℝ)
    (hx : 0 < x (Fin.last k)) :
    (∫ y, lastExitAvoidanceFactor ν c y ∂conditionedPastStateKernel ν dt k x) =
      lastExitGaussianKernelCDF ν c (x (Fin.last k)) dt := by
  rw [conditionedPastStateKernel, Kernel.withDensity_apply _
    (measurable_conditionedPastStateKernel_density _ _ _) x, Kernel.const_apply]
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (max 0
      (conditionedPositiveTransitionDensity ν dt (x (Fin.last k)) y))) :=
    (measurable_conditionedPastStateKernel_density ν dt k).comp
      (measurable_const.prodMk measurable_id)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have he : (∫ y, (ENNReal.ofReal (max 0
      (conditionedPositiveTransitionDensity ν dt (x (Fin.last k)) y))).toReal •
      lastExitAvoidanceFactor ν c y) =
      ∫ y, conditionedPositiveTransitionDensity ν dt (x (Fin.last k)) y *
        lastExitAvoidanceFactor ν c y := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [ENNReal.toReal_ofReal (le_max_left _ _),
      max_eq_right (conditionedPositiveTransitionDensity_nonneg hν.le hdt hx y), smul_eq_mul]
  rw [he, integral_conditionedTransition_avoidance_eq_gaussianCDF ν c (x (Fin.last k)) dt hν hc hx hdt]

/-- The explicit last-exit primitive is measurable in its starting state. -/
theorem measurable_lastExitGaussianKernelCDF_state (ν c dt : ℝ) :
    Measurable (fun x => lastExitGaussianKernelCDF ν c x dt) := by
  have hstandard : Continuous brownianStandardHeatTail :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_brownianStandardHeatTail x).continuousAt
  have htail : Measurable (brownianHeatTail dt) :=
    (hstandard.comp (continuous_id.div_const (Real.sqrt dt))).measurable
  have hH : Measurable (conditionedH ν) := measurable_conditionedH_ref ν
  unfold lastExitGaussianKernelCDF
  have h1 : Measurable (fun x : ℝ => brownianHeatTail dt (c-x-ν*dt)) :=
    htail.comp ((measurable_const.sub measurable_id).sub measurable_const)
  have h2 : Measurable (fun x : ℝ => brownianHeatTail dt (c+x-ν*dt)) :=
    htail.comp ((measurable_const.add measurable_id).sub measurable_const)
  have h3 : Measurable (fun x : ℝ => brownianHeatTail dt (c-x+ν*dt)) :=
    htail.comp ((measurable_const.sub measurable_id).add measurable_const)
  have h4 : Measurable (fun x : ℝ => brownianHeatTail dt (c+x+ν*dt)) :=
    htail.comp ((measurable_const.add measurable_id).add measurable_const)
  have hE2 : Measurable (fun x : ℝ => Real.exp (-2*ν*x)) := by fun_prop
  have hE3 : Measurable (fun x : ℝ => Real.exp (2*ν*(c-x))) := by fun_prop
  exact (((h1.sub (hE2.mul h2)).sub (hE3.mul h3)).add
    (measurable_const.mul h4)).div hH

/-- The last-exit primitive is a probability weight at every positive starting state. -/
theorem lastExitGaussianKernelCDF_bounds (ν c x dt : ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hx : 0 < x) (hdt : 0 < dt) :
    0 ≤ lastExitGaussianKernelCDF ν c x dt ∧ lastExitGaussianKernelCDF ν c x dt ≤ 1 := by
  have hp := integrable_conditionedPositiveTransitionDensity hν.le hdt hx
  have hbound : ∀ᵐ y ∂(volume : Measure ℝ), ‖lastExitAvoidanceFactor ν c y‖ ≤ 1 := by
    filter_upwards [] with y
    have hb := lastExitAvoidanceFactor_bounds (x := y) hν hc
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hi := hp.mul_bdd (measurable_lastExitAvoidanceFactor ν c).aestronglyMeasurable hbound
  rw [← integral_conditionedTransition_avoidance_eq_gaussianCDF ν c x dt hν hc hx hdt]
  constructor
  · exact integral_nonneg fun y => mul_nonneg
      (conditionedPositiveTransitionDensity_nonneg hν.le hdt hx y)
      (lastExitAvoidanceFactor_bounds (x := y) hν hc).1
  · calc
      _ ≤ ∫ y, conditionedPositiveTransitionDensity ν dt x y :=
        integral_mono hi hp (fun y => mul_le_of_le_one_right
          (conditionedPositiveTransitionDensity_nonneg hν.le hdt hx y)
          (lastExitAvoidanceFactor_bounds (x := y) hν hc).2)
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one hν.le hdt hx

/-- A finite past cylinder and a last-exit CDF event have the explicit final-transition CDF. -/
theorem negativeConditionedLaw_finitePast_lastExit_CDF
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (k : ℕ) (ss : Fin (k+1) → ℝ≥0) (hs : ∀ i, 0 < (ss i : ℝ))
    (hmono : StrictMono ss) (u : ℝ≥0) (hu : ss (Fin.last k) < u)
    (A : Set (Fin (k+1) → ℝ)) (hA : MeasurableSet A) :
    P.real {p : BrownianPath | (fun i => -(p (ss i))) ∈ A ∧
      negativeLastExitTime p (c : ℝ) ≤ u} =
      ∫ x in A, lastExitGaussianKernelCDF ν (c : ℝ) (x (Fin.last k))
        ((u : ℝ)-(ss (Fin.last k) : ℝ))
        ∂(volume : Measure (Fin (k+1) → ℝ)).withDensity
          (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ))) := by
  let : IsProbabilityMeasure P := hP.2.1
  let evalPast : BrownianPath → (Fin (k+1) → ℝ) := fun p i => -(p (ss i))
  let evalPair : BrownianPath → (Fin (k+1) → ℝ) × ℝ := fun p => (evalPast p, -(p u))
  let μ : Measure (Fin (k+1) → ℝ) := volume.withDensity
    (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))
  let κ := conditionedPastStateKernel ν ((u : ℝ)-(ss (Fin.last k) : ℝ)) k
  let U : Set BrownianPath := evalPast ⁻¹' A
  let E : Set BrownianPath := {p | negativeLastExitTime p (c : ℝ) ≤ u}
  let F : (Fin (k+1) → ℝ) × ℝ → ℝ :=
    (Prod.fst ⁻¹' A).indicator (fun z => lastExitAvoidanceFactor ν (c : ℝ) z.2)
  have hmPast : Measurable evalPast :=
    measurable_pi_iff.mpr fun _ => (ContinuousMap.measurable_eval _).neg
  have hmPair : Measurable evalPair := hmPast.prodMk (ContinuousMap.measurable_eval u).neg
  have hmF : Measurable F :=
    ((measurable_lastExitAvoidanceFactor ν (c : ℝ)).comp measurable_snd).indicator
      (hA.preimage measurable_fst)
  have hu0 : 0 < (u : ℝ) := (hs (Fin.last k)).trans (NNReal.coe_lt_coe.mpr hu)
  have hdt : 0 < (u : ℝ)-(ss (Fin.last k) : ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr hu)
  have hU : MeasurableSet[conditionedPositiveNaturalFiltration u] U := by
    let : MeasurableSpace BrownianPath := conditionedPositiveNaturalFiltration u
    have hmeval : Measurable evalPast := by
      apply measurable_pi_iff.mpr
      intro i
      change Measurable[conditionedPositiveNaturalFiltration u]
        (conditionedPositiveProcessValue (ss i))
      apply Measurable.of_comap_le
      have hsu : ss i ≤ u := (hmono.monotone (Fin.le_last i)).trans hu.le
      exact le_iSup_of_le (ss i) (le_iSup_of_le hsu le_rfl)
    exact hA.preimage hmeval
  have hE : MeasurableSet E := measurableSet_le
    (measurable_negativeLastExitTime_joint.comp (measurable_const.prodMk measurable_id))
    measurable_const
  have hCDF := conditionedPositiveHistory_lastExit_le_setIntegral hP hB hν u c hu0 hc U hU
  have hleft : (∫ p in U, E.indicator (fun _ => (1 : ℝ)) p ∂P) =
      P.real {p : BrownianPath | evalPast p ∈ A ∧ negativeLastExitTime p (c : ℝ) ≤ u} := by
    rw [setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hj : P.map evalPair = μ ⊗ₘ κ :=
    negativeConditionedLaw_finitePast_state_compProd hP k ss hs hmono u hu
  have hFint : Integrable F (P.map evalPair) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hmF.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z.1 ∈ A
    · have hb := lastExitAvoidanceFactor_bounds (x := z.2) hν hc
      have heF : F z = lastExitAvoidanceFactor ν (c : ℝ) z.2 :=
        Set.indicator_of_mem (show z ∈ Prod.fst ⁻¹' A from hz) _
      rw [heF, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
    · simp [F, hz]
  rw [hj] at hFint
  have hint : (∫ p in U, lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt u p) ∂P) =
      ∫ z, F z ∂(μ ⊗ₘ κ) := by
    rw [← hj, integral_map hmPair.aemeasurable hmF.aestronglyMeasurable,
      ← integral_indicator (hA.preimage hmPast)]
    apply integral_congr_ae
    exact ae_of_all _ fun _ => rfl
  have hpastLaw : P.map evalPast = μ :=
    negativeConditionedLaw_positiveFDD hP (k+1) (by omega) ss hs hmono
  have hxpos : ∀ᵐ x ∂μ, 0 < x (Fin.last k) := by
    rw [← hpastLaw]
    exact (ae_map_iff hmPast.aemeasurable
      (measurableSet_lt measurable_const (measurable_pi_apply _))).2
        (conditionedPositiveStateAt_pos_ae hP (ss (Fin.last k)) (hs (Fin.last k)))
  calc
    _ = ∫ p in U, E.indicator (fun _ => (1 : ℝ)) p ∂P := hleft.symm
    _ = ∫ p in U, lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt u p) ∂P := hCDF
    _ = ∫ z, F z ∂(μ ⊗ₘ κ) := hint
    _ = ∫ x, ∫ y, F (x,y) ∂κ x ∂μ := Measure.integral_compProd hFint
    _ = ∫ x in A, ∫ y, lastExitAvoidanceFactor ν (c : ℝ) y ∂κ x ∂μ := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hxA : x ∈ A <;> simp [F, hxA]
    _ = _ := by
      apply setIntegral_congr_ae hA
      filter_upwards [hxpos] with x hx _
      exact conditionedPastStateKernel_integral_avoidance ν (c : ℝ) _ k hν hc hdt x hx

end DOZZ.Proofs

end
