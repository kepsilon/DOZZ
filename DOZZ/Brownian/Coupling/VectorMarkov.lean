/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.RadialTransition
public import DOZZ.Brownian.Barrier.KilledMarkov
public import DOZZ.Brownian.ConditionedFDDMarkovKernel

/-!
# Deterministic Markov law of the actual three-dimensional Wiener source

Apply the proved scalar stopped-past/full-future product law to the three independent coordinate
paths, then interchange the finite product and the past/future pair. This retains all radial past
tests and the actual independent Euclidean Gaussian increment.

Positive current times avoid the singular radial start; the Maxwell entrance law supplies that start.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Stop and hold all three actual coordinate paths at one deterministic time. -/
noncomputable def wienerTripleStop (s : ℝ≥0) (V : BrownianTriple) : BrownianTriple :=
  fun i => stopBrownianPath (V i) s

/-- Restart all three actual coordinate paths with zero future increments. -/
noncomputable def wienerTripleShift (s : ℝ≥0) (V : BrownianTriple) : BrownianTriple :=
  fun i => brownianShiftPath s (V i)

theorem measurable_wienerTripleStop (s : ℝ≥0) : Measurable (wienerTripleStop s) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk (measurable_pi_apply i)))

theorem measurable_wienerTripleShift (s : ℝ≥0) : Measurable (wienerTripleShift s) := by
  apply measurable_pi_iff.mpr
  intro i
  exact continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk (measurable_pi_apply i))

/-- The actual stopped past and full future of the Wiener triple have product law. -/
theorem wienerTriple_deterministic_restart_joint_map (s : ℝ≥0) :
    wienerTripleMeasure.map (fun V => (wienerTripleStop s V, wienerTripleShift s V)) =
      (wienerTripleMeasure.map (wienerTripleStop s)).prod wienerTripleMeasure := by
  let Q := wienerPathMeasure.map (fun p => stopBrownianPath p s)
  have hscalar : wienerPathMeasure.map (fun p => (stopBrownianPath p s, brownianShiftPath s p)) =
      Q.prod wienerPathMeasure :=
    brownianPath_deterministic_restart_joint_map wienerPathMeasure wienerPathMeasure_isBrownian
      s (fun p => stopBrownianPath p s) (measurable_stopBrownianPath_raw s)
  have hQprob : IsProbabilityMeasure Q :=
    (Measure.isProbabilityMeasure_map_iff
      (continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable).mpr inferInstance
  let _ := hQprob
  let e := MeasurableEquiv.arrowProdEquivProdArrow BrownianPath BrownianPath (Fin 3)
  let pairs := fun V : BrownianTriple => fun i : Fin 3 => (stopBrownianPath (V i) s, brownianShiftPath s (V i))
  have hpairs : Measurable pairs := measurable_pi_iff.mpr fun i =>
    ((continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk (measurable_pi_apply i))).prodMk
      (continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk (measurable_pi_apply i))))
  have hstop : wienerTripleMeasure.map (wienerTripleStop s) = Measure.pi (fun _ : Fin 3 => Q) := by
    change (Measure.pi (fun _ : Fin 3 => wienerPathMeasure)).map
      (fun V i => stopBrownianPath (V i) s) = _
    exact Measure.pi_map_pi (fun _ =>
      (continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  calc
    _ = (wienerTripleMeasure.map pairs).map e := by
      rw [Measure.map_map e.measurable hpairs]
      rfl
    _ = (Measure.pi (fun _ : Fin 3 => Q.prod wienerPathMeasure)).map e := by
      change ((Measure.pi (fun _ : Fin 3 => wienerPathMeasure)).map
        (fun V i => (stopBrownianPath (V i) s, brownianShiftPath s (V i)))).map e = _
      rw [Measure.pi_map_pi (f := fun (_ : Fin 3) (p : BrownianPath) =>
        (stopBrownianPath p s, brownianShiftPath s p)) (fun _ =>
        ((continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)).prodMk
          (continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id))).aemeasurable)]
      simp_rw [hscalar]
    _ = (Measure.pi (fun _ : Fin 3 => Q)).prod (Measure.pi (fun _ : Fin 3 => wienerPathMeasure)) :=
      (measurePreserving_arrowProdEquivProdArrow BrownianPath BrownianPath (Fin 3)
        (fun _ => Q) (fun _ => wienerPathMeasure)).map_eq
    _ = _ := by rw [hstop]; rfl

/-- Every jointly measurable stopped-past/full-future test has the actual independent product integral. -/
theorem wienerTriple_deterministic_restart_lintegral (s : ℝ≥0)
    (F : BrownianTriple × BrownianTriple → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (wienerTripleStop s V, wienerTripleShift s V) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ U, F (wienerTripleStop s V, U) ∂wienerTripleMeasure ∂wienerTripleMeasure := by
  rw [← lintegral_map hF ((measurable_wienerTripleStop s).prodMk (measurable_wienerTripleShift s)),
    wienerTriple_deterministic_restart_joint_map s, lintegral_prod _ hF.aemeasurable,
    lintegral_map (show Measurable (fun x : BrownianTriple => ∫⁻ y, F (x, y) ∂wienerTripleMeasure) from
      Measurable.lintegral_prod_right (show Measurable (Function.uncurry (fun x y => F (x, y))) from hF))
      (measurable_wienerTripleStop s)]

/-- Centered vector evaluation of the actual coordinate paths. -/
noncomputable def wienerVectorEval (t : ℝ≥0) (V : BrownianTriple) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => V i t)

theorem measurable_wienerVectorEval (t : ℝ≥0) : Measurable (wienerVectorEval t) :=
  (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun i =>
    (ContinuousMap.measurable_eval t).comp (measurable_pi_apply i))

/-- Stopping retains the actual vector value at the stopping time. -/
theorem wienerVectorEval_stop (s : ℝ≥0) (V : BrownianTriple) :
    wienerVectorEval s (wienerTripleStop s V) = wienerVectorEval s V := by
  apply WithLp.ofLp_injective 2
  funext i
  change V i (min s s) = V i s
  rw [min_self]

/-- The actual shifted path reconstructs every future vector value from its start and increment. -/
theorem wienerVectorEval_shift_add (s dt : ℝ≥0) (V : BrownianTriple) :
    wienerVectorEval s V + wienerVectorEval dt (wienerTripleShift s V) = wienerVectorEval (s + dt) V := by
  apply WithLp.ofLp_injective
  funext i
  change V i s + (V i (s + dt) - V i s) = V i (s + dt)
  ring

/-- The Wiener vector has the actual centered Euclidean Gaussian evaluation law. -/
theorem wienerVectorEval_hasLaw (t : ℝ≥0) :
    HasLaw (wienerVectorEval t) (radialGaussianVectorMeasure t) wienerTripleMeasure :=
  wienerTriple_vectorEval_hasLaw t

/-- Deterministic-time vector Markov identity retains arbitrary measurable tests of the entire stopped past. -/
theorem wienerVector_deterministic_markov_lintegral (s dt : ℝ≥0)
    (G : BrownianTriple × EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ V, G (wienerTripleStop s V, wienerVectorEval (s + dt) V) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ w, G (wienerTripleStop s V, wienerVectorEval s V + w)
        ∂radialGaussianVectorMeasure dt ∂wienerTripleMeasure := by
  let F := fun p : BrownianTriple × BrownianTriple =>
    G (p.1, wienerVectorEval s p.1 + wienerVectorEval dt p.2)
  have hF : Measurable F := hG.comp (measurable_fst.prodMk
    (((measurable_wienerVectorEval s).comp measurable_fst).add
      ((measurable_wienerVectorEval dt).comp measurable_snd)))
  have h := wienerTriple_deterministic_restart_lintegral s F hF
  simp only [F, wienerVectorEval_stop, wienerVectorEval_shift_add] at h
  rw [h]
  apply lintegral_congr
  intro V
  rw [← (wienerVectorEval_hasLaw dt).map_eq,
    lintegral_map (show Measurable (fun w => G (wienerTripleStop s V, wienerVectorEval s V + w)) from
      hG.comp (measurable_const.prodMk (measurable_const.add measurable_id)))
      (measurable_wienerVectorEval dt)]

/-- A positive-time Gaussian vector is nonzero almost surely under the actual Wiener source. -/
theorem wienerVectorEval_ne_zero_ae (s : ℝ≥0) (hs : 0 < s) :
    ∀ᵐ V ∂wienerTripleMeasure, wienerVectorEval s V ≠ 0 := by
  apply (ae_map_iff (measurable_wienerVectorEval s).aemeasurable
    (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin 3))).compl).mp
  rw [(wienerVectorEval_hasLaw s).map_eq, ae_iff]
  simp only [not_not, mem_singleton_iff]
  change radialGaussianVectorMeasure s {0} = 0
  rw [radialGaussianVectorMeasure_eq_withDensity s hs]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton _)

/-- Radial deterministic-time Markov identity with arbitrary measurable tests of the entire stopped past. -/
theorem wienerRadial_deterministic_markov_lintegral (s : ℝ≥0) (hs : 0 < s)
    (dt : ℝ≥0) (ht : 0 < dt) (G : BrownianTriple × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ V, G (wienerTripleStop s V, ‖wienerVectorEval (s + dt) V‖) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ y, G (wienerTripleStop s V, y) *
        ENNReal.ofReal (conditionedPositiveTransitionDensity 0 dt ‖wienerVectorEval s V‖ y)
          ∂volume ∂wienerTripleMeasure := by
  have hGnorm : Measurable (fun p : BrownianTriple × EuclideanSpace ℝ (Fin 3) => G (p.1, ‖p.2‖)) :=
    hG.comp (measurable_fst.prodMk measurable_snd.norm)
  rw [wienerVector_deterministic_markov_lintegral s dt _ hGnorm]
  apply lintegral_congr_ae
  filter_upwards [wienerVectorEval_ne_zero_ae s hs] with V hV
  exact lintegral_radialGaussian_transition (wienerVectorEval s V) hV dt ht
    (fun y => G (wienerTripleStop s V, y)) (hG.comp (measurable_const.prodMk measurable_id))

/-- The same Markov identity in the existing total real-state radial kernel. -/
theorem wienerRadial_deterministic_markov_kernel (s : ℝ≥0) (hs : 0 < s)
    (dt : ℝ≥0) (ht : 0 < dt) (G : BrownianTriple × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ V, G (wienerTripleStop s V, ‖wienerVectorEval (s + dt) V‖) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ y, G (wienerTripleStop s V, y)
        ∂conditionedPositiveTransitionKernelOnReal 0 dt ‖wienerVectorEval s V‖ ∂wienerTripleMeasure := by
  rw [wienerRadial_deterministic_markov_lintegral s hs dt ht G hG]
  apply lintegral_congr_ae
  filter_upwards [wienerVectorEval_ne_zero_ae s hs] with V hV
  rw [conditionedPositiveTransitionKernelOnReal_apply_of_pos (norm_pos_iff.mpr hV),
    conditionedPositiveTransitionMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (show Measurable (fun y : ℝ => ENNReal.ofReal (conditionedPositiveTransitionDensity 0 dt ‖wienerVectorEval s V‖ y)) from
        ((measurable_conditionedPositiveTransitionDensity_pair 0 dt).comp
          (measurable_const.prodMk measurable_id)).ennreal_ofReal)
      (show Measurable (fun y => G (wienerTripleStop s V, y)) from
        hG.comp (measurable_const.prodMk measurable_id))]
  apply lintegral_congr
  intro y
  exact mul_comm _ _

/-- Finite radial observations of the actual Wiener triple. -/
noncomputable def wienerRadialSamples {n : ℕ} (times : Fin n → ℝ≥0) (V : BrownianTriple) : Fin n → ℝ :=
  fun i => ‖wienerVectorEval (times i) V‖

/-- Actual radial skeleton observations are measurable on the original source space. -/
theorem measurable_wienerRadialSamples {n : ℕ} (times : Fin n → ℝ≥0) :
    Measurable (wienerRadialSamples times) :=
  measurable_pi_iff.mpr fun i => (measurable_wienerVectorEval (times i)).norm

/-- Every observation before a stop is retained exactly in the stopped coordinate paths. -/
theorem wienerVectorEval_stop_of_le (s t : ℝ≥0) (ht : t ≤ s) (V : BrownianTriple) :
    wienerVectorEval t (wienerTripleStop s V) = wienerVectorEval t V := by
  apply WithLp.ofLp_injective 2
  funext i
  change V i (min t s) = V i t
  rw [min_eq_left ht]

/-- Finite radial histories before a deterministic time are unchanged by stopping. -/
theorem wienerRadialSamples_stop {n : ℕ} (times : Fin n → ℝ≥0) (s : ℝ≥0)
    (ht : ∀ i, times i ≤ s) (V : BrownianTriple) :
    wienerRadialSamples times (wienerTripleStop s V) = wienerRadialSamples times V := by
  funext i
  exact congrArg norm (wienerVectorEval_stop_of_le s (times i) (ht i) V)

/-- The exact radial Markov identity for every finite actual history before the current time. -/
theorem wienerRadial_samples_markov_lintegral {n : ℕ} (times : Fin n → ℝ≥0)
    (s : ℝ≥0) (hs : 0 < s) (htimes : ∀ i, times i ≤ s) (dt : ℝ≥0) (ht : 0 < dt)
    (F : (Fin n → ℝ) × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (wienerRadialSamples times V, ‖wienerVectorEval (s + dt) V‖) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ y, F (wienerRadialSamples times V, y) *
        ENNReal.ofReal (conditionedPositiveTransitionDensity 0 dt ‖wienerVectorEval s V‖ y)
          ∂volume ∂wienerTripleMeasure := by
  have hG : Measurable (fun p : BrownianTriple × ℝ => F (wienerRadialSamples times p.1, p.2)) :=
    hF.comp (((measurable_wienerRadialSamples times).comp measurable_fst).prodMk measurable_snd)
  have h := wienerRadial_deterministic_markov_lintegral s hs dt ht _ hG
  simpa only [wienerRadialSamples_stop times s htimes] using h

/-- Markov splitting remains valid for any measurable function of the stopped past. -/
theorem wienerRadial_pastObservable_markov_lintegral {E : Type*} [MeasurableSpace E]
    (X : BrownianTriple → E) (hX : Measurable X) (s : ℝ≥0) (hs : 0 < s)
    (hstop : ∀ V, X (wienerTripleStop s V) = X V) (dt : ℝ≥0) (ht : 0 < dt)
    (F : E × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (X V, ‖wienerVectorEval (s + dt) V‖) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ y, F (X V, y)
        ∂conditionedPositiveTransitionKernelOnReal 0 dt ‖wienerVectorEval s V‖ ∂wienerTripleMeasure := by
  have hG : Measurable (fun p : BrownianTriple × ℝ => F (X p.1, p.2)) :=
    hF.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have h := wienerRadial_deterministic_markov_kernel s hs dt ht _ hG
  simpa only [hstop] using h

/-- The full radial joint law from any sufficient measurable stopped-past observable. -/
theorem wienerRadial_pastObservable_joint_map {E : Type*} [MeasurableSpace E]
    (X : BrownianTriple → E) (hX : Measurable X) (r : E → ℝ) (hr : Measurable r)
    (s : ℝ≥0) (hs : 0 < s) (hstop : ∀ V, X (wienerTripleStop s V) = X V)
    (hradius : ∀ V, r (X V) = ‖wienerVectorEval s V‖) (dt : ℝ≥0) (ht : 0 < dt) :
    wienerTripleMeasure.map (fun V => (X V, ‖wienerVectorEval (s + dt) V‖)) =
      (wienerTripleMeasure.map X) ⊗ₘ (conditionedPositiveTransitionKernelOnReal 0 dt).comap r hr := by
  let _ := isMarkovKernel_conditionedPositiveTransitionKernelOnReal 0 dt (le_refl 0) ht
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (hX.prodMk (measurable_wienerVectorEval (s + dt)).norm),
    wienerRadial_pastObservable_markov_lintegral X hX s hs hstop dt ht F hF,
    Measure.lintegral_compProd hF]
  have hm : Measurable (fun x => ∫⁻ y, F (x, y)
      ∂(conditionedPositiveTransitionKernelOnReal 0 dt).comap r hr x) :=
    hF.lintegral_kernel_prod_right'
  rw [lintegral_map hm hX]
  simp only [Kernel.comap_apply, hradius]

/-- The vector Markov identity for any measurable observable of the stopped past. -/
theorem wienerVector_pastObservable_markov_lintegral {E : Type*} [MeasurableSpace E]
    (X : BrownianTriple → E) (hX : Measurable X) (s dt : ℝ≥0)
    (hstop : ∀ V, X (wienerTripleStop s V) = X V)
    (F : E × EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (X V, wienerVectorEval (s + dt) V) ∂wienerTripleMeasure) =
      ∫⁻ V, ∫⁻ w, F (X V, wienerVectorEval s V + w)
        ∂radialGaussianVectorMeasure dt ∂wienerTripleMeasure := by
  have hG : Measurable (fun p : BrownianTriple × EuclideanSpace ℝ (Fin 3) => F (X p.1, p.2)) :=
    hF.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have h := wienerVector_deterministic_markov_lintegral s dt _ hG
  simpa only [hstop] using h


/-- Appending the next radial observation gives the exact finite-history Markov measure. -/
theorem wienerRadial_samples_next_joint_map {n : ℕ} (times : Fin (n + 1) → ℝ≥0)
    (s : ℝ≥0) (hs : 0 < s) (htimes : ∀ i, times i ≤ s)
    (hlast : times (Fin.last n) = s) (dt : ℝ≥0) (ht : 0 < dt) :
    wienerTripleMeasure.map (fun V => (wienerRadialSamples times V, ‖wienerVectorEval (s + dt) V‖)) =
      (wienerTripleMeasure.map (wienerRadialSamples times)) ⊗ₘ
        (conditionedPositiveTransitionKernelOnReal 0 dt).comap
          (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) := by
  apply wienerRadial_pastObservable_joint_map (wienerRadialSamples times)
    (measurable_wienerRadialSamples times)
    (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) s hs
    (wienerRadialSamples_stop times s htimes)
  · intro V
    simp only [wienerRadialSamples, hlast]
  · exact ht


/-- Initial radial value has the exact Maxwell entrance measure. -/
theorem wienerRadialEval_map (t : ℝ≥0) (ht : 0 < t) :
    wienerTripleMeasure.map (fun V => ‖wienerVectorEval t V‖) = conditionedPositiveEntranceMeasure 0 t := by
  have h := rogersPitmanVectorAt_norm_hasLaw 0 (le_refl 0) t ht
  have heq : (fun V : BrownianTriple => ‖rogersPitmanVectorAt 0 V t‖) =
      (fun V => ‖wienerVectorEval t V‖) := by
    funext V
    congr 1
    apply WithLp.ofLp_injective 2
    funext i
    simp [rogersPitmanVectorAt, wienerVectorEval]
  rw [heq] at h
  exact h.map_eq


/-- The whole shifted Wiener triple retains the unconditional source law. -/
theorem wienerTripleShift_map (s : ℝ≥0) :
    wienerTripleMeasure.map (wienerTripleShift s) = wienerTripleMeasure := by
  have h := congrArg (fun μ : Measure (BrownianTriple × BrownianTriple) => μ.map Prod.snd)
    (wienerTriple_deterministic_restart_joint_map s)
  have hprob : IsProbabilityMeasure (wienerTripleMeasure.map (wienerTripleStop s)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_wienerTripleStop s).aemeasurable).mpr inferInstance
  let _ := hprob
  rw [Measure.map_map measurable_snd ((measurable_wienerTripleStop s).prodMk (measurable_wienerTripleShift s)),
    Measure.map_snd_prod] at h
  simpa only [Function.comp_def, measure_univ, one_smul] using h



/-- Every actual restarted coordinate starts at zero, samplewise. -/
theorem wienerTripleShift_zero (s : ℝ≥0) (V : BrownianTriple) (i : Fin 3) :
    wienerTripleShift s V i 0 = 0 := by
  change V i (s + 0) - V i s = 0
  rw [add_zero, sub_self]


end DOZZ.Proofs
