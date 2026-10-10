/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.RadialProfiles
public import DOZZ.Brownian.ConditionedKernelShiftedRatio
public import DOZZ.Brownian.ConditionedFDDUniqueness

/-!
# Terminal tilt and the literal Doob density

The angular factor telescopes across the transition chain. Equality on measurable
rectangles then identifies the entire actual Rogers--Pitman skeleton.
Nonpositive state boundaries and the continuous zero-drift endpoint are retained throughout.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- The angular factor is strictly positive for nonnegative drift at positive radius. -/
theorem radialAngularFactor_pos {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    0 < radialAngularFactor a r := by
  by_cases h0 : a = 0
  · rw [h0, radialAngularFactor_zero]; exact zero_lt_one
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rw [radialAngularFactor_of_ne_zero a r h0 hr.ne']
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hap hr)) (mul_pos hap hr)

/-- Entrance densities differ from the Maxwell law by the terminal radial likelihood. -/
theorem conditionedPositiveEntranceDensity_radial_tilt {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (r : ℝ) :
    conditionedPositiveEntranceDensity a t r = conditionedPositiveEntranceDensity 0 t r *
      (Real.exp (-a ^ 2 * t / 2) * radialAngularFactor a r) := by
  by_cases h0 : a = 0
  · subst a
    simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_mul, zero_div,
      Real.exp_zero, radialAngularFactor_zero, mul_one]
  · by_cases hr : 0 < r
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
      rw [entranceDensity_eq_radialGaussian hap ht hr,
        entranceDensity_zero_eq_radialGaussian ht hr,
        radialAngularFactor_of_ne_zero a r h0 hr.ne',
        show -r ^ 2 / (2 * t) - a ^ 2 * t / 2 =
          -r ^ 2 / (2 * t) + (-a ^ 2 * t / 2) by ring, Real.exp_add]
      field_simp
    · simp only [conditionedPositiveEntranceDensity, ha, ht, hr, and_false, ite_false, zero_mul]

/-- Positive-start Doob transitions differ by the angular ratio and Gaussian time factor. -/
theorem conditionedPositiveTransitionDensity_radial_tilt {a t x : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (hx : 0 < x) (y : ℝ) :
    conditionedPositiveTransitionDensity a t x y =
      conditionedPositiveTransitionDensity 0 t x y * Real.exp (-a ^ 2 * t / 2) *
        radialAngularFactor a y / radialAngularFactor a x := by
  by_cases h0 : a = 0
  · subst a
    simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_mul, zero_div,
      Real.exp_zero, radialAngularFactor_zero, mul_one, div_one]
  · by_cases hy : 0 < y
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
      have hsx : Real.sinh (a * x) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hap hx)).ne'
      have hroot : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
      rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hap ht hx hy,
        conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy,
        radialAngularFactor_of_ne_zero a x h0 hx.ne',
        radialAngularFactor_of_ne_zero a y h0 hy.ne',
        show -a ^ 2 * t / 2 - x ^ 2 / (2 * t) =
          (-a ^ 2 * t / 2) + (-x ^ 2 / (2 * t)) by ring, Real.exp_add]
      have harg : x / t * y = x * y / t := by ring
      rw [harg]
      field_simp [hroot, hsx, h0, hx.ne', hy.ne']
    · simp only [conditionedPositiveTransitionDensity, ha, ht, hx, hy, and_false, ite_false,
        zero_mul, zero_div]

/-- A nonpositive final state kills every literal positive finite-dimensional density. -/
theorem conditionedPositiveFDDDensity_last_nonpos (a : ℝ) (n : ℕ)
    (times x : Fin (n + 1) → ℝ) (hx : x (Fin.last n) ≤ 0) :
    conditionedPositiveFDDDensity a (List.ofFn times) (List.ofFn x) = 0 := by
  cases n with
  | zero =>
    rw [List.ofFn_succ (f := times), List.ofFn_succ (f := x)]
    simp only [List.ofFn_zero, conditionedPositiveFDDDensity, conditionedPositiveTimeChainDensity,
      mul_one, Fin.last_zero] at *
    simp only [conditionedPositiveEntranceDensity, not_lt.mpr hx, and_false, ite_false]
  | succ n =>
    rw [conditionedPositiveFDDDensity_last_split a n times x]
    simp only [conditionedPositiveTransitionDensity, not_lt.mpr hx, and_false, ite_false, mul_zero]

/-- The complete real-valued skeleton density has precisely one terminal tilt. -/
theorem conditionedPositiveFDDDensity_radial_tilt : ∀ (n : ℕ) (a : ℝ)
    (times : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ),
    0 ≤ a → (∀ i, 0 < times i) → StrictMono times →
    conditionedPositiveFDDDensity a (List.ofFn times) (List.ofFn x) =
      conditionedPositiveFDDDensity 0 (List.ofFn times) (List.ofFn x) *
        (Real.exp (-a ^ 2 * times (Fin.last n) / 2) * radialAngularFactor a (x (Fin.last n))) := by
  intro n
  induction n with
  | zero =>
    intro a times x ha hpos hmono
    rw [List.ofFn_succ (f := times), List.ofFn_succ (f := x)]
    simp only [List.ofFn_zero, conditionedPositiveFDDDensity, conditionedPositiveTimeChainDensity,
      mul_one, Fin.last_zero]
    exact conditionedPositiveEntranceDensity_radial_tilt ha (hpos 0) (x 0)
  | succ n ih =>
    intro a times x ha hpos hmono
    have ht := sub_pos.mpr (hmono (Fin.castSucc_lt_last (Fin.last n)))
    rw [conditionedPositiveFDDDensity_last_split a n times x,
      conditionedPositiveFDDDensity_last_split 0 n times x]
    by_cases hx : 0 < x ((Fin.last n).castSucc)
    · rw [conditionedPositiveTransitionDensity_radial_tilt ha ht hx]
      have hpast := ih a (Fin.init times) (Fin.init x) ha (fun i => hpos i.castSucc)
        (hmono.comp Fin.strictMono_castSucc)
      dsimp only [Fin.init] at hpast
      rw [hpast]
      have hcancel : radialAngularFactor a (x (Fin.last n).castSucc) ≠ 0 :=
        (radialAngularFactor_pos ha hx).ne'
      have hexp : Real.exp (-a ^ 2 * times (Fin.last n).castSucc / 2) *
          Real.exp (-a ^ 2 * (times (Fin.last (n + 1)) - times (Fin.last n).castSucc) / 2) =
            Real.exp (-a ^ 2 * times (Fin.last (n + 1)) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      field_simp [hcancel]
      have heq := congrArg (fun r : ℝ =>
        conditionedPositiveFDDDensity 0 (List.ofFn (Fin.init times)) (List.ofFn (Fin.init x)) *
          conditionedPositiveTransitionDensity 0
            (times (Fin.last (n + 1)) - times (Fin.last n).castSucc)
            (x (Fin.last n).castSucc) (x (Fin.last (n + 1))) *
          radialAngularFactor a (x (Fin.last (n + 1))) * r) hexp
      convert heq using 1 <;> ring_nf
    · have hn := le_of_not_gt hx
      rw [conditionedPositiveFDDDensity_last_nonpos a n (Fin.init times) (Fin.init x) hn,
        conditionedPositiveFDDDensity_last_nonpos 0 n (Fin.init times) (Fin.init x) hn]
      simp only [zero_mul]

/-- Applying the `max 0` convention preserves the terminal-tilt formula. -/
theorem conditionedPositiveFDDVectorDensity_radial_tilt (n : ℕ) (a : ℝ)
    (times : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ)
    (ha : 0 ≤ a) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    conditionedPositiveFDDVectorDensity a times x =
      conditionedPositiveFDDVectorDensity 0 times x *
        radialTerminalLikelihood a (times (Fin.last n)) (x (Fin.last n)) := by
  have hna := conditionedPositiveFDDDensity_nonneg ha (List.ofFn times) (List.ofFn x) (by simp)
  have hn0 := conditionedPositiveFDDDensity_nonneg (le_refl 0) (List.ofFn times) (List.ofFn x) (by simp)
  simp only [conditionedPositiveFDDVectorDensity, max_eq_right hna, max_eq_right hn0]
  rw [conditionedPositiveFDDDensity_radial_tilt n a times x ha hpos hmono,
    ENNReal.ofReal_mul hn0]
  by_cases hx : 0 < x (Fin.last n)
  · rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  · rw [conditionedPositiveFDDDensity_last_nonpos 0 n times x (le_of_not_gt hx)]
    simp only [ENNReal.ofReal_zero, zero_mul]

/-- Finite-dimensional measures are determined by all products of measurable nonnegative tests. -/
theorem finiteRealVector_measure_eq_of_product_tests (n : ℕ)
    (μ ν : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (h : ∀ (f : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
      (∫⁻ x, ∏ i, f i (x i) ∂μ) = ∫⁻ x, ∏ i, f i (x i) ∂ν) : μ = ν := by
  let C := fun _ : Fin n => {S : Set ℝ | MeasurableSet S}
  have hspan : ∀ i, IsCountablySpanning (C i) := fun _ =>
    ⟨fun _ => univ, (fun _ => by change MeasurableSet (univ : Set ℝ); exact MeasurableSet.univ),
      by ext x; simp only [mem_iUnion, mem_univ, exists_const]⟩
  have hgen : (inferInstance : MeasurableSpace (Fin n → ℝ)) =
      MeasurableSpace.generateFrom (univ.pi '' univ.pi C) :=
    (generateFrom_eq_pi (fun _ => MeasurableSpace.generateFrom_measurableSet) hspan).symm
  have huniv := h (fun _ _ => 1) (fun _ => measurable_const)
  simp only [Finset.prod_const_one, lintegral_one] at huniv
  apply ext_of_generate_finite _ hgen (IsPiSystem.pi fun _ => MeasurableSpace.isPiSystem_measurableSet) ?_ huniv
  rintro S ⟨s, hs, rfl⟩
  have hms : ∀ i, MeasurableSet (s i) := mem_univ_pi.mp hs
  have htest := h (fun i => (s i).indicator (fun _ => 1))
    (fun i => measurable_const.indicator (hms i))
  have hind (x : Fin n → ℝ) : (∏ i, (s i).indicator (fun _ => (1 : ℝ≥0∞)) (x i)) =
      (univ.pi s).indicator (fun _ => 1) x := by
    by_cases hx : ∀ i, x i ∈ s i
    · rw [indicator_of_mem (mem_univ_pi.mpr hx)]
      simp only [indicator_of_mem (hx _), Finset.prod_const_one]
    · rw [indicator_of_notMem (fun hx' => hx (mem_univ_pi.mp hx'))]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)
  simp_rw [hind] at htest
  have hmS : MeasurableSet (univ.pi s) := MeasurableSet.pi (to_countable _) (fun i _ => hms i)
  simpa only [lintegral_indicator hmS, setLIntegral_one] using htest

/-- Every full actual radial skeleton has the literal positive density at every drift. -/
theorem rogersPitman_radial_fdd_positive (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    wienerTripleMeasure.map (fun V i => ‖rogersPitmanVectorAt a V (times i)‖) =
      radialSkeletonDensityMeasure a (fun i => (times i : ℝ)) := by
  have hm : Measurable (fun V : BrownianTriple => fun i => ‖rogersPitmanVectorAt a V (times i)‖) :=
    measurable_pi_iff.mpr fun i => (ContinuousMap.measurable_eval (times i)).comp (measurable_rogersPitmanPath a)
  let _ : IsProbabilityMeasure (wienerTripleMeasure.map
      (fun V i => ‖rogersPitmanVectorAt a V (times i)‖)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply finiteRealVector_measure_eq_of_product_tests
  intro f hf
  have hprod : Measurable (fun x : Fin (n + 1) → ℝ => ∏ i, f i (x i)) :=
    Finset.measurable_prod Finset.univ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [lintegral_map hprod hm,
    rogersPitman_radial_product_terminal_likelihood n a times f hpos hmono hf]
  have htest : Measurable (fun x : Fin (n + 1) → ℝ => (∏ i, f i (x i)) *
      radialTerminalLikelihood a (times (Fin.last n)) (x (Fin.last n))) :=
    hprod.mul ((measurable_radialTerminalLikelihood a _).comp (measurable_pi_apply _))
  have h0 := lintegral_wienerRadialSamples_zeroDrift n times hpos hmono _ htest
  change (∫⁻ V, (fun x : Fin (n + 1) → ℝ => (∏ i, f i (x i)) *
    radialTerminalLikelihood a (times (Fin.last n)) (x (Fin.last n)))
      (wienerRadialSamples times V) ∂wienerTripleMeasure) = _
  rw [h0, radialSkeletonDensityMeasure, lintegral_withDensity_eq_lintegral_mul volume
    (measurable_conditionedPositiveFDDVectorDensity a _) hprod]
  apply lintegral_congr
  intro x
  dsimp only [Pi.mul_apply]
  have hrealMono : StrictMono (fun i => (times i : ℝ)) := fun i j hij => hmono hij
  have hd := conditionedPositiveFDDVectorDensity_radial_tilt n a (fun i => (times i : ℝ)) x ha
    (fun i => show 0 < (times i : ℝ) from hpos i) hrealMono
  rw [hd]
  ac_rfl

/-- The whole positive Rogers--Pitman path law has every exact finite-dimensional density. -/
theorem rogersPitmanWienerMeasure_fdd (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    (rogersPitmanWienerMeasure a).map (fun p i => p (times i)) =
      radialSkeletonDensityMeasure a (fun i => (times i : ℝ)) := by
  have hm : Measurable (fun p : BrownianPath => fun i => p (times i)) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval _
  rw [rogersPitmanWienerMeasure, rogersPitmanEntranceMeasure,
    Measure.map_map hm (measurable_rogersPitmanPath a)]
  exact rogersPitman_radial_fdd_positive n a ha times hpos hmono

/-- Reflection identifies the entire actual negative Rogers--Pitman skeleton with the density
`DOZZ.negativeConditionedFDDDensity`. -/
theorem rogersPitman_radial_fdd_identification (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    wienerTripleMeasure.map (fun V i => -‖rogersPitmanVectorAt a V (times i)‖) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity (fun x => ENNReal.ofReal (max 0
        (negativeConditionedFDDDensity a (List.ofFn fun i => (times i : ℝ)) (List.ofFn x)))) := by
  let e := conditionedCoordinateNegEquiv (Fin (n + 1))
  have hm : Measurable (fun V : BrownianTriple => fun i => ‖rogersPitmanVectorAt a V (times i)‖) :=
    measurable_pi_iff.mpr fun i => (ContinuousMap.measurable_eval _).comp (measurable_rogersPitmanPath a)
  have h := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) => μ.map e)
    (rogersPitman_radial_fdd_positive n a ha times hpos hmono)
  rw [Measure.map_map e.measurable hm, radialSkeletonDensityMeasure_map_neg] at h
  exact h

/-- Every negative radial candidate has the literal finite observation law. -/
theorem negativeRogersPitmanWienerMeasure_fdd (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    (negativeRogersPitmanWienerMeasure a).map (fun p i => p (times i)) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity (fun x => ENNReal.ofReal (max 0
        (negativeConditionedFDDDensity a (List.ofFn fun i => (times i : ℝ)) (List.ofFn x)))) := by
  have hm : Measurable (fun p : BrownianPath => fun i => p (times i)) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval _
  rw [negativeRogersPitmanWienerMeasure, negativeRogersPitmanEntranceMeasure,
    Measure.map_map hm (measurable_negativeRogersPitmanPath a)]
  exact rogersPitman_radial_fdd_identification n a ha times hpos hmono

/-- Unconditional realization of the full negative conditioned law at every nonnegative drift. -/
theorem negativeRogersPitmanWienerMeasure_isConditioned (a : ℝ) (ha : 0 ≤ a) :
    IsNegativeConditionedBrownianLaw a (negativeRogersPitmanWienerMeasure a) := by
  refine ⟨ha, inferInstance, negativeRogersPitmanWienerMeasure_zero_ae a, ?_⟩
  intro n hn times hpos hmono
  cases n with
  | zero => omega
  | succ n => exact negativeRogersPitmanWienerMeasure_fdd n a ha times (fun i => hpos i) hmono

/-- The actual GFF-derived Wiener construction supplies conditioned entrance existence for every drift. -/
theorem exists_negativeConditionedBrownianLaw_of_wiener (a : ℝ) (ha : 0 ≤ a) :
    ∃ Q : Measure BrownianPath, IsNegativeConditionedBrownianLaw a Q :=
  ⟨negativeRogersPitmanWienerMeasure a, negativeRogersPitmanWienerMeasure_isConditioned a ha⟩

/-- Every ordered positive skeleton density is a probability measure at every nonnegative drift. -/
theorem radialSkeletonDensityMeasure_isProbability (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    IsProbabilityMeasure (radialSkeletonDensityMeasure a (fun i => (times i : ℝ))) := by
  rw [← rogersPitmanWienerMeasure_fdd n a ha times hpos hmono]
  have hm : Measurable (fun p : BrownianPath => fun i => p (times i)) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval _
  exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance




/-- The actual drifted skeleton is the zero-drift skeleton tilted only at its terminal radius. -/
theorem radialSkeletonDensityMeasure_terminal_tilt (n : ℕ) (a : ℝ)
    (times : Fin (n + 1) → ℝ) (ha : 0 ≤ a)
    (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    radialSkeletonDensityMeasure a times =
      (radialSkeletonDensityMeasure 0 times).withDensity
        (fun x => radialTerminalLikelihood a (times (Fin.last n)) (x (Fin.last n))) := by
  rw [radialSkeletonDensityMeasure, radialSkeletonDensityMeasure,
    ← withDensity_mul volume (measurable_conditionedPositiveFDDVectorDensity 0 times)
      (show Measurable (fun x : Fin (n + 1) → ℝ =>
        radialTerminalLikelihood a (times (Fin.last n)) (x (Fin.last n))) from
          (measurable_radialTerminalLikelihood a _).comp (measurable_pi_apply _))]
  apply withDensity_congr_ae
  exact ae_of_all _ fun x => conditionedPositiveFDDVectorDensity_radial_tilt n a times x ha hpos hmono





/-- Every conditioned entrance law agrees with the concrete unconditional Wiener realization.
This identifies the whole continuous-path law, including all measurable future events. -/
theorem negativeConditionedBrownianLaw_eq_wiener (a : ℝ) {Q : Measure BrownianPath}
    (hQ : IsNegativeConditionedBrownianLaw a Q) : Q = negativeRogersPitmanWienerMeasure a := by
  exact isNegativeConditionedBrownianLaw_eq a hQ
    (negativeRogersPitmanWienerMeasure_isConditioned a hQ.1)

/-- The concrete Wiener realization and whole-path FDD uniqueness give the entrance existence
statement `DOZZ.negativeConditionedBrownianLaw_exists` at every nonnegative drift, including
zero. -/
theorem negativeConditionedBrownianLaw_exists (ν : ℝ) (hν : 0 ≤ ν) :
    ∃! P : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν P := by
  exact existsUnique_negativeConditionedBrownianLaw_of_exists ν
    (exists_negativeConditionedBrownianLaw_of_wiener ν hν)

end DOZZ.Proofs
