/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.VectorMarkov

/-!
# Exact finite radial skeleton densities

Factor the literal positive finite-dimensional density at its final observation. Lebesgue measure
is transported by the explicit last-coordinate split, so every induction step retains all state and
time operands of the transition density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Split a finite real vector into its initial block and final coordinate. -/
noncomputable def radialSkeletonLastSplit (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).trans
    (MeasurableEquiv.prodComm : ℝ × (Fin n → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ))

/-- Splitting the last coordinate preserves literal Lebesgue volume. -/
theorem radialSkeletonLastSplit_measurePreserving (n : ℕ) :
    MeasurePreserving (radialSkeletonLastSplit n) := by
  have hswap : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
  exact hswap.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))

/-- Its initial block is the actual `Fin.init`, without reordering observations. -/
theorem radialSkeletonLastSplit_fst (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (radialSkeletonLastSplit n x).1 = Fin.init x := by
  funext i
  simp [radialSkeletonLastSplit]
  rfl

/-- Its final coordinate is the actual last observation. -/
theorem radialSkeletonLastSplit_snd (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (radialSkeletonLastSplit n x).2 = x (Fin.last n) := rfl

/-- The literal finite-dimensional density measure in positive coordinates. -/
noncomputable def radialSkeletonDensityMeasure (a : ℝ) {n : ℕ} (times : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (conditionedPositiveFDDVectorDensity a times)

/-- Last-coordinate factorization of the positive density before applying `ofReal`. -/
theorem conditionedPositiveFDDDensity_last_split (a : ℝ) (n : ℕ)
    (times x : Fin (n + 2) → ℝ) :
    conditionedPositiveFDDDensity a (List.ofFn times) (List.ofFn x) =
      conditionedPositiveFDDDensity a (List.ofFn (Fin.init times)) (List.ofFn (Fin.init x)) *
        conditionedPositiveTransitionDensity a (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc))
          (x ((Fin.last n).castSucc)) (x (Fin.last (n + 1))) := by
  rw [List.ofFn_succ' times, List.ofFn_succ' x]
  simp only [List.concat_eq_append]
  change conditionedPositiveFDDDensity a ((List.ofFn (Fin.init times)) ++ [times (Fin.last (n + 1))])
    ((List.ofFn (Fin.init x)) ++ [x (Fin.last (n + 1))]) = _
  rw [List.ofFn_succ (f := Fin.init times), List.ofFn_succ (f := Fin.init x), List.cons_append, List.cons_append]
  rw [conditionedPositiveFDDDensity_append_split a _ _ _ _ _ _ (by simp)]
  rw [conditionedPositiveLastTime_ofFn_tail, conditionedPositiveLastState_ofFn_tail]
  simp only [conditionedPositiveTimeChainDensity, mul_one]
  rfl

/-- Last-coordinate factorization retains the `max 0` convention exactly. -/
theorem conditionedPositiveFDDVectorDensity_last_split (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (times x : Fin (n + 2) → ℝ) :
    conditionedPositiveFDDVectorDensity a times x =
      conditionedPositiveFDDVectorDensity a (Fin.init times) (Fin.init x) *
        ENNReal.ofReal (conditionedPositiveTransitionDensity a
          (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc))
          (x ((Fin.last n).castSucc)) (x (Fin.last (n + 1)))) := by
  have hnonneg := conditionedPositiveFDDDensity_nonneg ha (List.ofFn times) (List.ofFn x) (by simp)
  have hpast := conditionedPositiveFDDDensity_nonneg ha
    (List.ofFn (Fin.init times)) (List.ofFn (Fin.init x)) (by simp)
  rw [conditionedPositiveFDDVectorDensity, max_eq_right hnonneg,
    conditionedPositiveFDDDensity_last_split a n times x,
    ENNReal.ofReal_mul hpast]
  rw [conditionedPositiveFDDVectorDensity, max_eq_right hpast]

/-- Nonnegative transition-density kernel, with zero fibers at nonpositive starts. -/
noncomputable def radialSkeletonTransitionDensityKernel (a dt : ℝ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity
    (fun x y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt x y))

instance isSFiniteKernel_radialSkeletonTransitionDensityKernel (a dt : ℝ) :
    IsSFiniteKernel (radialSkeletonTransitionDensityKernel a dt) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  exact ENNReal.ofReal_ne_top

/-- Every density-kernel fiber is the literal Doob transition-density measure. -/
theorem radialSkeletonTransitionDensityKernel_apply (a dt x : ℝ) :
    radialSkeletonTransitionDensityKernel a dt x = conditionedPositiveTransitionMeasure a dt x := by
  rw [radialSkeletonTransitionDensityKernel, Kernel.withDensity_apply _
    (measurable_conditionedPositiveTransitionDensity_pair a dt).ennreal_ofReal, Kernel.const_apply]
  rfl

/-- Integrating against a fiber preserves the explicit nonnegative transition density. -/
theorem radialSkeletonTransitionDensityKernel_lintegral (a dt x : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y, F y ∂radialSkeletonTransitionDensityKernel a dt x) =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveTransitionDensity a dt x y) := by
  rw [radialSkeletonTransitionDensityKernel_apply, conditionedPositiveTransitionMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (show Measurable (fun y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt x y)) from
        ((measurable_conditionedPositiveTransitionDensity_pair a dt).comp
          (measurable_const.prodMk measurable_id)).ennreal_ofReal) hF]
  apply lintegral_congr
  intro y
  exact mul_comm _ _

/-- Transporting a literal FDD through the last split gives the explicit product-density measure. -/
theorem radialSkeletonDensityMeasure_last_split (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (times : Fin (n + 2) → ℝ) :
    (radialSkeletonDensityMeasure a times).map (radialSkeletonLastSplit (n + 1)) =
      (volume : Measure ((Fin (n + 1) → ℝ) × ℝ)).withDensity (fun p =>
        conditionedPositiveFDDVectorDensity a (Fin.init times) p.1 *
          ENNReal.ofReal (conditionedPositiveTransitionDensity a
            (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc)) (p.1 (Fin.last n)) p.2)) := by
  rw [radialSkeletonDensityMeasure, map_withDensity_of_measurePreserving_equiv
    (radialSkeletonLastSplit (n + 1)) volume volume (radialSkeletonLastSplit_measurePreserving _)
      _ (measurable_conditionedPositiveFDDVectorDensity a times)]
  apply withDensity_congr_ae
  filter_upwards [] with p
  rw [Function.comp_apply, conditionedPositiveFDDVectorDensity_last_split a ha n]
  have hf := radialSkeletonLastSplit_fst (n + 1) ((radialSkeletonLastSplit (n + 1)).symm p)
  have hs := radialSkeletonLastSplit_snd (n + 1) ((radialSkeletonLastSplit (n + 1)).symm p)
  rw [MeasurableEquiv.apply_symm_apply] at hf hs
  have hv := congrFun hf (Fin.last n)
  change p.1 (Fin.last n) = (radialSkeletonLastSplit (n + 1)).symm p ((Fin.last n).castSucc) at hv
  rw [← hf, ← hs, ← hv]

/-- The final FDD factor is an actual composition-product with the literal transition-density kernel. -/
theorem radialSkeletonDensityMeasure_last_compProd (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (times : Fin (n + 2) → ℝ) :
    (radialSkeletonDensityMeasure a times).map (radialSkeletonLastSplit (n + 1)) =
      (radialSkeletonDensityMeasure a (Fin.init times)) ⊗ₘ
        (radialSkeletonTransitionDensityKernel a
          (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc))).comap
            (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) := by
  rw [radialSkeletonDensityMeasure_last_split a ha n times]
  let dt := times (Fin.last (n + 1)) - times ((Fin.last n).castSucc)
  have hm : Measurable (Function.uncurry (fun (x : Fin (n + 1) → ℝ) y =>
      ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (x (Fin.last n)) y))) := by
    change Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (p.1 (Fin.last n)) p.2))
    have hp : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => (p.1 (Fin.last n), p.2)) :=
      ((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk measurable_snd
    exact ((measurable_conditionedPositiveTransitionDensity_pair a dt).comp hp).ennreal_ofReal
  have hk : (radialSkeletonTransitionDensityKernel a dt).comap
      (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) =
      (Kernel.const (Fin (n + 1) → ℝ) (volume : Measure ℝ)).withDensity
        (fun x y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (x (Fin.last n)) y)) := by
    ext x S hS
    rw [Kernel.comap_apply, radialSkeletonTransitionDensityKernel_apply, Kernel.withDensity_apply _ hm,
      Kernel.const_apply]
    rfl
  change _ = (radialSkeletonDensityMeasure a (Fin.init times)) ⊗ₘ
    (radialSkeletonTransitionDensityKernel a dt).comap _ _
  rw [hk, radialSkeletonDensityMeasure]
  have hf : IsSFiniteKernel ((Kernel.const (Fin (n + 1) → ℝ) (volume : Measure ℝ)).withDensity
      (fun x y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (x (Fin.last n)) y))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro x y
    exact ENNReal.ofReal_ne_top
  let _ := hf
  rw [Measure.withDensity_compProd_withDensity
    (measurable_conditionedPositiveFDDVectorDensity a (Fin.init times)) hm,
    Measure.compProd_const, ← Measure.volume_eq_prod]

/-- The actual radial history has the same last-step density-kernel factorization. -/
theorem wienerRadial_samples_next_density_joint_map {n : ℕ} (times : Fin (n + 1) → ℝ≥0)
    (s : ℝ≥0) (hs : 0 < s) (htimes : ∀ i, times i ≤ s)
    (hlast : times (Fin.last n) = s) (dt : ℝ≥0) (ht : 0 < dt) :
    wienerTripleMeasure.map (fun V => (wienerRadialSamples times V, ‖wienerVectorEval (s + dt) V‖)) =
      (wienerTripleMeasure.map (wienerRadialSamples times)) ⊗ₘ
        (radialSkeletonTransitionDensityKernel 0 dt).comap
          (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF ((measurable_wienerRadialSamples times).prodMk (measurable_wienerVectorEval (s + dt)).norm),
    wienerRadial_samples_markov_lintegral times s hs htimes dt ht F hF,
    Measure.lintegral_compProd hF]
  have hm : Measurable (fun x => ∫⁻ y, F (x, y)
      ∂(radialSkeletonTransitionDensityKernel 0 dt).comap
        (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) x) := hF.lintegral_kernel_prod_right'
  rw [lintegral_map hm (measurable_wienerRadialSamples times)]
  apply lintegral_congr
  intro V
  rw [Kernel.comap_apply, radialSkeletonTransitionDensityKernel_lintegral _ _ _ _
    (show Measurable (fun y => F (wienerRadialSamples times V, y)) from
      hF.comp (measurable_const.prodMk measurable_id))]
  simp only [wienerRadialSamples, hlast]

/-- A one-coordinate FDD is exactly the literal entrance measure. -/
theorem radialSkeletonDensityMeasure_one_map (a : ℝ) (ha : 0 ≤ a) (times : Fin 1 → ℝ)
    (ht : 0 < times 0) :
    (radialSkeletonDensityMeasure a times).map (MeasurableEquiv.funUnique (Fin 1) ℝ) =
      conditionedPositiveEntranceMeasure a (times 0) := by
  rw [radialSkeletonDensityMeasure, map_withDensity_of_measurePreserving_equiv
    (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume (volume_preserving_funUnique (Fin 1) ℝ)
      _ (measurable_conditionedPositiveFDDVectorDensity a times), conditionedPositiveEntranceMeasure]
  apply withDensity_congr_ae
  filter_upwards [] with y
  have hn := conditionedPositiveEntranceDensity_nonneg ha ht y
  change ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity a (List.ofFn times)
    (List.ofFn ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm y)))) = _
  simp only [List.ofFn_succ, List.ofFn_zero, conditionedPositiveFDDDensity,
    conditionedPositiveTimeChainDensity, mul_one]
  change ENNReal.ofReal (max 0 (conditionedPositiveEntranceDensity a (times 0) y)) = _
  rw [max_eq_right hn]

/-- The actual Wiener radial skeleton has the full exact zero-drift FDD density. -/
theorem wienerRadialSamples_zeroDrift_fdd : ∀ (n : ℕ) (times : Fin (n + 1) → ℝ≥0),
    (∀ i, 0 < times i) → StrictMono times →
    wienerTripleMeasure.map (wienerRadialSamples times) =
      radialSkeletonDensityMeasure 0 (fun i => (times i : ℝ)) := by
  intro n
  induction n with
  | zero =>
    intro times hpos hmono
    let e := MeasurableEquiv.funUnique (Fin 1) ℝ
    apply e.measurableEmbedding.map_injective
    rw [Measure.map_map e.measurable (measurable_wienerRadialSamples times),
      radialSkeletonDensityMeasure_one_map 0 (le_refl 0) _ (hpos 0)]
    exact wienerRadialEval_map (times 0) (hpos 0)
  | succ n ih =>
    intro times hpos hmono
    let past := Fin.init times
    let s := times ((Fin.last n).castSucc)
    let dt := times (Fin.last (n + 1)) - s
    have hlastlt : s < times (Fin.last (n + 1)) := hmono (Fin.castSucc_lt_last _)
    have hdt : 0 < dt := tsub_pos_iff_lt.mpr hlastlt
    have hs : 0 < s := hpos _
    have hsum : s + dt = times (Fin.last (n + 1)) := add_tsub_cancel_of_le hlastlt.le
    have hpast : ∀ i, past i ≤ s := fun i => hmono.monotone (Fin.strictMono_castSucc.monotone (Fin.le_last i))
    have hmonoPast : StrictMono past := hmono.comp Fin.strictMono_castSucc
    have hprev := ih past (fun i => hpos i.castSucc) hmonoPast
    let e := radialSkeletonLastSplit (n + 1)
    apply e.measurableEmbedding.map_injective
    rw [Measure.map_map e.measurable (measurable_wienerRadialSamples times)]
    have heval : (fun V => e (wienerRadialSamples times V)) =
        (fun V => (wienerRadialSamples past V, ‖wienerVectorEval (s + dt) V‖)) := by
      funext V
      apply Prod.ext
      · rw [radialSkeletonLastSplit_fst]
        rfl
      · rw [radialSkeletonLastSplit_snd, hsum]
        rfl
    change wienerTripleMeasure.map (fun V => e (wienerRadialSamples times V)) = _
    rw [heval, wienerRadial_samples_next_density_joint_map past s hs hpast rfl dt hdt, hprev,
      radialSkeletonDensityMeasure_last_compProd 0 (le_refl 0) n]
    have hcoe : (dt : ℝ) = (times (Fin.last (n + 1)) : ℝ) - (s : ℝ) :=
      NNReal.coe_sub hlastlt.le
    rw [hcoe]
    rfl

/-- Reflection of the literal positive FDD measure is the literal negative FDD measure. -/
theorem radialSkeletonDensityMeasure_map_neg (a : ℝ) {n : ℕ} (times : Fin n → ℝ) :
    (radialSkeletonDensityMeasure a times).map (conditionedCoordinateNegEquiv (Fin n)) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => ENNReal.ofReal (max 0
        (negativeConditionedFDDDensity a (List.ofFn times) (List.ofFn x)))) := by
  let e := conditionedCoordinateNegEquiv (Fin n)
  have hvol : MeasurePreserving e (volume : Measure (Fin n → ℝ)) volume :=
    ⟨e.measurable, map_conditionedCoordinateNegEquiv_volume (Fin n)⟩
  rw [radialSkeletonDensityMeasure, map_withDensity_of_measurePreserving_equiv e volume volume hvol
    _ (measurable_conditionedPositiveFDDVectorDensity a times)]
  apply withDensity_congr_ae
  filter_upwards [] with x
  change ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity a (List.ofFn times)
    (List.ofFn fun i => -x i))) = _
  have h := negativeConditionedFDDDensity_reflect a (List.ofFn times) (List.ofFn fun i => -x i)
  simp only [List.map_ofFn, Function.comp_def, neg_neg] at h
  rw [← h]

/-- The Rogers--Pitman vector at zero drift is exactly the actual Wiener vector. -/
theorem rogersPitmanVectorAt_zero_eq_wienerVectorEval (V : BrownianTriple) (t : ℝ≥0) :
    rogersPitmanVectorAt 0 V t = wienerVectorEval t V := by
  apply WithLp.ofLp_injective 2
  funext i
  simp [rogersPitmanVectorAt, wienerVectorEval]

/-- The zero-drift radial path evaluations are the actual positive Wiener-vector skeleton. -/
theorem rogersPitmanWienerMeasure_zero_fdd (n : ℕ) (times : Fin (n + 1) → ℝ≥0)
    (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    (rogersPitmanWienerMeasure 0).map (fun p i => p (times i)) =
      radialSkeletonDensityMeasure 0 (fun i => (times i : ℝ)) := by
  have hm : Measurable (fun p : BrownianPath => fun i => p (times i)) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval _
  rw [rogersPitmanWienerMeasure, rogersPitmanEntranceMeasure,
    Measure.map_map hm (measurable_rogersPitmanPath 0)]
  have heq : (fun V : BrownianTriple => fun i => rogersPitmanPath 0 V (times i)) =
      wienerRadialSamples times := by
    funext V i
    change ‖rogersPitmanVectorAt 0 V (times i)‖ = ‖wienerVectorEval (times i) V‖
    rw [rogersPitmanVectorAt_zero_eq_wienerVectorEval]
  change wienerTripleMeasure.map (fun V i => rogersPitmanPath 0 V (times i)) = _
  rw [heq]
  exact wienerRadialSamples_zeroDrift_fdd n times hpos hmono

/-- Actual negative zero-drift radial paths have every finite-dimensional density. -/
theorem negativeRogersPitmanWienerMeasure_zero_fdd (n : ℕ) (times : Fin (n + 1) → ℝ≥0)
    (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    (negativeRogersPitmanWienerMeasure 0).map (fun p i => p (times i)) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity (fun x => ENNReal.ofReal (max 0
        (negativeConditionedFDDDensity 0 (List.ofFn fun i => (times i : ℝ)) (List.ofFn x)))) := by
  let e := conditionedCoordinateNegEquiv (Fin (n + 1))
  have hm : Measurable (fun p : BrownianPath => fun i => p (times i)) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval _
  have heq : (negativeRogersPitmanWienerMeasure 0).map (fun p i => p (times i)) =
      ((rogersPitmanWienerMeasure 0).map (fun p i => p (times i))).map e := by
    rw [negativeRogersPitmanWienerMeasure, negativeRogersPitmanEntranceMeasure,
      rogersPitmanWienerMeasure, rogersPitmanEntranceMeasure,
      Measure.map_map hm (measurable_negativeRogersPitmanPath 0),
      Measure.map_map hm (measurable_rogersPitmanPath 0),
      Measure.map_map e.measurable (hm.comp (measurable_rogersPitmanPath 0))]
    rfl
  rw [heq, rogersPitmanWienerMeasure_zero_fdd n times hpos hmono,
    radialSkeletonDensityMeasure_map_neg]

/-- An unconditional continuous zero-drift entrance law on the exact `BrownianPath` carrier. -/
theorem negativeRogersPitmanWienerMeasure_zero_isConditioned :
    IsNegativeConditionedBrownianLaw 0 (negativeRogersPitmanWienerMeasure 0) := by
  refine ⟨le_refl 0, inferInstance, negativeRogersPitmanWienerMeasure_zero_ae 0, ?_⟩
  intro n hn times hpos hmono
  cases n with
  | zero => omega
  | succ n =>
      exact negativeRogersPitmanWienerMeasure_zero_fdd n times (fun i => hpos i) hmono


/-- Every positive ordered zero-drift skeleton density is a probability measure. -/
theorem radialSkeletonDensityMeasure_zero_isProbability (n : ℕ)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) :
    IsProbabilityMeasure (radialSkeletonDensityMeasure 0 (fun i => (times i : ℝ))) := by
  rw [← wienerRadialSamples_zeroDrift_fdd n times hpos hmono]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_wienerRadialSamples times).aemeasurable).mpr inferInstance


/-- Actual nonnegative tests of every zero-drift Wiener radial skeleton use the density
`conditionedPositiveFDDVectorDensity`. -/
theorem lintegral_wienerRadialSamples_zeroDrift (n : ℕ)
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times)
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (wienerRadialSamples times V) ∂wienerTripleMeasure) =
      ∫⁻ x, conditionedPositiveFDDVectorDensity 0 (fun i => (times i : ℝ)) x * F x := by
  rw [← lintegral_map hF (measurable_wienerRadialSamples times),
    wienerRadialSamples_zeroDrift_fdd n times hpos hmono, radialSkeletonDensityMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_conditionedPositiveFDDVectorDensity 0 _) hF]
  rfl




end DOZZ.Proofs
