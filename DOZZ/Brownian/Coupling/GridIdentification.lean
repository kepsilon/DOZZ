/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.RadialTiltDensity
public import DOZZ.Brownian.Coupling.GridConvergence
public import DOZZ.Brownian.Coupling.RationalExtension

/-!
# Exact common-grid marginals and the ordered two-sided coupling

The quantile chain and the actual Rogers--Pitman samples have the same full skeleton density.
This discharges the finite-grid law identity needed by the existing joint compactness construction.
The real extension retains every quantitative drift bound before two independent copies are taken.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Forget the positive subtypes in a finite sampled path. -/
def couplingGridRealCoords (n : ℕ) (x : ConditionedEntranceGridPath n) : Fin (n + 1) → ℝ :=
  fun i => (x i).1

theorem measurable_couplingGridRealCoords (n : ℕ) : Measurable (couplingGridRealCoords n) :=
  measurable_pi_iff.mpr fun i => measurable_subtype_coe.comp (measurable_pi_apply i)

/-- Forgetting positive subtypes is a measurable embedding, so it detects entire grid laws. -/
theorem couplingGridRealCoords_measurableEmbedding (n : ℕ) :
    MeasurableEmbedding (couplingGridRealCoords n) := by
  let e := (MeasurableEquiv.subtypePiEquivPi
    (p := fun (_ : Fin (n + 1)) (r : ℝ) => 0 < r)).symm
  have hS : MeasurableSet {x : Fin (n + 1) → ℝ | ∀ i, 0 < x i} := by
    have hs : ∀ i : Fin (n + 1), MeasurableSet {x : Fin (n + 1) → ℝ | 0 < x i} :=
      fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
    have heq : {x : Fin (n + 1) → ℝ | ∀ i, 0 < x i} =
        ⋂ i : Fin (n + 1), {x : Fin (n + 1) → ℝ | 0 < x i} := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq]
    rw [heq]
    exact MeasurableSet.iInter hs
  exact (MeasurableEmbedding.subtype_coe hS).comp e.measurableEmbedding

/-- The scalar entrance quantile chain is an actual probability law. -/
theorem coupling_scalarGrid_isProbability (a : ℝ) (ha : 0 ≤ a) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    IsProbabilityMeasure (conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ
      (fun _ => hδ) n) := by
  let v : Unit → ℝ≥0 := fun _ => ⟨a, ha⟩
  let _ := coupledEntranceGridMeasure_isProbabilityMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n
  have h := coupledEntranceGridMeasure_coordinate_map v δ (fun _ => δ) hδ (fun _ => hδ) () n
  change (coupledEntranceGridMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n).map
    (fun x => x ()) = conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) n at h
  rw [← h]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply ()).aemeasurable).mpr inferInstance

/-- The full real-coordinate past and next quantile state have the literal density kernel. -/
theorem coupling_scalarGrid_next_joint (a : ℝ) (ha : 0 ≤ a) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) (n + 1)).map
      (fun x => (couplingGridRealCoords n (Fin.init x), (x (Fin.last (n + 1))).1)) =
      ((conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) n).map
        (couplingGridRealCoords n)).compProd
          ((radialSkeletonTransitionDensityKernel a δ).comap (fun x => x (Fin.last n))
            (measurable_pi_apply _)) := by
  let μ := conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) n
  let μ' := conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) (n + 1)
  let J := fun x : ConditionedEntranceGridPath (n + 1) =>
    (couplingGridRealCoords n (Fin.init x), (x (Fin.last (n + 1))).1)
  have hmJ : Measurable J :=
    ((measurable_couplingGridRealCoords n).comp (measurable_pi_iff.mpr fun i =>
      measurable_pi_apply i.castSucc)).prodMk (measurable_subtype_coe.comp (measurable_pi_apply _))
  let _ := coupling_scalarGrid_isProbability a ha δ hδ (n + 1)
  let _ := coupling_scalarGrid_isProbability a ha δ hδ n
  let _ : IsProbabilityMeasure (μ'.map J) := (Measure.isProbabilityMeasure_map_iff hmJ.aemeasurable).mpr inferInstance
  apply Measure.ext_prod
  intro A B hA hB
  let A' := couplingGridRealCoords n ⁻¹' A
  let B' := (Subtype.val : ConditionedPositiveState → ℝ) ⁻¹' B
  have hA' : MeasurableSet A' := hA.preimage (measurable_couplingGridRealCoords n)
  have hB' : MeasurableSet B' := hB.preimage measurable_subtype_coe
  have hrect := conditionedPositiveEntranceGridMeasure_markov_rect a δ (fun _ => δ)
    ha hδ (fun _ => hδ) n A' B' hA' hB'
  have hmPair : Measurable (fun x : ConditionedEntranceGridPath (n + 1) =>
      (Fin.init x, x (Fin.last (n + 1)))) :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply _)
  rw [Measure.map_apply hmPair (hA'.prod hB')] at hrect
  rw [Measure.map_apply hmJ (hA.prod hB), Measure.compProd_apply_prod hA hB]
  have he : J ⁻¹' (A ×ˢ B) = (fun x : ConditionedEntranceGridPath (n + 1) =>
      (Fin.init x, x (Fin.last (n + 1)))) ⁻¹' (A' ×ˢ B') := rfl
  change μ' (J ⁻¹' (A ×ˢ B)) = _
  rw [he, hrect]
  have hk : Measurable (fun x : Fin (n + 1) → ℝ =>
      ((radialSkeletonTransitionDensityKernel a δ).comap (fun x => x (Fin.last n))
        (measurable_pi_apply _) x) B) := (Kernel.measurable_coe _ hB)
  rw [setLIntegral_map hA hk (measurable_couplingGridRealCoords n)]
  apply setLIntegral_congr_fun hA'
  intro x hx
  have hmap := congrArg (fun μ : Measure ℝ => μ B)
    (conditionedPositiveTransitionSubtypeMeasure_map_coe a δ ha hδ (x (Fin.last n)))
  rw [Measure.map_apply measurable_subtype_coe hB] at hmap
  dsimp only
  rw [hmap, Kernel.comap_apply, radialSkeletonTransitionDensityKernel_apply]
  rfl

/-- The actual arithmetic observation times are positive. -/
theorem couplingGridSampleTimes_pos (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (i : Fin (n + 1)) :
    0 < couplingGridSampleTime δ hδ i.val := by
  change 0 < ((i.val : ℝ) + 1) * δ
  exact mul_pos (by positivity) hδ

/-- Arithmetic observation times are strictly increasing in their literal finite index. -/
theorem couplingGridSampleTimes_strictMono (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    StrictMono (fun i : Fin (n + 1) => couplingGridSampleTime δ hδ i.val) := by
  intro i j hij
  change ((i.val : ℝ) + 1) * δ < ((j.val : ℝ) + 1) * δ
  have hcast : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  apply mul_lt_mul_of_pos_right _ hδ
  simpa only [add_comm] using add_lt_add_right hcast 1

/-- The full real-coordinate quantile grid law has the literal skeleton density. -/
theorem coupling_scalarGrid_real_density (a : ℝ) (ha : 0 ≤ a) (δ : ℝ) (hδ : 0 < δ) : ∀ n : ℕ,
    (conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) n).map
      (couplingGridRealCoords n) = radialSkeletonDensityMeasure a
        (fun i : Fin (n + 1) => ((i.val : ℝ) + 1) * δ) := by
  intro n
  induction n with
  | zero =>
    let e := MeasurableEquiv.funUnique (Fin 1) ℝ
    apply e.measurableEmbedding.map_injective
    rw [Measure.map_map e.measurable (measurable_couplingGridRealCoords 0),
      radialSkeletonDensityMeasure_one_map a ha _ (by simpa using hδ)]
    simpa [e, couplingGridRealCoords, Function.comp_def] using
      conditionedPositiveEntranceGridMeasure_initial_law a δ (fun _ => δ) ha hδ (fun _ => hδ)
  | succ n ih =>
    let e := radialSkeletonLastSplit (n + 1)
    apply e.measurableEmbedding.map_injective
    rw [Measure.map_map e.measurable (measurable_couplingGridRealCoords (n + 1))]
    have he : (fun x : ConditionedEntranceGridPath (n + 1) => e (couplingGridRealCoords (n + 1) x)) =
        (fun x => (couplingGridRealCoords n (Fin.init x), (x (Fin.last (n + 1))).1)) := by
      funext x
      apply Prod.ext
      · rw [radialSkeletonLastSplit_fst]; rfl
      · rw [radialSkeletonLastSplit_snd]; rfl
    change (conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) (n + 1)).map
      (fun x => e (couplingGridRealCoords (n + 1) x)) = _
    rw [he, coupling_scalarGrid_next_joint a ha δ hδ n, ih,
      radialSkeletonDensityMeasure_last_compProd a ha n]
    have hdiff : (((Fin.last (n + 1)).val : ℝ) + 1) * δ -
        (((Fin.last n).castSucc.val : ℝ) + 1) * δ = δ := by
      simp only [Fin.val_last, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      ring
    rw [hdiff]
    rfl

/-- Actual positive path samples have the same full real-coordinate skeleton density. -/
theorem rogersPitman_positive_samples_real_density (a : ℝ) (ha : 0 ≤ a)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ((rogersPitmanWienerProbability a : Measure BrownianPath).map
      (couplingPositivePathSamples δ hδ n)).map (couplingGridRealCoords n) =
      radialSkeletonDensityMeasure a (fun i : Fin (n + 1) => ((i.val : ℝ) + 1) * δ) := by
  rw [Measure.map_map (measurable_couplingGridRealCoords n) (measurable_couplingPositivePathSamples hδ n)]
  have he : (fun p : BrownianPath => couplingGridRealCoords n (couplingPositivePathSamples δ hδ n p)) =ᵐ[(rogersPitmanWienerProbability a : Measure BrownianPath)]

      (fun p i => p (couplingGridSampleTime δ hδ i.val)) := by
    filter_upwards [rogersPitmanWienerProbability_samples_positive_ae a (fun _ => δ)
      (fun _ => hδ) (fun _ => n)] with p hp
    funext i
    exact couplingPositivePathSamples_eq hδ n p i (hp 0 i)
  change (rogersPitmanWienerProbability a : Measure BrownianPath).map
    (fun p => couplingGridRealCoords n (couplingPositivePathSamples δ hδ n p)) = _
  rw [Measure.map_congr he]
  have h := rogersPitmanWienerMeasure_fdd n a ha
    (fun i => couplingGridSampleTime δ hδ i.val) (couplingGridSampleTimes_pos δ hδ n)
      (couplingGridSampleTimes_strictMono δ hδ n)
  change (wienerTripleMeasure.map (rogersPitmanPath a)).map
    (fun p => fun i : Fin (n + 1) => p (couplingGridSampleTime δ hδ i.val)) = _
  simpa only [couplingGridSampleTime_coe, rogersPitmanWienerMeasure, rogersPitmanEntranceMeasure, wienerTripleMeasure] using h

/-- The common-quantile scalar grid is exactly the sampled unconditional Rogers--Pitman path law. -/
theorem conditionedPositiveEntranceGridMeasure_eq_radial_samples (a : ℝ) (ha : 0 ≤ a)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    conditionedPositiveEntranceGridMeasure a δ (fun _ => δ) ha hδ (fun _ => hδ) n =
      (rogersPitmanWienerProbability a : Measure BrownianPath).map (couplingPositivePathSamples δ hδ n) := by
  apply (couplingGridRealCoords_measurableEmbedding n).map_injective
  rw [coupling_scalarGrid_real_density a ha δ hδ n,
    rogersPitman_positive_samples_real_density a ha δ hδ n]

/-- The negative radial probability law is the same concrete measure for which
`DOZZ.IsNegativeConditionedBrownianLaw` is proved. -/
theorem negativeRogersPitmanWienerProbability_isConditioned (a : ℝ) (ha : 0 ≤ a) :
    IsNegativeConditionedBrownianLaw a (negativeRogersPitmanWienerProbability a : Measure BrownianPath) := by
  change IsNegativeConditionedBrownianLaw a
    (wienerTripleMeasure.map (negativeRogersPitmanPath a))
  exact negativeRogersPitmanWienerMeasure_isConditioned a ha

/-- Actual common dyadic grids supply an unconditional countable ordered radial family. -/
theorem exists_ordered_countable_radial_family (v : ℕ → ℝ≥0) :
    ∃ Q : ProbabilityMeasure (ℕ → BrownianPath),
      (∀ j, Q.map (fun F => F j) = negativeRogersPitmanWienerProbability (v j)) ∧
      ∀ᵐ F ∂(Q : Measure (ℕ → BrownianPath)), F ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  apply exists_ordered_radial_countable_family_of_sample_law v couplingDyadicMesh couplingDyadicMesh_pos
    couplingDyadicLastIndex couplingDyadicMesh_tendsto couplingDyadicHorizon_tendsto
  intro m j
  exact conditionedPositiveEntranceGridMeasure_eq_radial_samples (v j) (v j).coe_nonneg
    (couplingDyadicMesh m) (couplingDyadicMesh_pos m) (couplingDyadicLastIndex m)

/-- Rational reindexing of the actual joint limit retains every marginal and simultaneous order bound. -/
theorem exists_ordered_rational_radial_family :
    ∃ Q : ProbabilityMeasure (ℚ → BrownianPath),
      (∀ q : ℚ, 0 ≤ q → Q.map (fun F => F q) = negativeRogersPitmanWienerProbability q) ∧
      ∀ᵐ F ∂(Q : Measure (ℚ → BrownianPath)), F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) := by
  let v : ℕ → ℝ≥0 := fun j => ⟨couplingEnumeratedDrift j, le_max_right _ _⟩
  obtain ⟨Q, hQlaw, hQorder⟩ := exists_ordered_countable_radial_family v
  refine ⟨Q.map couplingRationalReindex, ?_, ?_⟩
  · intro q hq
    apply Subtype.ext
    change ((Q : Measure (ℕ → BrownianPath)).map couplingRationalReindex).map (fun F => F q) =
      (negativeRogersPitmanWienerProbability q : Measure BrownianPath)
    rw [Measure.map_map (measurable_pi_apply q) measurable_couplingRationalReindex]
    have h := congrArg (fun R : ProbabilityMeasure BrownianPath => (R : Measure BrownianPath))
      (hQlaw (couplingRationalEnumeration q))
    change (Q : Measure (ℕ → BrownianPath)).map (fun x => x (couplingRationalEnumeration q)) = _ at h
    change (Q : Measure (ℕ → BrownianPath)).map (fun x => x (couplingRationalEnumeration q)) = _
    rw [h]
    have hdrift : (v (couplingRationalEnumeration q) : ℝ) = (q : ℝ) := by
      have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
      change couplingEnumeratedDrift (couplingRationalEnumeration q) = (q : ℝ)
      simp only [couplingEnumeratedDrift, Equiv.symm_apply_apply, max_eq_left hqR]
    exact congrArg (fun a : ℝ => (negativeRogersPitmanWienerProbability a : Measure BrownianPath)) hdrift
  · change ∀ᵐ F ∂((Q : Measure (ℕ → BrownianPath)).map couplingRationalReindex),
      F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
    apply (ae_map_iff measurable_couplingRationalReindex.aemeasurable
      (isClosed_negativeEntranceOrderSet ((↑) : ℚ → ℝ)).measurableSet).mpr
    exact hQorder.mono fun F hF => couplingRationalReindex_mem_orderSet F hF

/-- Fix the proved rational joint law for the concrete two-sided realization. -/
noncomputable def orderedRationalWienerProbability : ProbabilityMeasure (ℚ → BrownianPath) :=
  Classical.choose exists_ordered_rational_radial_family

/-- Every nonnegative rational coordinate has its actual conditioned Wiener marginal. -/
theorem orderedRationalWienerProbability_marginal (q : ℚ) (hq : 0 ≤ q) :
    orderedRationalWienerProbability.map (fun F => F q) = negativeRogersPitmanWienerProbability q :=
  (Classical.choose_spec exists_ordered_rational_radial_family).1 q hq

/-- All rational drift inequalities hold on one event for the chosen actual joint probability. -/
theorem orderedRationalWienerProbability_order :
    ∀ᵐ F ∂(orderedRationalWienerProbability : Measure (ℚ → BrownianPath)),
      F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) :=
  (Classical.choose_spec exists_ordered_rational_radial_family).2


/-- Every real coordinate of the extended joint family has the literal conditioned law. -/
theorem orderedRationalWienerProbability_real_law (a : ℝ) (ha : 0 ≤ a) :
    IsNegativeConditionedBrownianLaw a
      ((orderedRationalWienerProbability : Measure (ℚ → BrownianPath)).map
        (fun F => orderedRationalPathExtension F a)) :=
  orderedRationalPathExtension_real_law_of_radial _ orderedRationalWienerProbability_order
    orderedRationalWienerProbability_marginal negativeRogersPitmanWienerProbability_isConditioned a ha

/-- Two independent copies of the entire rational family form the concrete two-sided source. -/
noncomputable def orderedWienerCouplingMeasure :
    Measure ((ℚ → BrownianPath) × (ℚ → BrownianPath)) :=
  (orderedRationalWienerProbability : Measure (ℚ → BrownianPath)).prod
    (orderedRationalWienerProbability : Measure (ℚ → BrownianPath))

instance isProbabilityMeasure_orderedWienerCouplingMeasure :
    IsProbabilityMeasure orderedWienerCouplingMeasure := by
  unfold orderedWienerCouplingMeasure
  infer_instance

/-- The concrete all-real family satisfies every clause of the ordered characterization
`DOZZ.IsOrderedTwoSidedConditionedCoupling`. -/
theorem orderedWienerCouplingMeasure_isOrdered :
    IsOrderedTwoSidedConditionedCoupling orderedWienerCouplingMeasure realDriftCouplingOfRationalPaths :=
  realDriftCouplingOfRationalPaths_isOrdered_of_marginals _ orderedRationalWienerProbability_real_law

/-- The first half of the actual coupled law is the concrete conditioned entrance law. -/
theorem orderedWienerCouplingMeasure_first_map (a : ℝ) (ha : 0 ≤ a) :
    orderedWienerCouplingMeasure.map (fun F => (realDriftCouplingOfRationalPaths a F).1) =
      negativeRogersPitmanWienerMeasure a := by
  exact negativeConditionedBrownianLaw_eq_wiener a
    (orderedWienerCouplingMeasure_isOrdered.1 a ha).1.2

/-- The second half has the same entire continuous-path law. -/
theorem orderedWienerCouplingMeasure_second_map (a : ℝ) (ha : 0 ≤ a) :
    orderedWienerCouplingMeasure.map (fun F => (realDriftCouplingOfRationalPaths a F).2) =
      negativeRogersPitmanWienerMeasure a := by
  exact negativeConditionedBrownianLaw_eq_wiener a
    (orderedWienerCouplingMeasure_isOrdered.1 a ha).2.1.2

/-- At every real drift the two actual half-paths are independent. -/
theorem orderedWienerCouplingMeasure_independent (a : ℝ) :
    IndepFun (fun F => (realDriftCouplingOfRationalPaths a F).1)
      (fun F => (realDriftCouplingOfRationalPaths a F).2) orderedWienerCouplingMeasure :=
  realDriftCouplingOfRationalPaths_indep _ a


/-- Every fixed-parameter coupled observation is measurable as a pair of full paths. -/
theorem orderedWienerCoupling_measurable (a : ℝ) : Measurable (realDriftCouplingOfRationalPaths a) :=
  measurable_realDriftCouplingOfRationalPaths.comp (measurable_const.prodMk measurable_id)

/-- The coupled pair law is the product of the two concrete conditioned path laws. -/
theorem orderedWienerCouplingMeasure_pair_map (a : ℝ) (ha : 0 ≤ a) :
    orderedWienerCouplingMeasure.map (realDriftCouplingOfRationalPaths a) =
      (negativeRogersPitmanWienerMeasure a).prod (negativeRogersPitmanWienerMeasure a) := by
  have h := (orderedWienerCouplingMeasure_independent a).map_prod_eq_prod_map_map
    (measurable_fst.comp (orderedWienerCoupling_measurable a)).aemeasurable
    (measurable_snd.comp (orderedWienerCoupling_measurable a)).aemeasurable
  simp only [Function.comp_def, Prod.eta] at h
  rw [orderedWienerCouplingMeasure_first_map a ha,
    orderedWienerCouplingMeasure_second_map a ha] at h
  exact h









/-- The comparison theorem supplies a common coupling on a suitable measurable carrier.
Brownian foundations `thm:comparison` constructs the rational-parameter coupling and extends it;
this statement leaves the carrier existential instead of imposing the real-indexed product
sigma algebra. The negative-path bounds reverse the source's positive-path inequalities. -/
theorem twoSidedConditionedBrownian_orderedCoupling_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (B : ℝ → Ω → BrownianPath × BrownianPath),
      IsProbabilityMeasure P ∧ IsOrderedTwoSidedConditionedCoupling P B := by
  exact ⟨(ℚ → BrownianPath) × (ℚ → BrownianPath), inferInstance, orderedWienerCouplingMeasure,
    realDriftCouplingOfRationalPaths, inferInstance, orderedWienerCouplingMeasure_isOrdered⟩

end DOZZ.Proofs
