/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.Interpolation
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compact-time convergence of sampled entrance-path interpolants

The error of linear interpolation is controlled by the continuity modulus of the sampled path.
This is the deterministic ingredient used to identify whole-path marginal limits of the common
quantile grids. It requires no additional process moment estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- The positive sampling time at grid index `k`. -/
noncomputable def couplingGridSampleTime (δ : ℝ) (hδ : 0 < δ) (k : ℕ) : ℝ≥0 :=
  ⟨((k : ℝ) + 1) * δ, by positivity⟩

theorem couplingGridSampleTime_coe (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (couplingGridSampleTime δ hδ k : ℝ) = ((k : ℝ) + 1) * δ := rfl

/-- Convex interpolation retains a common endpoint error bound. -/
theorem coupling_convex_error {x y b r ε : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : |x - b| ≤ ε) (hy : |y - b| ≤ ε) :
    |(1 - r) * x + r * y - b| ≤ ε := by
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  have hlo0 := mul_le_mul_of_nonneg_left hxlo (sub_nonneg.mpr hr1)
  have hlo1 := mul_le_mul_of_nonneg_left hylo hr0
  have hhi0 := mul_le_mul_of_nonneg_left hxhi (sub_nonneg.mpr hr1)
  have hhi1 := mul_le_mul_of_nonneg_left hyhi hr0
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Interpolation error is bounded by the sampled path's modulus over one grid cell. -/
theorem couplingGridInterpolant_error {δ ε : ℝ} (hδ : 0 < δ)
    (p : BrownianPath) (hp0 : p 0 = 0) (n : ℕ) (x : ConditionedEntranceGridPath n)
    (hsample : ∀ i : Fin (n + 1), (x i).1 = p (couplingGridSampleTime δ hδ i.val))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ)
    (hmodulus : ∀ s : ℝ≥0, |(s : ℝ) - (t : ℝ)| ≤ δ → |p s - p t| ≤ ε) :
    |couplingGridInterpolant δ n x t - p t| ≤ ε := by
  induction n with
  | zero =>
      have ht' : (t : ℝ) ≤ δ := by simpa using ht
      have hzero := hmodulus 0 (by
        change |(0 : ℝ) - (t : ℝ)| ≤ δ
        rw [abs_le]
        constructor <;> linarith [NNReal.coe_nonneg t])
      have hfirst := hmodulus (couplingGridSampleTime δ hδ 0) (by
        rw [couplingGridSampleTime_coe]
        norm_num only [Nat.cast_zero, zero_add, one_mul]
        rw [abs_le]
        constructor <;> linarith [NNReal.coe_nonneg t])
      rw [hp0] at hzero
      have hs0 := hsample 0
      simp only [Fin.val_zero] at hs0
      rw [← hs0] at hfirst
      have h := coupling_convex_error (couplingRamp_nonneg 0 δ (t : ℝ))
        (couplingRamp_le_one 0 δ (t : ℝ)) hzero hfirst
      change |(x 0).1 * couplingRamp 0 δ (t : ℝ) - p t| ≤ ε
      have heq : (x 0).1 * couplingRamp 0 δ (t : ℝ) =
          (1 - couplingRamp 0 δ (t : ℝ)) * 0 + couplingRamp 0 δ (t : ℝ) * (x 0).1 := by ring
      rw [heq]
      exact h
  | succ n ih =>
      by_cases hbefore : (t : ℝ) ≤ ((n : ℝ) + 1) * δ
      · rw [couplingGridInterpolant_before_append hδ n x t hbefore]
        exact ih (Fin.init x) (fun i => hsample i.castSucc) hbefore
      · have hafter : ((n : ℝ) + 1) * δ ≤ (t : ℝ) := le_of_not_ge hbefore
        have hold : |p (couplingGridSampleTime δ hδ n) - p t| ≤ ε := hmodulus _ (by
          rw [couplingGridSampleTime_coe]
          rw [abs_le]
          push_cast at ht
          constructor <;> nlinarith)
        have hnew : |p (couplingGridSampleTime δ hδ (n + 1)) - p t| ≤ ε := hmodulus _ (by
          rw [couplingGridSampleTime_coe]
          rw [abs_le]
          push_cast at ht ⊢
          constructor <;> nlinarith)
        have hsampleOld := hsample (Fin.last n).castSucc
        have hsampleNew := hsample (Fin.last (n + 1))
        simp only [Fin.val_castSucc, Fin.val_last] at hsampleOld hsampleNew
        rw [← hsampleOld] at hold
        rw [← hsampleNew] at hnew
        rw [couplingGridInterpolant_after_append hδ n x t hafter]
        exact coupling_convex_error (couplingRamp_nonneg _ _ _) (couplingRamp_le_one _ _ _) hold hnew

/-- Sampled interpolants converge uniformly on each compact time set as mesh shrinks and horizon
increases. Both mesh and horizon may vary without any relation beyond these two limits. -/
theorem couplingGridInterpolant_tendstoUniformlyOn
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop)
    (p : BrownianPath) (hp0 : p 0 = 0)
    (x : ∀ m, ConditionedEntranceGridPath (N m))
    (hsample : ∀ m (i : Fin (N m + 1)),
      (x m i).1 = p (couplingGridSampleTime (δ m) (hδ m) i.val))
    (K : Set ℝ≥0) (hK : IsCompact K) :
    TendstoUniformlyOn (fun m t => couplingGridInterpolant (δ m) (N m) (x m) t) p atTop K := by
  obtain ⟨T, hTpos, hT⟩ := compact_nonnegative_times_bounded K hK
  let B : ℝ≥0 := ⟨T + 1, by positivity⟩
  have huniform : UniformContinuousOn p (Icc 0 B) :=
    isCompact_Icc.uniformContinuousOn_of_continuous p.continuous.continuousOn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuousOn_iff_le.mp huniform (ε / 2) (by positivity)
  have hsmall := hmesh.eventually (gt_mem_nhds hηpos)
  have hsmallOne := hmesh.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlarge : ∀ᶠ m in atTop, T ≤ ((N m : ℝ) + 1) * δ m :=
    (tendsto_atTop.1 hhorizon) T
  filter_upwards [hsmall, hsmallOne, hlarge] with m hm hm1 hmT
  intro t ht
  have htT := hT t ht
  have htB : t ∈ Icc 0 B := ⟨zero_le, by change (t : ℝ) ≤ T + 1; linarith⟩
  have herror := couplingGridInterpolant_error (hδ m) p hp0 (N m) (x m) (hsample m)
    t (htT.trans hmT) (ε := ε / 2) (by
      intro s hs
      have hsB : s ∈ Icc 0 B := by
        refine ⟨zero_le, ?_⟩
        change (s : ℝ) ≤ T + 1
        have hbound := (abs_le.mp hs).2
        linarith
      have hdist : dist s t ≤ η := by
        change |(s : ℝ) - (t : ℝ)| ≤ η
        exact hs.trans hm.le
      simpa only [Real.dist_eq] using hη s hsB t htB hdist)
  rw [Real.dist_eq, abs_sub_comm]
  exact herror.trans_lt (half_lt_self hε)

/-- Compact-uniform convergence is convergence in the actual continuous-path carrier. -/
theorem couplingGridInterpolant_tendsto
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop)
    (p : BrownianPath) (hp0 : p 0 = 0)
    (x : ∀ m, ConditionedEntranceGridPath (N m))
    (hsample : ∀ m (i : Fin (N m + 1)),
      (x m i).1 = p (couplingGridSampleTime (δ m) (hδ m) i.val)) :
    Tendsto (fun m => couplingGridInterpolant (δ m) (N m) (x m)) atTop (𝓝 p) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  exact couplingGridInterpolant_tendstoUniformlyOn δ hδ N hmesh hhorizon p hp0 x hsample

/-- Sample a path in the positive finite-grid carrier, using a harmless fixed value whenever
one of its finitely many evaluations is nonpositive. -/
noncomputable def couplingPositivePathSamples (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (p : BrownianPath) : ConditionedEntranceGridPath n :=
  fun i => if hp : 0 < p (couplingGridSampleTime δ hδ i.val) then
    ⟨p (couplingGridSampleTime δ hδ i.val), hp⟩ else ⟨1, by norm_num⟩

theorem couplingPositivePathSamples_eq {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (p : BrownianPath) (i : Fin (n + 1))
    (hp : 0 < p (couplingGridSampleTime δ hδ i.val)) :
    (couplingPositivePathSamples δ hδ n p i).1 = p (couplingGridSampleTime δ hδ i.val) := by
  rw [couplingPositivePathSamples, dite_eq_left hp]

theorem measurable_couplingPositivePathSamples {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Measurable (couplingPositivePathSamples δ hδ n) := by
  apply measurable_pi_iff.mpr
  intro i
  let f : BrownianPath → ℝ := fun p =>
    if 0 < p (couplingGridSampleTime δ hδ i.val) then
      p (couplingGridSampleTime δ hδ i.val) else 1
  have hf : Measurable f := (ContinuousMap.measurable_eval _).ite
    (measurableSet_lt measurable_const (ContinuousMap.measurable_eval _)) measurable_const
  have hpos (p : BrownianPath) : 0 < f p := by
    dsimp [f]
    split_ifs with hp
    · exact hp
    · norm_num
  have hms : Measurable (fun p => (⟨f p, hpos p⟩ : ConditionedPositiveState)) := hf.subtype_mk
  have heq : (fun p : BrownianPath => couplingPositivePathSamples δ hδ n p i) =
      (fun p => (⟨f p, hpos p⟩ : ConditionedPositiveState)) := by
    funext p
    apply Subtype.ext
    dsimp only [couplingPositivePathSamples, f]
    split_ifs <;> rfl
  rw [heq]
  exact hms

/-- The sampled interpolant is an actual measurable whole-path random variable. -/
theorem measurable_couplingSampledInterpolant {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Measurable (fun p => couplingGridInterpolant δ n (couplingPositivePathSamples δ hδ n p)) :=
  (measurable_couplingGridInterpolant δ n).comp (measurable_couplingPositivePathSamples hδ n)

/-- Positive sampled paths with a zero start are recovered in the compact-open limit. -/
theorem couplingSampledInterpolant_tendsto
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop)
    (p : BrownianPath) (hp0 : p 0 = 0)
    (hpositive : ∀ m (i : Fin (N m + 1)),
      0 < p (couplingGridSampleTime (δ m) (hδ m) i.val)) :
    Tendsto (fun m => couplingGridInterpolant (δ m) (N m)
      (couplingPositivePathSamples (δ m) (hδ m) (N m) p)) atTop (𝓝 p) := by
  apply couplingGridInterpolant_tendsto δ hδ N hmesh hhorizon p hp0
  intro m i
  exact couplingPositivePathSamples_eq (hδ m) (N m) p i (hpositive m i)

/-- Whole-path marginal convergence follows directly from continuous sampled paths and dominated
convergence for bounded continuous tests; no independence of grid increments is required here. -/
theorem couplingSampledInterpolant_probability_tendsto
    (Q : ProbabilityMeasure BrownianPath)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop)
    (hzero : ∀ᵐ p ∂(Q : Measure BrownianPath), p 0 = 0)
    (hpositive : ∀ᵐ p ∂(Q : Measure BrownianPath), ∀ m (i : Fin (N m + 1)),
      0 < p (couplingGridSampleTime (δ m) (hδ m) i.val)) :
    Tendsto (fun m => Q.map (fun p => couplingGridInterpolant (δ m) (N m)
      (couplingPositivePathSamples (δ m) (hδ m) (N m) p))) atTop (𝓝 Q) := by
  have hlim := coupling_probabilityMap_tendsto_of_ae Q
    (fun m p => couplingGridInterpolant (δ m) (N m)
      (couplingPositivePathSamples (δ m) (hδ m) (N m) p)) id
    (fun m => measurable_couplingSampledInterpolant (hδ m) (N m)) measurable_id (by
      filter_upwards [hzero, hpositive] with p hp0 hp
      exact couplingSampledInterpolant_tendsto δ hδ N hmesh hhorizon p hp0 hp)
  have hid : Q.map id = Q := by
    apply Subtype.ext
    exact Measure.map_id
  rw [hid] at hlim
  exact hlim

/-- The positive unconditional Rogers--Pitman candidate as a path probability law. -/
noncomputable def rogersPitmanWienerProbability (a : ℝ) : ProbabilityMeasure BrownianPath :=
  ProbabilityMeasure.map (⟨wienerTripleMeasure, inferInstance⟩ : ProbabilityMeasure BrownianTriple)
    (rogersPitmanPath a)

/-- A single positive-time radial evaluation is strictly positive almost surely. A drift-free
coordinate already rules out the zero vector; no all-time polarity theorem is used. -/
theorem rogersPitmanWienerProbability_eval_positive_ae (a : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ p ∂(rogersPitmanWienerProbability a : Measure BrownianPath), 0 < p t := by
  have hB := wienerTriple_coordinate_isBrownian (1 : Fin 3)
  let _ := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) ht.ne'
  have hnonzero : ∀ᵐ V ∂wienerTripleMeasure, V (1 : Fin 3) t ≠ 0 := by
    have hmeasure : wienerTripleMeasure {V | V (1 : Fin 3) t = 0} = 0 :=
      ((hB.hasLaw_eval t).measure_eq (measurableSet_singleton (0 : ℝ))).trans (measure_singleton 0)
    apply ae_iff.mpr
    simpa only [not_not] using hmeasure
  apply (ae_map_iff (measurable_rogersPitmanPath a).aemeasurable
    (measurableSet_lt measurable_const (ContinuousMap.measurable_eval t))).mpr
  filter_upwards [hnonzero] with V hV
  change 0 < ‖rogersPitmanVectorAt a V t‖
  apply norm_pos_iff.mpr
  intro hzero
  apply hV
  have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z (1 : Fin 3)) hzero
  simpa [rogersPitmanVectorAt] using hcoord

/-- The entire countable collection of sampled radial evaluations is positive on one event. -/
theorem rogersPitmanWienerProbability_samples_positive_ae
    (a : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ) :
    ∀ᵐ p ∂(rogersPitmanWienerProbability a : Measure BrownianPath),
      ∀ m (i : Fin (N m + 1)), 0 < p (couplingGridSampleTime (δ m) (hδ m) i.val) := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro i
  apply rogersPitmanWienerProbability_eval_positive_ae
  change (0 : ℝ) < ((i.val : ℝ) + 1) * δ m
  exact mul_pos (by positivity) (hδ m)

/-- The positive candidate has the singular zero start on the path probability carrier. -/
theorem rogersPitmanWienerProbability_zero_ae (a : ℝ) :
    ∀ᵐ p ∂(rogersPitmanWienerProbability a : Measure BrownianPath), p 0 = 0 :=
  rogersPitmanWienerMeasure_zero_ae a

/-- Reflecting the positive path law gives exactly the negative radial candidate. -/
theorem rogersPitmanWienerProbability_map_neg (a : ℝ) :
    (rogersPitmanWienerProbability a).map (fun p => -p) =
      negativeRogersPitmanWienerProbability a := by
  apply Subtype.ext
  change (wienerTripleMeasure.map (rogersPitmanPath a)).map (fun p => -p) =
    wienerTripleMeasure.map (negativeRogersPitmanPath a)
  rw [Measure.map_map measurable_neg (measurable_rogersPitmanPath a)]
  rfl

/-- The unconditional radial candidate's sampled grids converge to its whole path law. -/
theorem rogersPitman_sampledInterpolant_probability_tendsto
    (a : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop) :
    Tendsto (fun m => (rogersPitmanWienerProbability a).map (fun p =>
      couplingGridInterpolant (δ m) (N m) (couplingPositivePathSamples (δ m) (hδ m) (N m) p)))
      atTop (𝓝 (rogersPitmanWienerProbability a)) :=
  couplingSampledInterpolant_probability_tendsto _ δ hδ N hmesh hhorizon
    (rogersPitmanWienerProbability_zero_ae a)
    (rogersPitmanWienerProbability_samples_positive_ae a δ hδ N)

/-- The negative interpolated candidate converges to the negative radial path probability law. -/
theorem negativeRogersPitman_sampledInterpolant_probability_tendsto
    (a : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop) :
    Tendsto (fun m => (rogersPitmanWienerProbability a).map (fun p =>
      -(couplingGridInterpolant (δ m) (N m) (couplingPositivePathSamples (δ m) (hδ m) (N m) p))))
      atTop (𝓝 (negativeRogersPitmanWienerProbability a)) := by
  have hlim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (rogersPitman_sampledInterpolant_probability_tendsto a δ hδ N hmesh hhorizon)
    (continuous_neg : Continuous (fun p : BrownianPath => -p))
  rw [rogersPitmanWienerProbability_map_neg] at hlim
  have hcomp (m : ℕ) : ((rogersPitmanWienerProbability a).map (fun p =>
      couplingGridInterpolant (δ m) (N m) (couplingPositivePathSamples (δ m) (hδ m) (N m) p))).map
      (fun p => -p) = (rogersPitmanWienerProbability a).map (fun p =>
        -(couplingGridInterpolant (δ m) (N m) (couplingPositivePathSamples (δ m) (hδ m) (N m) p))) := by
    apply Subtype.ext
    exact Measure.map_map measurable_neg (measurable_couplingSampledInterpolant (hδ m) (N m))
  simp_rw [hcomp] at hlim
  exact hlim

/-- Once the norm path's sampled finite law is identified, the actual coupled grid marginal
converges to the unconditional radial path law. -/
theorem couplingInterpolatedGridProbability_marginal_tendsto_of_sample_law
    (v : ℕ → ℝ≥0) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop)
    (hsampled : ∀ m j,
      conditionedPositiveEntranceGridMeasure (v j) (δ m) (fun _ => δ m)
        (NNReal.coe_nonneg (v j)) (hδ m) (fun _ => hδ m) (N m) =
      (rogersPitmanWienerProbability (v j) : Measure BrownianPath).map
        (couplingPositivePathSamples (δ m) (hδ m) (N m)))
    (j : ℕ) :
    Tendsto (fun m => (couplingInterpolatedGridProbability v (δ m) (hδ m) (N m)).map
      (fun F => F j)) atTop (𝓝 (negativeRogersPitmanWienerProbability (v j))) := by
  have heq (m : ℕ) :
      (couplingInterpolatedGridProbability v (δ m) (hδ m) (N m)).map (fun F => F j) =
      (rogersPitmanWienerProbability (v j)).map (fun p =>
        -(couplingGridInterpolant (δ m) (N m)
          (couplingPositivePathSamples (δ m) (hδ m) (N m) p))) := by
    apply Subtype.ext
    change (couplingInterpolatedGridMeasure v (δ m) (hδ m) (N m)).map (fun F => F j) = _
    rw [couplingInterpolatedGridMeasure_coordinate_map, hsampled m j]
    have hnegative : Measurable (fun x : ConditionedEntranceGridPath (N m) =>
        -(couplingGridInterpolant (δ m) (N m) x)) :=
      (measurable_couplingGridInterpolant (δ m) (N m)).neg
    rw [Measure.map_map hnegative (measurable_couplingPositivePathSamples (hδ m) (N m))]
    rfl
  simp_rw [heq]
  exact negativeRogersPitman_sampledInterpolant_probability_tendsto (v j) δ hδ N hmesh hhorizon

/-- The actual common-quantile interpolants have an ordered joint subsequential limit with the
prescribed unconditional radial marginals, conditional only on the finite sampled-law identity. -/
theorem exists_ordered_radial_countable_family_of_sample_law
    (v : ℕ → ℝ≥0) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (N : ℕ → ℕ)
    (hmesh : Tendsto δ atTop (𝓝 0))
    (hhorizon : Tendsto (fun m => ((N m : ℝ) + 1) * δ m) atTop atTop)
    (hsampled : ∀ m j,
      conditionedPositiveEntranceGridMeasure (v j) (δ m) (fun _ => δ m)
        (NNReal.coe_nonneg (v j)) (hδ m) (fun _ => hδ m) (N m) =
      (rogersPitmanWienerProbability (v j) : Measure BrownianPath).map
        (couplingPositivePathSamples (δ m) (hδ m) (N m))) :
    ∃ Q : ProbabilityMeasure (ℕ → BrownianPath),
      (∀ j, Q.map (fun F => F j) = negativeRogersPitmanWienerProbability (v j)) ∧
      ∀ᵐ F ∂(Q : Measure (ℕ → BrownianPath)),
        F ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  apply conditioned_countable_ordered_path_limit (fun j => (v j : ℝ))
    (fun m => couplingInterpolatedGridProbability v (δ m) (hδ m) (N m))
    (fun j => negativeRogersPitmanWienerProbability (v j))
  · exact couplingInterpolatedGridProbability_marginal_tendsto_of_sample_law
      v δ hδ N hmesh hhorizon hsampled
  · intro m
    exact couplingInterpolatedGridMeasure_order_ae v (δ m) (hδ m) (N m)


/-- The dyadic mesh `(1/2)^m`. -/
noncomputable def couplingDyadicMesh (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m

/-- Sample through horizon `m+1`, then use the constant terminal extension. -/
def couplingDyadicLastIndex (m : ℕ) : ℕ := (m + 1) * 2 ^ m - 1

theorem couplingDyadicMesh_pos (m : ℕ) : 0 < couplingDyadicMesh m := by
  unfold couplingDyadicMesh
  positivity

theorem couplingDyadicMesh_tendsto : Tendsto couplingDyadicMesh atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The terminal sample time is exactly the growing horizon, including the initial dyadic level. -/
theorem couplingDyadicHorizon (m : ℕ) :
    ((couplingDyadicLastIndex m : ℝ) + 1) * couplingDyadicMesh m = (m : ℝ) + 1 := by
  have hcount : couplingDyadicLastIndex m + 1 = (m + 1) * 2 ^ m := by
    apply Nat.sub_add_cancel
    have hpos : 0 < (m + 1) * 2 ^ m := by positivity
    exact hpos
  have hcast : (couplingDyadicLastIndex m : ℝ) + 1 = ((m : ℝ) + 1) * (2 : ℝ) ^ m := by
    exact_mod_cast hcount
  rw [hcast, couplingDyadicMesh]
  have hcancel : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((m : ℝ) + 1) * ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) := by ring
    _ = _ := by rw [hcancel, mul_one]

theorem couplingDyadicHorizon_tendsto :
    Tendsto (fun m => ((couplingDyadicLastIndex m : ℝ) + 1) * couplingDyadicMesh m)
      atTop atTop := by
  simp_rw [couplingDyadicHorizon]
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end DOZZ.Proofs
