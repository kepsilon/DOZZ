/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.CountableLimit
public import DOZZ.Brownian.WienerExists
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Extension of an ordered rational-drift family

The drift-gap bounds give uniform continuity into the complete compact-open path carrier.
Extend the clipped rational family through its dense embedding into real drifts. Monotone
rational floor approximations transfer both order bounds and provide a jointly measurable
real-parameter family, with the zero family used outside the measurable order event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Uniformity Classical

namespace DOZZ.Proofs

/-- A monotone rational approximation from below, at mesh `1/(n+1)`. -/
noncomputable def couplingRationalApprox (n : ℕ) (a : ℝ) : ℚ :=
  (⌊((n : ℝ) + 1) * a⌋ : ℚ) / ((n : ℚ) + 1)

theorem couplingRationalApprox_cast (n : ℕ) (a : ℝ) :
    (couplingRationalApprox n a : ℝ) =
      (⌊((n : ℝ) + 1) * a⌋ : ℝ) / ((n : ℝ) + 1) := by
  simp only [couplingRationalApprox, Rat.cast_div, Rat.cast_intCast, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one]

/-- The deterministic mesh error is bounded independently of the drift. -/
theorem couplingRationalApprox_error (n : ℕ) (a : ℝ) :
    0 ≤ a - (couplingRationalApprox n a : ℝ) ∧
      a - (couplingRationalApprox n a : ℝ) < 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [couplingRationalApprox_cast]
  have hlo := Int.floor_le (((n : ℝ) + 1) * a)
  have hhi := Int.lt_floor_add_one (((n : ℝ) + 1) * a)
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hlo))
  · apply (lt_div_iff₀ hn).mpr
    have he : (a - (⌊((n : ℝ) + 1) * a⌋ : ℝ) / ((n : ℝ) + 1)) *
        ((n : ℝ) + 1) = ((n : ℝ) + 1) * a - (⌊((n : ℝ) + 1) * a⌋ : ℝ) := by
      field_simp
    rw [he]
    nlinarith

theorem couplingRationalApprox_mono (n : ℕ) : Monotone (couplingRationalApprox n) := by
  intro a b hab
  unfold couplingRationalApprox
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_left hab (by positivity))
  · positivity

/-- The floor approximation converges at every real drift. -/
theorem couplingRationalApprox_tendsto (a : ℝ) :
    Tendsto (fun n => (couplingRationalApprox n a : ℝ)) atTop (𝓝 a) := by
  have herr : Tendsto (fun n => a - (couplingRationalApprox n a : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (couplingRationalApprox_error n a).1)
      (fun n => (couplingRationalApprox_error n a).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (tendsto_const_nhds (x := a)).sub herr
  simpa using h

/-- Every mesh selector is measurable; its countable range is essential below. -/
theorem measurable_couplingRationalApprox (n : ℕ) : Measurable (couplingRationalApprox n) := by
  have hfloor : Measurable (fun a : ℝ => ⌊((n : ℝ) + 1) * a⌋) :=
    Int.measurable_floor.comp (measurable_const.mul measurable_id)
  exact (measurable_of_countable (fun k : ℤ => (k : ℚ) / ((n : ℚ) + 1))).comp hfloor

/-- Compact-time pointwise Lipschitz bounds suffice for uniform continuity into paths. -/
theorem uniformContinuous_rationalPaths_of_drift_bound
    {F : ℚ → BrownianPath}
    (hF : ∀ q r : ℚ, ∀ t : ℝ≥0,
      |F q t - F r t| ≤ |(q : ℝ) - (r : ℝ)| * (t : ℝ)) : UniformContinuous F := by
  intro U hU
  obtain ⟨K, V, hK, hV, hVU⟩ :=
    (ContinuousMap.mem_compactConvergence_entourage_iff U).mp hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨T, hTpos, hT⟩ := compact_nonnegative_times_bounded K hK
  have hδ : 0 < ε / T := div_pos hε hTpos
  change {p : ℚ × ℚ | (F p.1, F p.2) ∈ U} ∈ 𝓤 ℚ
  filter_upwards [Metric.dist_mem_uniformity hδ] with p hp
  apply hVU
  intro t ht
  apply hεV
  rw [Real.dist_eq]
  have hsource : |(p.1 : ℝ) - (p.2 : ℝ)| < ε / T := by
    simpa only [Rat.dist_eq] using hp
  have hbound := (hF p.1 p.2 t).trans
    (mul_le_mul_of_nonneg_left (hT t ht) (abs_nonneg _))
  exact hbound.trans_lt ((lt_div_iff₀ hTpos).mp hsource)

/-- The uniform extension through the dense rational embedding. -/
noncomputable def rationalPathExtension (F : ℚ → BrownianPath) : ℝ → BrownianPath :=
  Rat.isDenseEmbedding_coe_real.isDenseInducing.extend F

theorem uniformContinuous_rationalPathExtension
    {F : ℚ → BrownianPath} (hF : UniformContinuous F) :
    UniformContinuous (rationalPathExtension F) :=
  uniformContinuous_uniformly_extend Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.denseRange_cast hF

theorem rationalPathExtension_rat
    {F : ℚ → BrownianPath} (hF : UniformContinuous F) (q : ℚ) :
    rationalPathExtension F q = F q :=
  uniformly_extend_of_ind Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.denseRange_cast hF q

/-- The extension is the compact-time limit along the explicit monotone mesh selectors. -/
theorem rationalPathExtension_approx_tendsto
    {F : ℚ → BrownianPath} (hF : UniformContinuous F) (a : ℝ) :
    Tendsto (fun n => F (couplingRationalApprox n a)) atTop
      (𝓝 (rationalPathExtension F a)) := by
  have h := (uniformContinuous_rationalPathExtension hF).continuous.continuousAt.tendsto.comp
    (couplingRationalApprox_tendsto a)
  simpa only [Function.comp_def, rationalPathExtension_rat hF] using h

/-- Global rational order and drift-gap estimates persist under the extension. -/
theorem rationalPathExtension_order
    {F : ℚ → BrownianPath} (hF : UniformContinuous F)
    (horder : ∀ q r : ℚ, q ≤ r → ∀ t : ℝ≥0,
      F r t ≤ F q t ∧ F q t ≤ F r t + ((r : ℝ) - (q : ℝ)) * (t : ℝ)) :
    ∀ a b : ℝ, a ≤ b → ∀ t : ℝ≥0,
      rationalPathExtension F b t ≤ rationalPathExtension F a t ∧
        rationalPathExtension F a t ≤
          rationalPathExtension F b t + (b - a) * (t : ℝ) := by
  intro a b hab t
  have ha := (continuous_eval_const t).continuousAt.tendsto.comp
    (rationalPathExtension_approx_tendsto hF a)
  have hb := (continuous_eval_const t).continuousAt.tendsto.comp
    (rationalPathExtension_approx_tendsto hF b)
  have hg := ((couplingRationalApprox_tendsto b).sub
    (couplingRationalApprox_tendsto a)).mul_const (t : ℝ)
  constructor
  · exact le_of_tendsto_of_tendsto hb ha (Eventually.of_forall fun n =>
      (horder _ _ (couplingRationalApprox_mono n hab) t).1)
  · exact le_of_tendsto_of_tendsto ha (hb.add hg) (Eventually.of_forall fun n =>
      (horder _ _ (couplingRationalApprox_mono n hab) t).2)

/-- Extend a rational family constantly below zero before extending its parameter carrier. -/
def clippedRationalPathFamily (F : ℚ → BrownianPath) (q : ℚ) : BrownianPath := F (max q 0)

/-- The constant negative-drift part satisfies the same global drift-gap bounds. -/
theorem clippedRationalPathFamily_order
    {F : ℚ → BrownianPath}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) :
    ∀ q r : ℚ, q ≤ r → ∀ t : ℝ≥0,
      clippedRationalPathFamily F r t ≤ clippedRationalPathFamily F q t ∧
        clippedRationalPathFamily F q t ≤ clippedRationalPathFamily F r t +
          ((r : ℝ) - (q : ℝ)) * (t : ℝ) := by
  intro q r hqr t
  have hqrR : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqr
  have htn : 0 ≤ (t : ℝ) := t.2
  by_cases hr : r ≤ 0
  · have hq := hqr.trans hr
    simp only [clippedRationalPathFamily, max_eq_right hr, max_eq_right hq]
    exact ⟨le_rfl, le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hqrR) htn)⟩
  · have hr0 : 0 ≤ r := (lt_of_not_ge hr).le
    by_cases hq : q ≤ 0
    · have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq
      have hrR : 0 ≤ (r : ℝ) := by exact_mod_cast hr0
      have h := hF 0 r (by norm_num) (by simpa only [Rat.cast_zero] using hrR) t
      simp only [clippedRationalPathFamily, max_eq_left hr0, max_eq_right hq]
      constructor
      · exact h.1
      · have hgap := h.2
        simp only [Rat.cast_zero, sub_zero] at hgap
        nlinarith
    · have hq0 : 0 ≤ q := (lt_of_not_ge hq).le
      have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq0
      simpa only [clippedRationalPathFamily, max_eq_left hr0, max_eq_left hq0]
        using hF q r hqR hqrR t

/-- The clipped rational family's drift difference bounds its path difference. -/
theorem clippedRationalPathFamily_abs_sub_le
    {F : ℚ → BrownianPath}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) (q r : ℚ) (t : ℝ≥0) :
    |clippedRationalPathFamily F q t - clippedRationalPathFamily F r t| ≤
      |(q : ℝ) - (r : ℝ)| * (t : ℝ) := by
  rcases le_total q r with hqr | hrq
  · have h := clippedRationalPathFamily_order hF q r hqr t
    have hqrR : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqr
    rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonpos (sub_nonpos.mpr hqrR)]
    nlinarith [h.2]
  · have h := clippedRationalPathFamily_order hF r q hrq t
    have hrqR : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
    rw [abs_of_nonpos (sub_nonpos.mpr h.1), abs_of_nonneg (sub_nonneg.mpr hrqR)]
    nlinarith [h.2]

theorem uniformContinuous_clippedRationalPathFamily
    {F : ℚ → BrownianPath}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) :
    UniformContinuous (clippedRationalPathFamily F) :=
  uniformContinuous_rationalPaths_of_drift_bound (clippedRationalPathFamily_abs_sub_le hF)

/-- A real-parameter family defined on every sample. Off the closed order set use the zero path;
this choice permits a measurable extension without assuming order on exceptional samples. -/
noncomputable def orderedRationalPathExtension (F : ℚ → BrownianPath) (a : ℝ) : BrownianPath :=
  if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
    rationalPathExtension (clippedRationalPathFamily F) a else 0

/-- Every sample of the completed family is continuous in its real parameter. -/
theorem continuous_orderedRationalPathExtension (F : ℚ → BrownianPath) :
    Continuous (orderedRationalPathExtension F) := by
  classical
  change Continuous (fun a => if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
    rationalPathExtension (clippedRationalPathFamily F) a else 0)
  by_cases hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
  · simpa only [orderedRationalPathExtension, ite_eq_left hF] using
      (uniformContinuous_rationalPathExtension
        (uniformContinuous_clippedRationalPathFamily hF)).continuous
  · simpa only [orderedRationalPathExtension, ite_eq_right hF] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : BrownianPath)))

/-- Both all-real order bounds hold samplewise in the completed family. -/
theorem orderedRationalPathExtension_order (F : ℚ → BrownianPath) :
    NegativeEntranceFamilyOrder (orderedRationalPathExtension F) := by
  classical
  by_cases hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
  · intro a b _ hab t
    simpa only [orderedRationalPathExtension, ite_eq_left hF] using
      rationalPathExtension_order (uniformContinuous_clippedRationalPathFamily hF)
        (clippedRationalPathFamily_order hF) a b hab t
  · intro a b _ hab t
    simp only [orderedRationalPathExtension, ite_eq_right hF, ContinuousMap.zero_apply, zero_add]
    exact ⟨le_rfl, mul_nonneg (sub_nonneg.mpr hab) t.2⟩

/-- Nonnegative rational coordinates agree with the original family on its order event. -/
theorem orderedRationalPathExtension_rat
    {F : ℚ → BrownianPath}
    (hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)) {q : ℚ} (hq : 0 ≤ q) :
    orderedRationalPathExtension F q = F q := by
  rw [orderedRationalPathExtension, ite_eq_left hF,
    rationalPathExtension_rat (uniformContinuous_clippedRationalPathFamily hF)]
  exact congrArg F (max_eq_left hq)

/-- The explicit selector sequence converges for all samples, including exceptional ones. -/
theorem orderedRationalPathExtension_approx_tendsto (F : ℚ → BrownianPath) (a : ℝ) :
    Tendsto (fun n => if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
      clippedRationalPathFamily F (couplingRationalApprox n a) else 0) atTop
      (𝓝 (orderedRationalPathExtension F a)) := by
  classical
  by_cases hF : F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
  · simpa only [orderedRationalPathExtension, ite_eq_left hF] using
      rationalPathExtension_approx_tendsto (uniformContinuous_clippedRationalPathFamily hF) a
  · simp only [orderedRationalPathExtension, ite_eq_right hF]
    exact tendsto_const_nhds

/-- Joint measurability of one clipped mesh selector. Countability of the rational parameter
allows arbitrary dependence among the path coordinates. -/
theorem measurable_clipped_rational_selector (n : ℕ) :
    Measurable (fun p : ℝ × (ℚ → BrownianPath) =>
      clippedRationalPathFamily p.2 (couplingRationalApprox n p.1)) := by
  have hm : Measurable (fun p : ℚ × (ℚ → BrownianPath) => p.2 (max p.1 0)) :=
    measurable_from_prod_countable_right (fun q => measurable_pi_apply (max q 0))
  exact hm.comp (((measurable_couplingRationalApprox n).comp measurable_fst).prodMk measurable_snd)

/-- The completed family is jointly measurable in drift and sample, not only separately
measurable at fixed drifts. -/
theorem measurable_orderedRationalPathExtension :
    Measurable (fun p : ℝ × (ℚ → BrownianPath) => orderedRationalPathExtension p.2 p.1) := by
  classical
  have hgood : MeasurableSet {p : ℝ × (ℚ → BrownianPath) |
      p.2 ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)} :=
    (isClosed_negativeEntranceOrderSet ((↑) : ℚ → ℝ)).measurableSet.preimage measurable_snd
  apply measurable_of_tendsto_metrizable
    (f := fun n p => if p.2 ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
      clippedRationalPathFamily p.2 (couplingRationalApprox n p.1) else 0)
  · intro n
    exact (measurable_clipped_rational_selector n).ite hgood measurable_const
  · apply tendsto_pi_nhds.mpr
    intro p
    exact orderedRationalPathExtension_approx_tendsto p.2 p.1

/-- Every fixed-drift evaluation is a measurable whole random path. -/
theorem measurable_orderedRationalPathExtension_at (a : ℝ) :
    Measurable (fun F : ℚ → BrownianPath => orderedRationalPathExtension F a) :=
  measurable_orderedRationalPathExtension.comp
    ((show Measurable (fun _ : ℚ → BrownianPath => a) from measurable_const).prodMk measurable_id)

/-- The simultaneous rational order event ensures exact AE agreement at each rational drift. -/
theorem orderedRationalPathExtension_rat_ae
    {Q : Measure (ℚ → BrownianPath)}
    (hQ : ∀ᵐ F ∂Q, F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ))
    {q : ℚ} (hq : 0 ≤ q) :
    (fun F => orderedRationalPathExtension F q) =ᵐ[Q] (fun F => F q) :=
  hQ.mono fun _ hF => orderedRationalPathExtension_rat hF hq

/-- Rational conditioned process laws are retained by the measurable extension. -/
theorem orderedRationalPathExtension_rational_process
    {Q : Measure (ℚ → BrownianPath)}
    (hQ : ∀ᵐ F ∂Q, F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ))
    {q : ℚ} (hq : 0 ≤ q)
    (hlaw : IsNegativeConditionedBrownianProcess Q (fun F => F q) q) :
    IsNegativeConditionedBrownianProcess Q (fun F => orderedRationalPathExtension F q) q :=
  negativeConditionedBrownianProcess_congr_ae hlaw
    (orderedRationalPathExtension_rat_ae hQ hq).symm

/-- The completed family has the exact compact-time zero-drift limit for every sample. -/
theorem orderedRationalPathExtension_tendsto_zero (F : ℚ → BrownianPath) :
    Tendsto (orderedRationalPathExtension F) (𝓝[>] 0)
      (𝓝 (orderedRationalPathExtension F 0)) :=
  negativeEntranceFamilyOrder_tendsto_zero (orderedRationalPathExtension_order F)

/-- The real-drift family on two independent copies of the rational-path carrier. -/
noncomputable def realDriftCouplingOfRationalPaths
    (a : ℝ) (F : (ℚ → BrownianPath) × (ℚ → BrownianPath)) :
    BrownianPath × BrownianPath :=
  (orderedRationalPathExtension F.1 a, orderedRationalPathExtension F.2 a)

/-- Joint drift/sample measurability survives independent duplication. -/
theorem measurable_realDriftCouplingOfRationalPaths :
    Measurable (fun p : ℝ × ((ℚ → BrownianPath) × (ℚ → BrownianPath)) =>
      realDriftCouplingOfRationalPaths p.1 p.2) := by
  have hfirst : Measurable
      (fun p : ℝ × ((ℚ → BrownianPath) × (ℚ → BrownianPath)) =>
        orderedRationalPathExtension p.2.1 p.1) := measurable_orderedRationalPathExtension.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hsecond : Measurable
      (fun p : ℝ × ((ℚ → BrownianPath) × (ℚ → BrownianPath)) =>
        orderedRationalPathExtension p.2.2 p.1) := measurable_orderedRationalPathExtension.comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact hfirst.prodMk hsecond

/-- Continuity in drift for the pair of completed half-paths holds at every sample. -/
theorem continuous_realDriftCouplingOfRationalPaths
    (F : (ℚ → BrownianPath) × (ℚ → BrownianPath)) :
    Continuous (fun a => realDriftCouplingOfRationalPaths a F) :=
  (continuous_orderedRationalPathExtension F.1).prodMk
    (continuous_orderedRationalPathExtension F.2)

/-- The quantitative order and zero-drift limit hold samplewise for the completed pair. -/
theorem realDriftCouplingOfRationalPaths_order_and_limit
    (F : (ℚ → BrownianPath) × (ℚ → BrownianPath)) :
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ t : ℝ≥0,
      (realDriftCouplingOfRationalPaths b F).1 t ≤
        (realDriftCouplingOfRationalPaths a F).1 t ∧
      (realDriftCouplingOfRationalPaths a F).1 t ≤
        (realDriftCouplingOfRationalPaths b F).1 t + (b - a) * (t : ℝ) ∧
      (realDriftCouplingOfRationalPaths b F).2 t ≤
        (realDriftCouplingOfRationalPaths a F).2 t ∧
      (realDriftCouplingOfRationalPaths a F).2 t ≤
        (realDriftCouplingOfRationalPaths b F).2 t + (b - a) * (t : ℝ)) ∧
      Tendsto (fun a => realDriftCouplingOfRationalPaths a F) (𝓝[>] 0)
        (𝓝 (realDriftCouplingOfRationalPaths 0 F)) := by
  refine ⟨?_, (orderedRationalPathExtension_tendsto_zero F.1).prodMk_nhds
    (orderedRationalPathExtension_tendsto_zero F.2)⟩
  intro a b ha hab t
  have hfirst := orderedRationalPathExtension_order F.1 a b ha hab t
  have hsecond := orderedRationalPathExtension_order F.2 a b ha hab t
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩


/-- Independence of the two completed paths at every real drift uses only the product space
and proved measurability, before identifying their real-drift marginals. -/
theorem realDriftCouplingOfRationalPaths_indep
    (Q : Measure (ℚ → BrownianPath)) [IsProbabilityMeasure Q] (a : ℝ) :
    IndepFun (fun F => (realDriftCouplingOfRationalPaths a F).1)
      (fun F => (realDriftCouplingOfRationalPaths a F).2) (Q.prod Q) :=
  indepFun_prod (measurable_orderedRationalPathExtension_at a)
    (measurable_orderedRationalPathExtension_at a)

/-- Only real-drift marginal identification remains in the final conditional assembly. The
simultaneous order event, path continuity, measurability and two-half independence are proved. -/
theorem realDriftCouplingOfRationalPaths_isOrdered_of_marginals
    (Q : Measure (ℚ → BrownianPath)) [IsProbabilityMeasure Q]
    (hlaw : ∀ a : ℝ, 0 ≤ a → IsNegativeConditionedBrownianLaw a
      (Q.map (fun F => orderedRationalPathExtension F a))) :
    IsOrderedTwoSidedConditionedCoupling (Q.prod Q) realDriftCouplingOfRationalPaths := by
  refine ⟨?_, ae_of_all _ realDriftCouplingOfRationalPaths_order_and_limit⟩
  intro a ha
  have hprocess : IsNegativeConditionedBrownianProcess Q
      (fun F => orderedRationalPathExtension F a) a :=
    ⟨(measurable_orderedRationalPathExtension_at a).aemeasurable, hlaw a ha⟩
  exact independentEntranceCopies_twoSided (F := fun a F => orderedRationalPathExtension F a) hprocess


/-- Fix an enumeration of all rational drifts for the countable-product compactness argument. -/
noncomputable def couplingRationalEnumeration : ℚ ≃ ℕ := Denumerable.eqv ℚ

/-- Reindex the extracted countable path family by actual rational drifts. -/
noncomputable def couplingRationalReindex (x : ℕ → BrownianPath) : ℚ → BrownianPath :=
  fun q => x (couplingRationalEnumeration q)

theorem measurable_couplingRationalReindex : Measurable couplingRationalReindex :=
  measurable_pi_iff.mpr fun q => measurable_pi_apply (couplingRationalEnumeration q)

/-- Clipping negative drifts before enumeration provides nonnegative entrance marginals. -/
noncomputable def couplingEnumeratedDrift (n : ℕ) : ℝ :=
  max (couplingRationalEnumeration.symm n : ℝ) 0

/-- The reindexed limit retains the simultaneous rational order event. -/
theorem couplingRationalReindex_mem_orderSet (x : ℕ → BrownianPath)
    (hx : x ∈ negativeEntranceOrderSet couplingEnumeratedDrift) :
    couplingRationalReindex x ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) := by
  intro q r hq hqr t
  have hr : 0 ≤ (r : ℝ) := hq.trans hqr
  have hq' : couplingEnumeratedDrift (couplingRationalEnumeration q) = (q : ℝ) := by
    simp [couplingEnumeratedDrift, max_eq_left hq]
  have hr' : couplingEnumeratedDrift (couplingRationalEnumeration r) = (r : ℝ) := by
    simp [couplingEnumeratedDrift, max_eq_left hr]
  have h := hx (couplingRationalEnumeration q) (couplingRationalEnumeration r)
    (by rw [hq']; exact hq) (by rw [hq', hr']; exact hqr) t
  simpa only [couplingRationalReindex, hq', hr'] using h

/-- Enumeration does not alter an actual conditioned marginal at any nonnegative rational. -/
theorem couplingRationalReindex_process {Q : Measure (ℕ → BrownianPath)}
    (hQ : ∀ n, IsNegativeConditionedBrownianProcess Q (fun x => x n)
      (couplingEnumeratedDrift n)) {q : ℚ} (hq : 0 ≤ q) :
    IsNegativeConditionedBrownianProcess (Q.map couplingRationalReindex)
      (fun F => F q) (q : ℝ) := by
  have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hdrift : couplingEnumeratedDrift (couplingRationalEnumeration q) = (q : ℝ) := by
    simp [couplingEnumeratedDrift, max_eq_left hqR]
  refine ⟨(measurable_pi_apply q).aemeasurable, ?_⟩
  rw [Measure.map_map (measurable_pi_apply q) measurable_couplingRationalReindex]
  change IsNegativeConditionedBrownianLaw (q : ℝ)
    (Q.map (fun x => x (couplingRationalEnumeration q)))
  rw [← hdrift]
  exact (hQ (couplingRationalEnumeration q)).2


/-- Almost-sure convergence of measurable random paths gives convergence of their full path laws. -/
theorem coupling_probabilityMap_tendsto_of_ae
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : ProbabilityMeasure Ω) (f : ℕ → Ω → E) (g : Ω → E)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(Q : Measure Ω), Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => Q.map (f n)) atTop (𝓝 (Q.map g)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmap (n : ℕ) : (∫ x, test x ∂(Q.map (f n) : Measure E)) =
      ∫ ω, test (f n ω) ∂(Q : Measure Ω) := by
    exact integral_map (hf n).aemeasurable test.continuous.measurable.aestronglyMeasurable
  have hmapg : (∫ x, test x ∂(Q.map g : Measure E)) =
      ∫ ω, test (g ω) ∂(Q : Measure Ω) := by
    exact integral_map hg.aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [hmap, hmapg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro n
    exact (test.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => test.norm_coe_le_norm (f n ω)
  · exact hlim.mono fun ω hω => test.continuous.continuousAt.tendsto.comp hω

/-- The unconditional radial paths vary continuously with their drift in the compact-open topology. -/
theorem continuous_rogersPitmanPath_parameter (V : BrownianTriple) :
    Continuous (fun a : ℝ => rogersPitmanPath a V) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × ℝ≥0 => ‖rogersPitmanVectorAt p.1 V p.2‖)
  apply Continuous.norm
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  change Continuous (fun p : ℝ × ℝ≥0 => V i p.2 +
    (if i = 0 then p.1 * (p.2 : ℝ) else 0))
  split_ifs <;> fun_prop

theorem continuous_negativeRogersPitmanPath_parameter (V : BrownianTriple) :
    Continuous (fun a : ℝ => negativeRogersPitmanPath a V) :=
  (continuous_rogersPitmanPath_parameter V).neg

/-- A probability-measure version of the unconditional negative radial path candidate. -/
noncomputable def negativeRogersPitmanWienerProbability (a : ℝ) :
    ProbabilityMeasure BrownianPath :=
  ProbabilityMeasure.map
    (⟨wienerTripleMeasure, inferInstance⟩ : ProbabilityMeasure BrownianTriple)
    (negativeRogersPitmanPath a)

/-- Whole-path convergence of radial candidates supplies parameter continuity without kernel
limits. -/
theorem negativeRogersPitmanWienerProbability_tendsto
    {a : ℕ → ℝ} {b : ℝ} (hab : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => negativeRogersPitmanWienerProbability (a n)) atTop
      (𝓝 (negativeRogersPitmanWienerProbability b)) := by
  apply coupling_probabilityMap_tendsto_of_ae
  · intro n
    exact measurable_negativeRogersPitmanPath (a n)
  · exact measurable_negativeRogersPitmanPath b
  · exact ae_of_all _ fun V =>
      (continuous_negativeRogersPitmanPath_parameter V).continuousAt.tendsto.comp hab

/-- The completed real family is the weak limit of its measurable rational selectors. -/
theorem orderedRationalPathExtension_probability_tendsto
    (Q : ProbabilityMeasure (ℚ → BrownianPath)) (a : ℝ) :
    Tendsto (fun n => Q.map (fun F => if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ)
      then clippedRationalPathFamily F (couplingRationalApprox n a) else 0)) atTop
      (𝓝 (Q.map (fun F => orderedRationalPathExtension F a))) := by
  apply coupling_probabilityMap_tendsto_of_ae
  · intro n
    exact ((measurable_clipped_rational_selector n).comp
      (measurable_const.prodMk measurable_id)).ite
        (isClosed_negativeEntranceOrderSet ((↑) : ℚ → ℝ)).measurableSet measurable_const
  · exact measurable_orderedRationalPathExtension_at a
  · exact ae_of_all _ fun F => orderedRationalPathExtension_approx_tendsto F a

/-- Uniqueness of weak limits identifies the real-drift extension from its rational path marginals.
The norm candidate supplies parameter continuity, so no density limit interchange is required. -/
theorem orderedRationalPathExtension_map_eq_radial
    (Q : ProbabilityMeasure (ℚ → BrownianPath))
    (hgood : ∀ᵐ F ∂(Q : Measure (ℚ → BrownianPath)),
      F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ))
    (hrational : ∀ q : ℚ, 0 ≤ q →
      Q.map (fun F => F q) = negativeRogersPitmanWienerProbability q)
    (a : ℝ) (ha : 0 ≤ a) :
    Q.map (fun F => orderedRationalPathExtension F a) =
      negativeRogersPitmanWienerProbability a := by
  have hmap (n : ℕ) : Q.map (fun F =>
      if F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ) then
        clippedRationalPathFamily F (couplingRationalApprox n a) else 0) =
      negativeRogersPitmanWienerProbability ((max (couplingRationalApprox n a) 0 : ℚ) : ℝ) := by
    calc
      _ = Q.map (fun F => F (max (couplingRationalApprox n a) 0)) := by
        apply Subtype.ext
        apply Measure.map_congr
        exact hgood.mono fun F hF => by
          dsimp only
          rw [ite_eq_left hF]
          rfl
      _ = _ := hrational _ (le_max_right _ _)
  have hparameter : Tendsto (fun n => ((max (couplingRationalApprox n a) 0 : ℚ) : ℝ)) atTop
      (𝓝 a) := by
    simp only [Rat.cast_max, Rat.cast_zero]
    simpa only [max_eq_left ha] using
      (couplingRationalApprox_tendsto a).max (tendsto_const_nhds (x := (0 : ℝ)))
  have hradial := negativeRogersPitmanWienerProbability_tendsto hparameter
  simp_rw [← hmap] at hradial
  exact tendsto_nhds_unique (orderedRationalPathExtension_probability_tendsto Q a) hradial

/-- Once the actual radial candidate is characterized, every real marginal of the completed
family has the literal conditioned law. -/
theorem orderedRationalPathExtension_real_law_of_radial
    (Q : ProbabilityMeasure (ℚ → BrownianPath))
    (hgood : ∀ᵐ F ∂(Q : Measure (ℚ → BrownianPath)),
      F ∈ negativeEntranceOrderSet ((↑) : ℚ → ℝ))
    (hrational : ∀ q : ℚ, 0 ≤ q →
      Q.map (fun F => F q) = negativeRogersPitmanWienerProbability q)
    (hradial : ∀ a : ℝ, 0 ≤ a → IsNegativeConditionedBrownianLaw a
      (negativeRogersPitmanWienerProbability a : Measure BrownianPath))
    (a : ℝ) (ha : 0 ≤ a) :
    IsNegativeConditionedBrownianLaw a
      ((Q : Measure (ℚ → BrownianPath)).map (fun F => orderedRationalPathExtension F a)) := by
  have h := congrArg (fun R : ProbabilityMeasure BrownianPath => (R : Measure BrownianPath))
    (orderedRationalPathExtension_map_eq_radial Q hgood hrational a ha)
  change (Q : Measure (ℚ → BrownianPath)).map (fun F => orderedRationalPathExtension F a) =
    (negativeRogersPitmanWienerProbability a : Measure BrownianPath) at h
  rw [h]
  exact hradial a ha


end DOZZ.Proofs
