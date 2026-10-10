/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsOrderedTwoSidedConditionedCoupling
public import DOZZ.Brownian.ConditionedFDDUniqueness
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Independent duplication of an ordered conditioned entrance family

The common one-sided family is duplicated on an ordinary two-factor probability product.
The drift-gap estimate itself supplies convergence in the compact-open path topology, so the
zero-drift continuity clause does not require a separate probabilistic continuity assumption.
This module assembles a supplied one-sided family; it does not assert its existence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The negative-path form of the two drift inequalities: `F b t ≤ F a t ≤ F b t + (b - a) t`
for `0 ≤ a ≤ b`. -/
def NegativeEntranceFamilyOrder (F : ℝ → BrownianPath) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ t : ℝ≥0,
    F b t ≤ F a t ∧ F a t ≤ F b t + (b - a) * (t : ℝ)

/-- The positive-path inequalities before reflection. -/
def PositiveEntranceFamilyOrder (F : ℝ → BrownianPath) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ t : ℝ≥0,
    F a t ≤ F b t ∧ F b t ≤ F a t + (b - a) * (t : ℝ)



/-- The two directed inequalities give a symmetric pointwise Lipschitz bound in the drift. -/
theorem negativeEntranceFamilyOrder_abs_sub_le {F : ℝ → BrownianPath}
    (hF : NegativeEntranceFamilyOrder F) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (t : ℝ≥0) : |F a t - F b t| ≤ |a - b| * (t : ℝ) := by
  rcases le_total a b with hab | hba
  · have h := hF a b ha hab t
    rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith [h.2]
  · have h := hF b a hb hba t
    rw [abs_of_nonpos (sub_nonpos.mpr h.1), abs_of_nonneg (sub_nonneg.mpr hba)]
    nlinarith [h.2]

/-- Every compact time set admits one finite time bound. -/
theorem compact_nonnegative_times_bounded (K : Set ℝ≥0) (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∀ t ∈ K, (t : ℝ) ≤ T := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_subtype_val.continuousOn
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro t ht
  exact (hM (mem_image_of_mem (fun t : ℝ≥0 => (t : ℝ)) ht)).trans
    (by linarith [le_max_left M 0])

/-- The drift estimate is uniform on every compact time set. -/
theorem negativeEntranceFamilyOrder_compact_bound {F : ℝ → BrownianPath}
    (hF : NegativeEntranceFamilyOrder F) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {K : Set ℝ≥0} {T : ℝ} (hT : ∀ t ∈ K, (t : ℝ) ≤ T) :
    ∀ t ∈ K, dist (F a t) (F b t) ≤ |a - b| * T := by
  intro t ht
  rw [Real.dist_eq]
  exact (negativeEntranceFamilyOrder_abs_sub_le hF ha hb t).trans
    (mul_le_mul_of_nonneg_left (hT t ht) (abs_nonneg _))

/-- A convergent sequence or net of nonnegative drifts converges uniformly on each compact time
set. This implication uses only the simultaneous drift inequality. -/
theorem negativeEntranceFamilyOrder_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {F : ℝ → BrownianPath}
    (hF : NegativeEntranceFamilyOrder F) {v : ι → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ᶠ i in l, 0 ≤ v i) (hva : Tendsto v l (𝓝 a))
    (K : Set ℝ≥0) (hK : IsCompact K) :
    TendstoUniformlyOn (fun i t => F (v i) t) (F a) l K := by
  obtain ⟨T, hTpos, hT⟩ := compact_nonnegative_times_bounded K hK
  have hlim : Tendsto (fun i => |a - v i| * T) l (𝓝 (0 : ℝ)) := by
    simpa using (((tendsto_const_nhds (x := a)).sub hva).abs.mul_const T)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hv, hlim.eventually (gt_mem_nhds hε)] with i hi hεi
  intro t ht
  exact (negativeEntranceFamilyOrder_compact_bound hF ha hi hT t ht).trans_lt hεi

/-- Compact-time convergence is convergence in the continuous-path carrier `BrownianPath`. -/
theorem negativeEntranceFamilyOrder_tendsto
    {ι : Type*} {l : Filter ι} {F : ℝ → BrownianPath}
    (hF : NegativeEntranceFamilyOrder F) {v : ι → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ᶠ i in l, 0 ≤ v i) (hva : Tendsto v l (𝓝 a)) :
    Tendsto (fun i => F (v i)) l (𝓝 (F a)) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  exact negativeEntranceFamilyOrder_tendstoUniformlyOn hF ha hv hva K hK

/-- The right limit at zero follows directly from the order estimate. -/
theorem negativeEntranceFamilyOrder_tendsto_zero {F : ℝ → BrownianPath}
    (hF : NegativeEntranceFamilyOrder F) :
    Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := by
  apply negativeEntranceFamilyOrder_tendsto hF le_rfl
  · have hpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    exact hpos.mono fun _ h => h.le
  · exact tendsto_id.mono_left nhdsWithin_le_nhds


/-- The canonical two-copy map on the product sample space. -/
def independentEntranceCopies {Ω : Type*} (F : ℝ → Ω → BrownianPath)
    (a : ℝ) (ω : Ω × Ω) : BrownianPath × BrownianPath :=
  (F a ω.1, F a ω.2)



/-- Transporting a characterized entrance process preserves its exact path law. -/
theorem negativeConditionedBrownianProcess_comp_measurePreserving
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {G : Ξ → Ω}
    (hG : MeasurePreserving G Q P) {F : Ω → BrownianPath} {a : ℝ}
    (hF : IsNegativeConditionedBrownianProcess P F a) :
    IsNegativeConditionedBrownianProcess Q (fun ω => F (G ω)) a := by
  have hmeas : AEMeasurable (fun ω => F (G ω)) Q :=
    hF.1.comp_quasiMeasurePreserving hG.quasiMeasurePreserving
  refine ⟨hmeas, ?_⟩
  have hcomp : Q.map (fun ω => F (G ω)) = P.map F := by
    rw [← hG.map_eq]
    exact (AEMeasurable.map_map_of_aemeasurable
      (by simpa only [hG.map_eq] using hF.1) hG.measurable.aemeasurable).symm
  rw [hcomp]
  exact hF.2

/-- The first copy has exactly the prescribed entrance process law. -/
theorem independentEntranceCopies_first_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath} {a : ℝ}
    (hF : IsNegativeConditionedBrownianProcess P (F a) a) :
    IsNegativeConditionedBrownianProcess (P.prod P)
      (fun ω => (independentEntranceCopies F a ω).1) a :=
  negativeConditionedBrownianProcess_comp_measurePreserving measurePreserving_fst hF

/-- The second copy has the same exact entrance process law. -/
theorem independentEntranceCopies_second_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath} {a : ℝ}
    (hF : IsNegativeConditionedBrownianProcess P (F a) a) :
    IsNegativeConditionedBrownianProcess (P.prod P)
      (fun ω => (independentEntranceCopies F a ω).2) a :=
  negativeConditionedBrownianProcess_comp_measurePreserving measurePreserving_snd hF

/-- The two whole paths are independent, rather than merely their fixed-time evaluations. -/
theorem independentEntranceCopies_indep
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath} {a : ℝ} (hF : AEMeasurable (F a) P) :
    IndepFun (fun ω => (independentEntranceCopies F a ω).1)
      (fun ω => (independentEntranceCopies F a ω).2) (P.prod P) :=
  indepFun_prod₀ hF hF

/-- The two-sided process characterization `DOZZ.IsTwoSidedConditionedBrownianProcess` from the
actual product construction. -/
theorem independentEntranceCopies_twoSided
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath} {a : ℝ}
    (hF : IsNegativeConditionedBrownianProcess P (F a) a) :
    IsTwoSidedConditionedBrownianProcess (P.prod P) (independentEntranceCopies F a) a :=
  ⟨independentEntranceCopies_first_law hF,
    independentEntranceCopies_second_law hF, independentEntranceCopies_indep hF.1⟩

/-- Almost sure simultaneous order is lifted separately along the two measure-preserving
projections. No uncountable intersection of drift-dependent null events is taken. -/
theorem independentEntranceCopies_order_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath}
    (horder : ∀ᵐ ω ∂P, NegativeEntranceFamilyOrder (fun a => F a ω)) :
    ∀ᵐ ω ∂P.prod P,
      NegativeEntranceFamilyOrder (fun a => F a ω.1) ∧
      NegativeEntranceFamilyOrder (fun a => F a ω.2) := by
  have hfst := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae horder
  have hsnd := (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae horder
  exact hfst.and hsnd

/-- Both components converge at zero on the same event on which their order estimates hold. -/
theorem independentEntranceCopies_tendsto_zero
    {Ω : Type*} {F : ℝ → Ω → BrownianPath} {ω : Ω × Ω}
    (hfirst : NegativeEntranceFamilyOrder (fun a => F a ω.1))
    (hsecond : NegativeEntranceFamilyOrder (fun a => F a ω.2)) :
    Tendsto (fun a => independentEntranceCopies F a ω) (𝓝[>] 0)
      (𝓝 (independentEntranceCopies F 0 ω)) :=
  (negativeEntranceFamilyOrder_tendsto_zero hfirst).prodMk_nhds
    (negativeEntranceFamilyOrder_tendsto_zero hsecond)

/-- Every clause of the ordered two-sided characterization
`DOZZ.IsOrderedTwoSidedConditionedCoupling` is assembled from a supplied one-sided entrance
family with one simultaneous order event. -/
theorem independentEntranceCopies_isOrdered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath}
    (hlaw : ∀ a : ℝ, 0 ≤ a → IsNegativeConditionedBrownianProcess P (F a) a)
    (horder : ∀ᵐ ω ∂P, NegativeEntranceFamilyOrder (fun a => F a ω)) :
    IsOrderedTwoSidedConditionedCoupling (P.prod P) (independentEntranceCopies F) := by
  refine ⟨fun a ha => independentEntranceCopies_twoSided (hlaw a ha), ?_⟩
  filter_upwards [independentEntranceCopies_order_ae horder] with ω hω
  refine ⟨?_, independentEntranceCopies_tendsto_zero hω.1 hω.2⟩
  intro a b ha hab t
  have h₁ := hω.1 a b ha hab t
  have h₂ := hω.2 a b ha hab t
  exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩


/-- The joint fixed-drift law is the product of the full entrance path laws. -/
theorem independentEntranceCopies_map
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → BrownianPath} {a : ℝ} (hF : AEMeasurable (F a) P) :
    (P.prod P).map (independentEntranceCopies F a) = (P.map (F a)).prod (P.map (F a)) := by
  have hfst := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving
  have hsnd := (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving
  have hm₁ : AEMeasurable (fun ω : Ω × Ω => F a ω.1) (P.prod P) :=
    hF.comp_quasiMeasurePreserving hfst
  have hm₂ : AEMeasurable (fun ω : Ω × Ω => F a ω.2) (P.prod P) :=
    hF.comp_quasiMeasurePreserving hsnd
  have heq₁ : (P.prod P).map (fun ω => F a ω.1) = P.map (F a) := by
    calc
      _ = ((P.prod P).map Prod.fst).map (F a) :=
        (AEMeasurable.map_map_of_aemeasurable
          (by simpa using hF) measurable_fst.aemeasurable).symm
      _ = _ := by simp
  have heq₂ : (P.prod P).map (fun ω => F a ω.2) = P.map (F a) := by
    calc
      _ = ((P.prod P).map Prod.snd).map (F a) :=
        (AEMeasurable.map_map_of_aemeasurable
          (by simpa using hF) measurable_snd.aemeasurable).symm
      _ = _ := by simp
  change (P.prod P).map (fun ω => (F a ω.1, F a ω.2)) = _
  rw [(independentEntranceCopies_indep hF).map_prod_eq_prod_map_map hm₁ hm₂,
    heq₁, heq₂]

/-- Any countable set of drifts has measurable whole-family evaluations. This is the carrier
used for the rational-drift limit, before extending to every real drift. -/
theorem aemeasurable_countable_entrance_family
    {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    {P : Measure Ω} {F : ℝ → Ω → BrownianPath} (v : J → ℝ)
    (hF : ∀ j, AEMeasurable (F (v j)) P) :
    AEMeasurable (fun ω j => F (v j) ω) P :=
  aemeasurable_pi_iff.mpr hF


/-- Changing a random path on a null set leaves its characterized entrance law unchanged. -/
theorem negativeConditionedBrownianProcess_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F G : Ω → BrownianPath} {a : ℝ}
    (hF : IsNegativeConditionedBrownianProcess P F a) (hFG : F =ᵐ[P] G) :
    IsNegativeConditionedBrownianProcess P G a := by
  refine ⟨hF.1.congr hFG, ?_⟩
  rw [← Measure.map_congr hFG]
  exact hF.2



/-- The closed constraint set on a countable family of path coordinates. The drift carrier
may be rational; every time is retained in the closed constraints. -/
def negativeEntranceOrderSet {J : Type*} (v : J → ℝ) : Set (J → BrownianPath) :=
  {F | ∀ i j, 0 ≤ v i → v i ≤ v j → ∀ t : ℝ≥0,
    F j t ≤ F i t ∧ F i t ≤ F j t + (v j - v i) * (t : ℝ)}

/-- The all-time constraints persist under joint weak limits because their support set is
closed in the product of compact-open path spaces. -/
theorem isClosed_negativeEntranceOrderSet {J : Type*} (v : J → ℝ) :
    IsClosed (negativeEntranceOrderSet v) := by
  classical
  simp only [negativeEntranceOrderSet, ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro t
  have hi : Continuous (fun F : J → BrownianPath => F i t) :=
    (continuous_eval_const t).comp (continuous_apply i)
  have hj : Continuous (fun F : J → BrownianPath => F j t) :=
    (continuous_eval_const t).comp (continuous_apply j)
  exact (isClosed_le hj hi).inter (isClosed_le hi (hj.add continuous_const))







end DOZZ.Proofs
