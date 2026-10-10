/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.FirstHitFiniteDensity
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Exact first-hit laws selected by lifetime cells

A countable measurable selector partitions a nonnegative integral into its
disjoint measurable fibers. On every fiber, its selected finite observation
tuple is deterministic. Restricting the proved finite ordered marked law to
a lifetime cell lying beyond its last observation gives exactly the same
restriction of its full product-density measure.

Summing these actual cell identities identifies the entire law selected by
the lifetime. Both the selected observation map and the selected density are
measurable by their countable families. The actual selected pushforward equals
its selected density measure on the prescribed lifetime domain. That density
measure is finite because it is the restricted Brownian observation law.

For the reversal grid, round the real lifetime upward to its dyadic ceiling.
Clip every deterministic grid horizon above the fixed localization cutoff;
this makes every tuple in the countable family positive and ordered, even
when its lifetime cell is empty. On a lifetime above the cutoff, the clipped
selected horizon equals the literal ceiling.

A mesh smaller than the first reversed observation time puts the whole
selected forward tuple strictly before the actual lifetime cell. Every
observation time in that tuple is positive when the cutoff exceeds the last
reversed observation. These are proved geometric facts, rather than inputs
asserting a probabilistic reversal law.

The exact dyadic-cell density identity is then a specialization of the
countable-selector identity for all nonnegative measurable observation tests.
Its density retains the complete finite killed/hitting factors and the actual
absolute lifetime mark. No Markov restart is made at the selected grid time.
Each probabilistic identity is applied at fixed deterministic cell times.

Dyadic widths tend to zero. The lifetime ceilings converge to the input time,
and every selected forward observation time converges to its lifetime-indexed
time. Continuity of each actual path gives convergence of the entire finite
observation tuple together with its unchanged lifetime mark.

Passing the cell densities through a localized integral limit, and identifying
the conditioned last-exit marked law, remain the next proof steps. The grid
law and pathwise convergence alone do not assert the final reversal.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology BigOperators
namespace DOZZ.Proofs

/-- A countable measurable selector partitions every nonnegative integral into its disjoint fibers. -/
theorem brownian_lintegral_selector_fibers {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (A : Set E) (hA : MeasurableSet A) (κ : E → ℕ) (hκ : Measurable κ)
    (F : E → ℝ≥0∞) :
    (∫⁻ z in A, F z ∂μ) = ∑' j, ∫⁻ z in A ∩ {z | κ z = j}, F z ∂μ := by
  have he : A = ⋃ j : ℕ, A ∩ {z | κ z = j} := by
    ext z
    simp only [mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    exact ⟨fun hz => ⟨κ z,hz,rfl⟩,fun ⟨_,hz,_⟩ => hz⟩
  have hm (j : ℕ) : MeasurableSet (A ∩ {z | κ z = j}) := hA.inter (measurableSet_eq_fun hκ measurable_const)
  have hd : Pairwise (Disjoint on (fun j : ℕ => A ∩ {z | κ z = j})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨_,hi⟩ ⟨_,hj⟩
    exact hij (hi.symm.trans hj)
  conv_lhs => rw [he]
  exact lintegral_iUnion hm hd F

/-- The actual observation tuple at fixed absolute times, together with its first-hit lifetime. -/
noncomputable def brownianOrderedFirstHitObservation (a c : ℝ) (n : ℕ) (ts : Fin n → ℝ≥0)
    (p : BrownianPath) : (Fin n → ℝ) × ℝ :=
  ((fun i => c-(p (ts i)+a*(ts i : ℝ))), (firstPassageTime (driftedBrownianPath a p) c : ℝ))

/-- Every fixed absolute-time observation map is measurable on the actual path carrier. -/
theorem measurable_brownianOrderedFirstHitObservation (a c : ℝ) (n : ℕ) (ts : Fin n → ℝ≥0) :
    Measurable (brownianOrderedFirstHitObservation a c n ts) := by
  have hmτ : Measurable (fun p : BrownianPath => (firstPassageTime (driftedBrownianPath a p) c : ℝ)) :=
    NNReal.continuous_coe.measurable.comp ((measurable_firstPassageTime c).comp
      (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)))
  have hmX : Measurable (fun p : BrownianPath => fun i : Fin n => c-(p (ts i)+a*(ts i : ℝ))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_const.sub ((ContinuousMap.measurable_eval _).add measurable_const)
  exact hmX.prodMk hmτ

/-- A finite ordered marked law restricted to any lifetime cell beyond its last observation has exactly the corresponding restriction of its full density. -/
theorem brownianPath_firstHit_ordered_cell_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (ht0 : ∀ i, 0 < ts i) (hts : StrictMono ts)
    (S : Set ℝ) (hS : MeasurableSet S) (hafter : ∀ t ∈ S, (ts (Fin.last n) : ℝ) < t) :
    (P.restrict {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ S}).map
      (brownianOrderedFirstHitObservation a c (n+1) ts) =
      ((volume.prod volume).withDensity (fun z : (Fin (n+1) → ℝ) × ℝ =>
        brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) ts) c z.1 z.2)).restrict {z | z.2 ∈ S} := by
  have hm := measurable_brownianOrderedFirstHitObservation a c (n+1) ts
  have he := brownianPath_firstHit_ordered_density_map P hB a c ha hc n ts ht0 hts
  change (P.restrict {p : BrownianPath | ts (Fin.last n) < firstPassageTime (driftedBrownianPath a p) c}).map
    (brownianOrderedFirstHitObservation a c (n+1) ts) = _ at he
  rw [← he,Measure.restrict_map hm (show MeasurableSet {z : (Fin (n+1) → ℝ) × ℝ | z.2 ∈ S} from hS.preimage measurable_snd)]
  have hsub : (brownianOrderedFirstHitObservation a c (n+1) ts) ⁻¹' {z | z.2 ∈ S} ⊆
      {p : BrownianPath | ts (Fin.last n) < firstPassageTime (driftedBrownianPath a p) c} := by
    intro p hp
    exact NNReal.coe_lt_coe.mp (hafter _ hp)
  rw [Measure.restrict_restrict_of_subset hsub]
  rfl

/-- Every nonnegative test of a finite ordered law in a lifetime cell integrates against its exact cell density. -/
theorem brownianPath_firstHit_ordered_cell_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (ht0 : ∀ i, 0 < ts i) (hts : StrictMono ts)
    (S : Set ℝ) (hS : MeasurableSet S) (hafter : ∀ t ∈ S, (ts (Fin.last n) : ℝ) < t)
    (H : ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ S},
      H (brownianOrderedFirstHitObservation a c (n+1) ts p) ∂P) =
      ∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | z.2 ∈ S},
        brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) ts) c z.1 z.2*H z ∂volume.prod volume := by
  have hm := measurable_brownianOrderedFirstHitObservation a c (n+1) ts
  calc
    _ = ∫⁻ z, H z ∂(P.restrict {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ S}).map
        (brownianOrderedFirstHitObservation a c (n+1) ts) := (lintegral_map hH hm).symm
    _ = ∫⁻ z in {z | z.2 ∈ S}, H z ∂(volume.prod volume).withDensity
        (fun z : (Fin (n+1) → ℝ) × ℝ => brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) ts) c z.1 z.2) := by
      rw [brownianPath_firstHit_ordered_cell_map P hB a c ha hc n ts ht0 hts S hS hafter]
    _ = _ := by
      rw [restrict_withDensity (show MeasurableSet {z : (Fin (n+1) → ℝ) × ℝ | z.2 ∈ S} from hS.preimage measurable_snd),
        lintegral_withDensity_eq_lintegral_mul _
          (measurable_brownianFirstHitFinitePDF_fixed a c (n+1) (brownianFirstHitElapsed (n+1) ts)) hH]
      simp only [Pi.mul_apply]

/-- A measurable lifetime selector chooses a finite observation tuple from a countable family. -/
noncomputable def brownianSelectedFirstHitObservation (a c : ℝ) (n : ℕ)
    (κ : ℝ → ℕ) (ts : ℕ → Fin n → ℝ≥0) (p : BrownianPath) : (Fin n → ℝ) × ℝ :=
  brownianOrderedFirstHitObservation a c n (ts (κ (firstPassageTime (driftedBrownianPath a p) c : ℝ))) p

/-- The complete actual observation map selected by its lifetime is measurable. -/
theorem measurable_brownianSelectedFirstHitObservation (a c : ℝ) (n : ℕ)
    (κ : ℝ → ℕ) (hκ : Measurable κ) (ts : ℕ → Fin n → ℝ≥0) :
    Measurable (brownianSelectedFirstHitObservation a c n κ ts) := by
  have hmτ : Measurable (fun p : BrownianPath => (firstPassageTime (driftedBrownianPath a p) c : ℝ)) :=
    NNReal.continuous_coe.measurable.comp ((measurable_firstPassageTime c).comp
      (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)))
  have hm : Measurable (fun z : ℕ × BrownianPath => brownianOrderedFirstHitObservation a c n (ts z.1) z.2) :=
    measurable_from_prod_countable_right (fun j => measurable_brownianOrderedFirstHitObservation a c n (ts j))
  exact hm.comp ((hκ.comp hmτ).prodMk measurable_id)

/-- The countably selected complete finite density is a measurable function of states and absolute lifetime. -/
theorem measurable_brownianSelectedFirstHitPDF (a c : ℝ) (n : ℕ)
    (κ : ℝ → ℕ) (hκ : Measurable κ) (ts : ℕ → Fin n → ℝ≥0) :
    Measurable (fun z : (Fin n → ℝ) × ℝ =>
      brownianFirstHitFinitePDF a n (brownianFirstHitElapsed n (ts (κ z.2))) c z.1 z.2) := by
  have hm : Measurable (fun z : ℕ × ((Fin n → ℝ) × ℝ) =>
      brownianFirstHitFinitePDF a n (brownianFirstHitElapsed n (ts z.1)) c z.2.1 z.2.2) :=
    measurable_from_prod_countable_right (fun j =>
      measurable_brownianFirstHitFinitePDF_fixed a c n (brownianFirstHitElapsed n (ts j)))
  exact hm.comp ((hκ.comp measurable_snd).prodMk measurable_id)

/-- Countably selected deterministic observation tuples have their exact selected density law whenever every selected observation precedes the actual lifetime cell. -/
theorem brownianPath_firstHit_selected_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (κ : ℝ → ℕ) (hκ : Measurable κ) (ts : ℕ → Fin (n+1) → ℝ≥0)
    (ht0 : ∀ j i, 0 < ts j i) (hts : ∀ j, StrictMono (ts j))
    (A : Set ℝ) (hA : MeasurableSet A) (hafter : ∀ t ∈ A, (ts (κ t) (Fin.last n) : ℝ) < t)
    (H : ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ A},
      H (brownianSelectedFirstHitObservation a c (n+1) κ ts p) ∂P) =
      ∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | z.2 ∈ A},
        brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) (ts (κ z.2))) c z.1 z.2*H z ∂volume.prod volume := by
  have hmτ : Measurable (fun p : BrownianPath => (firstPassageTime (driftedBrownianPath a p) c : ℝ)) :=
    NNReal.continuous_coe.measurable.comp ((measurable_firstPassageTime c).comp
      (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)))
  rw [brownian_lintegral_selector_fibers P {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ A}
      (hA.preimage hmτ) (fun p => κ (firstPassageTime (driftedBrownianPath a p) c : ℝ))
      (hκ.comp hmτ),
    brownian_lintegral_selector_fibers (volume.prod volume) {z : (Fin (n+1) → ℝ) × ℝ | z.2 ∈ A}
      (hA.preimage measurable_snd) (fun z => κ z.2)
      (hκ.comp measurable_snd)]
  apply tsum_congr
  intro j
  let S : Set ℝ := A ∩ {t | κ t = j}
  have hS : MeasurableSet S := hA.inter (measurableSet_eq_fun hκ measurable_const)
  have hlast : ∀ t ∈ S, (ts j (Fin.last n) : ℝ) < t := by
    intro t ht
    have hh := hafter t ht.1
    rw [ht.2] at hh
    exact hh
  change (∫⁻ p in {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ S},
      H (brownianSelectedFirstHitObservation a c (n+1) κ ts p) ∂P) =
    ∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | z.2 ∈ S},
      brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) (ts (κ z.2))) c z.1 z.2*H z ∂volume.prod volume
  calc
    _ = ∫⁻ p in {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ S},
        H (brownianOrderedFirstHitObservation a c (n+1) (ts j) p) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hS.preimage hmτ)] with p hp
      dsimp [brownianSelectedFirstHitObservation]
      rw [hp.2]
    _ = ∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | z.2 ∈ S},
        brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) (ts j)) c z.1 z.2*H z ∂volume.prod volume :=
      brownianPath_firstHit_ordered_cell_lintegral P hB a c ha hc n (ts j) (ht0 j) (hts j) S hS hlast H hH
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hS.preimage measurable_snd)] with z hz
      rw [hz.2]

/-- A dyadic lifetime-cell index, defined measurably on the whole real time axis. -/
noncomputable def brownianLifetimeCellIndex (m : ℕ) (t : ℝ) : ℕ :=
  Nat.ceil (Real.toNNReal t*brownianDyadicMesh m)

/-- The dyadic lifetime ceiling, without any stopping-time assertion. -/
noncomputable def brownianLifetimeCeiling (m : ℕ) (t : ℝ) : ℝ≥0 :=
  (brownianLifetimeCellIndex m t : ℝ≥0)/brownianDyadicMesh m

/-- The dyadic lifetime index is a measurable countable selector. -/
theorem measurable_brownianLifetimeCellIndex (m : ℕ) : Measurable (brownianLifetimeCellIndex m) := by
  exact Nat.measurable_ceil.comp (measurable_real_toNNReal.mul_const _)


/-- The dyadic lifetime ceiling is at least its nonnegative input time. -/
theorem brownianLifetimeCeiling_lower (m : ℕ) (t : ℝ) :
    Real.toNNReal t ≤ brownianLifetimeCeiling m t := by
  have hq : 0 < brownianDyadicMesh m := pow_pos (by norm_num : (0 : ℝ≥0) < 2) m
  apply (le_div_iff₀ hq).mpr
  exact_mod_cast Nat.le_ceil (Real.toNNReal t*brownianDyadicMesh m)

/-- The lifetime ceiling differs from its input by at most one dyadic mesh interval. -/
theorem brownianLifetimeCeiling_upper (m : ℕ) (t : ℝ) :
    brownianLifetimeCeiling m t ≤ Real.toNNReal t+(brownianDyadicMesh m)⁻¹ := by
  have hq : 0 < brownianDyadicMesh m := pow_pos (by norm_num : (0 : ℝ≥0) < 2) m
  apply (div_le_iff₀ hq).mpr
  have hc : (Nat.ceil (Real.toNNReal t*brownianDyadicMesh m) : ℝ≥0) ≤ Real.toNNReal t*brownianDyadicMesh m+1 := by
    calc
      _ ≤ (Nat.floor (Real.toNNReal t*brownianDyadicMesh m) : ℝ≥0)+1 := by
        exact_mod_cast Nat.ceil_le_floor_add_one (Real.toNNReal t*brownianDyadicMesh m)
      _ ≤ _ := add_le_add (Nat.floor_le zero_le) le_rfl
  change (Nat.ceil (Real.toNNReal t*brownianDyadicMesh m) : ℝ≥0) ≤
    (Real.toNNReal t+(brownianDyadicMesh m)⁻¹)*brownianDyadicMesh m
  rw [add_mul,inv_mul_cancel₀ hq.ne']
  exact hc

/-- Dyadic mesh widths tend to zero. -/
theorem tendsto_brownianLifetimeMesh_zero :
    Tendsto (fun m : ℕ => (brownianDyadicMesh m)⁻¹) atTop (𝓝 0) := by
  have he : (fun m : ℕ => (brownianDyadicMesh m)⁻¹) = fun m => (1/2 : ℝ≥0)^m := by
    funext m
    simp only [brownianDyadicMesh,inv_pow,one_div]
  rw [he]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Every dyadic lifetime ceiling converges to the nonnegative input time. -/
theorem tendsto_brownianLifetimeCeiling (t : ℝ) :
    Tendsto (fun m => brownianLifetimeCeiling m t) atTop (𝓝 (Real.toNNReal t)) := by
  have hu : Tendsto (fun m => Real.toNNReal t+(brownianDyadicMesh m)⁻¹) atTop (𝓝 (Real.toNNReal t)) := by
    simpa only [add_zero] using tendsto_const_nhds.add tendsto_brownianLifetimeMesh_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun m => brownianLifetimeCeiling_lower m t) (fun m => brownianLifetimeCeiling_upper m t)

/-- A countable grid horizon is clipped above the localization cutoff. -/
noncomputable def brownianLifetimeGridHorizon (b : ℝ≥0) (m j : ℕ) : ℝ≥0 :=
  max b ((j : ℝ≥0)/brownianDyadicMesh m)

/-- On a lifetime above the cutoff, its selected clipped grid horizon is exactly its ceiling. -/
theorem brownianLifetimeGridHorizon_selected (b : ℝ≥0) (m : ℕ) (t : ℝ) (hbt : (b : ℝ) < t) :
    brownianLifetimeGridHorizon b m (brownianLifetimeCellIndex m t) = brownianLifetimeCeiling m t := by
  apply max_eq_right
  have hb : b ≤ Real.toNNReal t := by
    exact NNReal.coe_le_coe.mp (by rw [Real.coe_toNNReal t (le_of_lt ((NNReal.coe_nonneg b).trans_lt hbt))];exact hbt.le)
  exact hb.trans (brownianLifetimeCeiling_lower m t)

/-- The deterministic forward observation times attached to a reversed-time tuple in a lifetime cell. -/
noncomputable def brownianReversalGridTimes (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (b : ℝ≥0) (m j : ℕ) : Fin (n+1) → ℝ≥0 :=
  fun i => brownianLifetimeGridHorizon b m j-ss i.rev

/-- Every clipped-grid forward observation time is positive above the last reversed observation. -/
theorem brownianReversalGridTimes_pos (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (b : ℝ≥0) (hb : ss (Fin.last n) < b) (m j : ℕ) (i : Fin (n+1)) :
    0 < brownianReversalGridTimes n ss b m j i := by
  apply tsub_pos_iff_lt.mpr
  exact ((hss.monotone (Fin.le_last i.rev)).trans_lt hb).trans_le (le_max_left _ _)

/-- The deterministic forward times in every clipped cell are strictly ordered. -/
theorem strictMono_brownianReversalGridTimes (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (b : ℝ≥0) (hb : ss (Fin.last n) < b) (m j : ℕ) :
    StrictMono (brownianReversalGridTimes n ss b m j) := by
  intro i k hik
  have hs := hss (Fin.rev_lt_rev.mpr hik)
  have hi : ss i.rev ≤ brownianLifetimeGridHorizon b m j :=
    ((hss.monotone (Fin.le_last i.rev)).trans hb.le).trans (le_max_left _ _)
  change brownianLifetimeGridHorizon b m j-ss i.rev < brownianLifetimeGridHorizon b m j-ss k.rev
  exact tsub_lt_tsub_left_of_le hi hs

/-- With a mesh smaller than the first reversed observation time, every selected forward observation lies strictly before its lifetime cell. -/
theorem brownianReversalGridTimes_last_lt_lifetime (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (b : ℝ≥0) (hb : ss (Fin.last n) < b) (m : ℕ)
    (hmesh : (brownianDyadicMesh m)⁻¹ < ss 0) (t : ℝ) (hbt : (b : ℝ) < t) :
    (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m t) (Fin.last n) : ℝ) < t := by
  have hs0 : ss 0 ≤ brownianLifetimeGridHorizon b m (brownianLifetimeCellIndex m t) :=
    ((hss.monotone (Fin.zero_le _)).trans hb.le).trans (le_max_left _ _)
  have ht : 0 ≤ t := (NNReal.coe_nonneg b).trans hbt.le
  have hceil : (brownianLifetimeCeiling m t : ℝ) ≤ t+((brownianDyadicMesh m)⁻¹ : ℝ) := by
    have he := NNReal.coe_le_coe.mpr (brownianLifetimeCeiling_upper m t)
    rwa [NNReal.coe_add,Real.coe_toNNReal t ht] at he
  have hδ : ((brownianDyadicMesh m)⁻¹ : ℝ) < (ss 0 : ℝ) := NNReal.coe_lt_coe.mpr hmesh
  change ((brownianLifetimeGridHorizon b m (brownianLifetimeCellIndex m t)-ss (Fin.last n).rev : ℝ≥0) : ℝ) < t
  rw [Fin.rev_last,NNReal.coe_sub hs0,brownianLifetimeGridHorizon_selected b m t hbt]
  linarith

/-- The exact dyadic lifetime-cell approximation law follows from countable selection of the actual deterministic finite densities. -/
theorem brownianPath_firstHit_reversal_grid_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (b : ℝ≥0) (hb : ss (Fin.last n) < b)
    (m : ℕ) (hmesh : (brownianDyadicMesh m)⁻¹ < ss 0)
    (H : ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : BrownianPath | (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)},
      H (brownianSelectedFirstHitObservation a c (n+1) (brownianLifetimeCellIndex m)
        (brownianReversalGridTimes n ss b m) p) ∂P) =
      ∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | (b : ℝ) < z.2},
        brownianFirstHitFinitePDF a (n+1)
          (brownianFirstHitElapsed (n+1) (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2)))
          c z.1 z.2*H z ∂volume.prod volume :=
  brownianPath_firstHit_selected_lintegral P hB a c ha hc n (brownianLifetimeCellIndex m)
    (measurable_brownianLifetimeCellIndex m) (brownianReversalGridTimes n ss b m)
    (brownianReversalGridTimes_pos n ss hss b hb m)
    (strictMono_brownianReversalGridTimes n ss hss b hb m) (Ioi (b : ℝ)) measurableSet_Ioi
    (brownianReversalGridTimes_last_lt_lifetime n ss hss b hb m hmesh) H hH

/-- The countably selected actual finite observation law is the corresponding selected density measure on its lifetime domain. -/
theorem brownianPath_firstHit_selected_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (κ : ℝ → ℕ) (hκ : Measurable κ) (ts : ℕ → Fin (n+1) → ℝ≥0)
    (ht0 : ∀ j i, 0 < ts j i) (hts : ∀ j, StrictMono (ts j))
    (A : Set ℝ) (hA : MeasurableSet A) (hafter : ∀ t ∈ A, (ts (κ t) (Fin.last n) : ℝ) < t) :
    (P.restrict {p : BrownianPath | (firstPassageTime (driftedBrownianPath a p) c : ℝ) ∈ A}).map
      (brownianSelectedFirstHitObservation a c (n+1) κ ts) =
      ((volume.prod volume).restrict {z : (Fin (n+1) → ℝ) × ℝ | z.2 ∈ A}).withDensity
        (fun z => brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) (ts (κ z.2))) c z.1 z.2) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (measurable_brownianSelectedFirstHitObservation a c (n+1) κ hκ ts),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_brownianSelectedFirstHitPDF a c (n+1) κ hκ ts) hH]
  simp only [Pi.mul_apply]
  exact brownianPath_firstHit_selected_lintegral P hB a c ha hc n κ hκ ts ht0 hts A hA hafter H hH


/-- Every selected deterministic forward grid time converges to its lifetime-indexed forward time. -/
theorem tendsto_brownianReversalGridTimes_selected (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (b : ℝ≥0) (t : ℝ) (hbt : (b : ℝ) < t) (i : Fin (n+1)) :
    Tendsto (fun m => brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m t) i)
      atTop (𝓝 (Real.toNNReal t-ss i.rev)) := by
  have he : (fun m => brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m t) i) =
      fun m => brownianLifetimeCeiling m t-ss i.rev := by
    funext m
    unfold brownianReversalGridTimes
    rw [brownianLifetimeGridHorizon_selected b m t hbt]
  rw [he]
  exact (tendsto_brownianLifetimeCeiling t).sub tendsto_const_nhds

/-- The actual complete grid observation and lifetime mark converge pathwise to their lifetime-indexed observations. -/
theorem tendsto_brownianSelectedFirstHitObservation_grid (a c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (b : ℝ≥0) (p : BrownianPath)
    (hp : (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)) :
    Tendsto (fun m => brownianSelectedFirstHitObservation a c (n+1) (brownianLifetimeCellIndex m)
      (brownianReversalGridTimes n ss b m) p) atTop
      (𝓝 ((fun i => c-(p (firstPassageTime (driftedBrownianPath a p) c-ss i.rev)+
        a*((firstPassageTime (driftedBrownianPath a p) c-ss i.rev : ℝ≥0) : ℝ))),
        (firstPassageTime (driftedBrownianPath a p) c : ℝ))) := by
  let τ := firstPassageTime (driftedBrownianPath a p) c
  have ht (i : Fin (n+1)) : Tendsto
      (fun m => brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m (τ : ℝ)) i)
        atTop (𝓝 (τ-ss i.rev)) := by
    simpa only [Real.toNNReal_coe] using tendsto_brownianReversalGridTimes_selected n ss b (τ : ℝ) hp i
  have hs : Tendsto (fun m => fun i : Fin (n+1) =>
      c-(p (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m (τ : ℝ)) i)+
        a*(brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m (τ : ℝ)) i : ℝ))) atTop
      (𝓝 (fun i => c-(p (τ-ss i.rev)+a*((τ-ss i.rev : ℝ≥0) : ℝ)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have heval := (p.continuous.tendsto (τ-ss i.rev)).comp (ht i)
    have hreal := (NNReal.continuous_coe.tendsto (τ-ss i.rev)).comp (ht i)
    exact (tendsto_const_nhds (x := c)).sub (heval.add ((tendsto_const_nhds (x := a)).mul hreal))
  rw [nhds_prod_eq]
  exact hs.prodMk (tendsto_const_nhds (x := (τ : ℝ)))

end DOZZ.Proofs
