/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.GaussianBounds

/-!
# Measurable lifetime-marked Brownian paths

The first-passage infimum is zero when its hitting set is empty. Its full
measurability therefore differs from the stopping-time property proved for capped
hits. Compact crossing tests give joint measurability in the level and path while
preserving that convention exactly.

Last exits are treated through compact level-distance tests and countable horizon
exhaustion. The conditional supremum also has value zero for an unbounded hit set;
the proof handles this case explicitly and makes no stopping-time claim.

Stopping, reversing, translating and recentering act on the literal path carriers.
Their measurability supplies both reversal measurability conjuncts and the
level-dependent first-hit kernel in Williams' statement. This module does not
assert either path-law identity.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs
/-- The compact crossing event is jointly measurable in its level and continuous path. -/
theorem measurableSet_brownianPath_joint_crossing (T : ℝ≥0) :
    MeasurableSet {z : ℝ × BrownianPath | ∃ u ≤ T, z.1 ≤ z.2 u} := by
  have hm : Measurable (fun p : BrownianPath => ⨆ u : Iic T, p u) :=
    (measurable_brownianPath_runningMaximum T).mono
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T) le_rfl
  have he : {z : ℝ × BrownianPath | ∃ u ≤ T, z.1 ≤ z.2 u} =
      {z | z.1 ≤ ⨆ u : Iic T, z.2 u} := by
    ext z
    constructor
    · rintro ⟨u,hu,h⟩
      exact h.trans (le_ciSup (brownianPath_Iic_bddAbove z.2 T) ⟨u,hu⟩)
    · intro h
      obtain ⟨u,hu⟩ := brownianPath_runningMaximum_attained z.2 T
      exact ⟨u.1,u.2,hu ▸ h⟩
  rw [he]
  exact measurableSet_le measurable_fst (hm.comp measurable_snd)

/-- Ever reaching an upper level is a countable union of compact crossing tests. -/
theorem brownianPath_joint_hit_eq_iUnion :
    {z : ℝ × BrownianPath | ∃ u : ℝ≥0, z.1 ≤ z.2 u} =
      ⋃ n : ℕ, {z | ∃ u ≤ (n : ℝ≥0), z.1 ≤ z.2 u} := by
  ext z
  simp only [mem_ofPred_eq,mem_iUnion]
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨n,hn⟩ := exists_nat_ge (u : ℝ)
    exact ⟨n,u,by exact_mod_cast hn,hu⟩
  · rintro ⟨n,u,_,hu⟩
    exact ⟨u,hu⟩

/-- Ever reaching an upper level is jointly measurable in that level and the entire path. -/
theorem measurableSet_brownianPath_joint_hit :
    MeasurableSet {z : ℝ × BrownianPath | ∃ u : ℝ≥0, z.1 ≤ z.2 u} := by
  rw [brownianPath_joint_hit_eq_iUnion]
  exact MeasurableSet.iUnion (fun n => measurableSet_brownianPath_joint_crossing n)

/-- A nonempty upper hitting set contains the literal first-passage time. -/
theorem firstPassageTime_mem (p : BrownianPath) (c : ℝ)
    (h : ∃ u : ℝ≥0, c ≤ p u) : c ≤ p (firstPassageTime p c) := by
  have hc : IsClosed {u : ℝ≥0 | c ≤ p u} := isClosed_le continuous_const p.continuous
  exact hc.csInf_mem h (OrderBot.bddBelow _)

/-- The infimum convention adds the no-hit event to every finite sublevel. -/
theorem firstPassageTime_le_iff (p : BrownianPath) (c : ℝ) (s : ℝ≥0) :
    firstPassageTime p c ≤ s ↔ (¬∃ u : ℝ≥0, c ≤ p u) ∨ ∃ u ≤ s, c ≤ p u := by
  by_cases hh : ∃ u : ℝ≥0, c ≤ p u
  · constructor
    · intro hs
      exact Or.inr ⟨_,hs,firstPassageTime_mem p c hh⟩
    · rintro (hn | ⟨u,hu,hcu⟩)
      · exact (hn hh).elim
      · exact (csInf_le (s := {u : ℝ≥0 | c ≤ p u}) (OrderBot.bddBelow _) hcu).trans hu
  · have he : {u : ℝ≥0 | c ≤ p u} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hh ⟨u,hu⟩
    rw [firstPassageTime,he]
    have hempty : sInf (∅ : Set ℝ≥0) = 0 := NNReal.sInf_empty
    rw [hempty]
    exact ⟨fun _ => Or.inl hh,fun _ => zero_le⟩

/-- The literal first-passage time is jointly measurable, including its no-hit value zero. -/
theorem measurable_firstPassageTime_joint :
    Measurable (fun z : ℝ × BrownianPath => firstPassageTime z.2 z.1) := by
  apply measurable_of_Iic
  intro s
  have he : (fun z : ℝ × BrownianPath => firstPassageTime z.2 z.1) ⁻¹' Iic s =
      {z : ℝ × BrownianPath | ∃ u : ℝ≥0, z.1 ≤ z.2 u}ᶜ ∪
        {z : ℝ × BrownianPath | ∃ u ≤ s, z.1 ≤ z.2 u} := by
    ext z
    simp only [mem_preimage,mem_Iic,firstPassageTime_le_iff,mem_union,mem_compl_iff,mem_ofPred_eq]
  rw [he]
  exact measurableSet_brownianPath_joint_hit.compl.union
    (measurableSet_brownianPath_joint_crossing s)

/-- A fixed-level first-passage time is measurable for the full continuous-path sigma algebra. -/
theorem measurable_firstPassageTime (c : ℝ) : Measurable (fun p => firstPassageTime p c) :=
  measurable_firstPassageTime_joint.comp (measurable_const.prodMk measurable_id)

/-- Stop and hold is jointly continuous in its lifetime and input continuous path. -/
theorem continuous_stopBrownianPath :
    Continuous (fun z : ℝ≥0 × BrownianPath => stopBrownianPath z.2 z.1) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ≥0 × BrownianPath) × ℝ≥0 => z.1.2 (min z.2 z.1.1))
  exact continuous_eval.comp (continuous_fst.snd.prodMk (continuous_snd.min continuous_fst.fst))

/-- The drift definition `DOZZ.driftedBrownianPath` used in the marked paths is the same literal
translation already constructed. -/
theorem driftedBrownianPath_eq (ν : ℝ) (p : BrownianPath) :
    driftedBrownianPath ν p = brownianDriftPath ν p := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The drift map `DOZZ.driftedBrownianPath` is jointly continuous. -/
theorem continuous_driftedBrownianPath :
    Continuous (fun z : ℝ × BrownianPath => driftedBrownianPath z.1 z.2) := by
  simpa only [driftedBrownianPath_eq] using continuous_brownianDriftPath

/-- The positive-drift first-hit segment is jointly measurable in its level and actual input path. -/
theorem measurable_positiveDriftFirstHitSegment_joint (ν : ℝ) :
    Measurable (fun z : ℝ × BrownianPath => positiveDriftFirstHitSegment ν z.1 z.2) := by
  let U : ℝ × BrownianPath → BrownianPath := fun z => driftedBrownianPath ν z.2
  have hmU : Measurable U := continuous_driftedBrownianPath.measurable.comp
    (measurable_const.prodMk measurable_snd)
  have hmτ := measurable_firstPassageTime_joint.comp (measurable_fst.prodMk hmU)
  exact hmτ.prodMk (continuous_stopBrownianPath.measurable.comp (hmτ.prodMk hmU))

/-- Every positive-drift first-hit segment is measurable without a finiteness premise. -/
theorem measurable_positiveDriftFirstHitSegment (ν c : ℝ) :
    Measurable (positiveDriftFirstHitSegment ν c) :=
  (measurable_positiveDriftFirstHitSegment_joint ν).comp (measurable_const.prodMk measurable_id)

/-- Lifetime reversal and recentering are jointly continuous on the actual path carriers. -/
theorem continuous_brownianPath_reverse_recenter :
    Continuous (fun z : (ℝ≥0 × ℝ) × BrownianPath =>
      (⟨fun t => z.2 (z.1.1-min t z.1.1)-z.1.2,by fun_prop⟩ : BrownianPath)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : ((ℝ≥0 × ℝ) × BrownianPath) × ℝ≥0 =>
    z.1.2 (z.1.1.1-min z.2 z.1.1.1)-z.1.1.2)
  exact (continuous_eval.comp (continuous_fst.snd.prodMk
    (continuous_fst.fst.fst.sub (continuous_snd.min continuous_fst.fst.fst)))).sub continuous_fst.fst.snd

/-- The reversed positive first-hit segment has its literal lifetime-marked measurable law. -/
theorem measurable_reversedPositiveFirstHitSegment (ν c : ℝ) :
    Measurable (reversedPositiveFirstHitSegment ν c) := by
  have hmU : Measurable (driftedBrownianPath ν) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hmτ := (measurable_firstPassageTime c).comp hmU
  exact hmτ.prodMk (continuous_brownianPath_reverse_recenter.measurable.comp
    ((hmτ.prodMk measurable_const).prodMk hmU))
/-- Translation without recentering is continuous on the whole continuous-path carrier. -/
noncomputable def brownianTranslatePath (s : ℝ≥0) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p (s+t),p.continuous.comp (continuous_const.add continuous_id)⟩

/-- Joint continuity of literal future evaluation without recentering. -/
theorem continuous_brownianTranslatePath :
    Continuous (fun z : ℝ≥0 × BrownianPath => brownianTranslatePath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ≥0 × BrownianPath) × ℝ≥0 => z.1.2 (z.1.1+z.2))
  exact continuous_eval.comp (continuous_fst.snd.prodMk (continuous_fst.fst.add continuous_snd))

/-- A level-distance test encoded as a literal continuous path. -/
noncomputable def brownianLevelDistancePath (c : ℝ) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => -|p t+c|,(p.continuous.add continuous_const).abs.neg⟩

/-- Level-distance encoding is jointly continuous in the level and path. -/
theorem continuous_brownianLevelDistancePath :
    Continuous (fun z : ℝ × BrownianPath => brownianLevelDistancePath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ × BrownianPath) × ℝ≥0 => -|z.1.2 z.2+z.1.1|)
  exact ((continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)).add continuous_fst.fst).abs.neg

/-- A compact level hit is the zero maximum of the negative level-distance test. -/
theorem brownianPath_compact_levelHit_iff (p : BrownianPath) (c : ℝ) (s T : ℝ≥0) :
    (∃ u ∈ Icc s (s+T), p u = -c) ↔
      (⨆ u : Iic T, brownianLevelDistancePath c (brownianTranslatePath s p) u) = 0 := by
  let q := brownianLevelDistancePath c (brownianTranslatePath s p)
  have hnonpos : (⨆ u : Iic T, q u) ≤ 0 := ciSup_le (fun u => neg_nonpos.mpr (abs_nonneg _))
  constructor
  · rintro ⟨u,hu,hpu⟩
    have hut : u-s ≤ T := (tsub_le_iff_right).mpr (by simpa only [add_comm] using hu.2)
    have hqu : q (u-s) = 0 := by
      change -|p (s+(u-s))+c| = 0
      rw [add_tsub_cancel_of_le hu.1,hpu,neg_add_cancel,abs_zero,neg_zero]
    apply le_antisymm hnonpos
    rw [← hqu]
    exact le_ciSup (brownianPath_Iic_bddAbove q T) ⟨u-s,hut⟩
  · intro hM
    obtain ⟨u,hu⟩ := brownianPath_runningMaximum_attained q T
    refine ⟨s+u.1,⟨le_add_of_nonneg_right (zero_le),add_le_add (α := ℝ≥0) (show s ≤ s from le_rfl) u.2⟩,?_⟩
    have he : q u.1 = 0 := hu.symm.trans hM
    change -|p (s+u.1)+c| = 0 at he
    have hv : p (s+u.1)+c = 0 := abs_eq_zero.mp (neg_eq_zero.mp he)
    linarith

/-- Existence of a level hit on a fixed compact interval is jointly measurable in the level and path. -/
theorem measurableSet_brownianPath_compact_levelHit (s T : ℝ≥0) :
    MeasurableSet {z : ℝ × BrownianPath | ∃ u ∈ Icc s (s+T), z.2 u = -z.1} := by
  have hmM : Measurable (fun p : BrownianPath => ⨆ u : Iic T, p u) :=
    (measurable_brownianPath_runningMaximum T).mono
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T) le_rfl
  have hmT : Measurable (fun z : ℝ × BrownianPath => brownianTranslatePath s z.2) :=
    continuous_brownianTranslatePath.measurable.comp (measurable_const.prodMk measurable_snd)
  have hmD := continuous_brownianLevelDistancePath.measurable.comp (measurable_fst.prodMk hmT)
  have he : {z : ℝ × BrownianPath | ∃ u ∈ Icc s (s+T), z.2 u = -z.1} =
      {z | (⨆ u : Iic T, brownianLevelDistancePath z.1 (brownianTranslatePath s z.2) u) = 0} := by
    ext z
    exact brownianPath_compact_levelHit_iff z.2 z.1 s T
  rw [he]
  exact measurableSet_eq_fun (hmM.comp hmD) measurable_const
/-- Visits strictly after a deterministic time are exhausted by countably many compact interval tests. -/
theorem brownianPath_levelHit_after_eq_iUnion (s : ℝ≥0) :
    {z : ℝ × BrownianPath | ∃ u : ℝ≥0, s < u ∧ z.2 u = -z.1} =
      ⋃ j : ℕ, ⋃ n : ℕ, {z | ∃ u ∈ Icc (s+1/((j : ℝ≥0)+1))
        (s+1/((j : ℝ≥0)+1)+(n : ℝ≥0)), z.2 u = -z.1} := by
  ext z
  simp only [mem_ofPred_eq,mem_iUnion]
  constructor
  · rintro ⟨u,hu,hp⟩
    have hgap : 0 < (u : ℝ)-(s : ℝ) := sub_pos.mpr (by exact_mod_cast hu)
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt hgap
    let ε : ℝ≥0 := 1/((j : ℝ≥0)+1)
    have hε : (ε : ℝ) < (u : ℝ)-(s : ℝ) := by simpa [ε] using hj
    have hsu : s+ε ≤ u := by
      have he : (s : ℝ)+(ε : ℝ) ≤ (u : ℝ) := by linarith
      exact_mod_cast he
    obtain ⟨n,hn⟩ := exists_nat_ge (u : ℝ)
    have hun : u ≤ (n : ℝ≥0) := by exact_mod_cast hn
    exact ⟨j,n,u,⟨hsu,hun.trans (le_add_of_nonneg_left zero_le)⟩,hp⟩
  · rintro ⟨j,n,u,hu,hp⟩
    have hε : (0 : ℝ≥0) < 1/((j : ℝ≥0)+1) := by positivity
    exact ⟨u,(lt_add_of_pos_right s hε).trans_le hu.1,hp⟩

/-- Future level visits are measurable, without treating a last exit as a stopping time. -/
theorem measurableSet_brownianPath_levelHit_after (s : ℝ≥0) :
    MeasurableSet {z : ℝ × BrownianPath | ∃ u : ℝ≥0, s < u ∧ z.2 u = -z.1} := by
  rw [brownianPath_levelHit_after_eq_iUnion]
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun n =>
    measurableSet_brownianPath_compact_levelHit (s+1/((j : ℝ≥0)+1)) n))

/-- Boundedness of the full level-hit set is a countable exhaustion property. -/
theorem brownianPath_levelHits_bddAbove_iff (p : BrownianPath) (c : ℝ) :
    BddAbove {u : ℝ≥0 | p u = -c} ↔
      ∃ n : ℕ, ¬∃ u : ℝ≥0, (n : ℝ≥0) < u ∧ p u = -c := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨n,hn⟩ := exists_nat_ge (b : ℝ)
    refine ⟨n,?_⟩
    rintro ⟨u,hu,hpu⟩
    have hbn : b ≤ (n : ℝ≥0) := by exact_mod_cast hn
    exact ((hb hpu).trans hbn).not_gt hu
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    intro u hpu
    exact le_of_not_gt (fun h => hn ⟨u,h,hpu⟩)

/-- Boundedness of level-hit times is jointly measurable in the level and actual continuous path. -/
theorem measurableSet_brownianPath_levelHits_bddAbove :
    MeasurableSet {z : ℝ × BrownianPath | BddAbove {u : ℝ≥0 | z.2 u = -z.1}} := by
  have he : {z : ℝ × BrownianPath | BddAbove {u : ℝ≥0 | z.2 u = -z.1}} =
      ⋃ n : ℕ, {z : ℝ × BrownianPath | ∃ u : ℝ≥0, (n : ℝ≥0) < u ∧ z.2 u = -z.1}ᶜ := by
    ext z
    simp only [mem_ofPred_eq,mem_iUnion,mem_compl_iff,brownianPath_levelHits_bddAbove_iff]
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurableSet_brownianPath_levelHit_after n).compl)

/-- For a bounded level-hit set the literal last exit is at most `s` exactly when no visit follows `s`. -/
theorem negativeLastExitTime_le_iff_of_bddAbove (p : BrownianPath) (c : ℝ)
    (hb : BddAbove {u : ℝ≥0 | p u = -c}) (s : ℝ≥0) :
    negativeLastExitTime p c ≤ s ↔ ¬∃ u : ℝ≥0, s < u ∧ p u = -c := by
  constructor
  · intro hs
    rintro ⟨u,hu,hpu⟩
    exact ((le_csSup hb hpu).trans hs).not_gt hu
  · intro hn
    by_cases hh : ({u : ℝ≥0 | p u = -c}).Nonempty
    · exact csSup_le hh (fun u hpu => le_of_not_gt (fun hu => hn ⟨u,hu,hpu⟩))
    · have he : {u : ℝ≥0 | p u = -c} = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
      rw [negativeLastExitTime,he,csSup_empty]
      exact zero_le

/-- The full last-exit convention is measurable, including its value for an unbounded hit set. -/
theorem measurable_negativeLastExitTime_joint :
    Measurable (fun z : ℝ × BrownianPath => negativeLastExitTime z.2 z.1) := by
  apply measurable_of_Iic
  intro s
  have he : (fun z : ℝ × BrownianPath => negativeLastExitTime z.2 z.1) ⁻¹' Iic s =
      {z : ℝ × BrownianPath | BddAbove {u : ℝ≥0 | z.2 u = -z.1}}ᶜ ∪
      {z : ℝ × BrownianPath | ∃ u : ℝ≥0, s < u ∧ z.2 u = -z.1}ᶜ := by
    ext z
    simp only [mem_preimage,mem_Iic,mem_union,mem_compl_iff,mem_ofPred_eq]
    by_cases hb : BddAbove {u : ℝ≥0 | z.2 u = -z.1}
    · simp only [hb,not_true_eq_false,false_or]
      exact negativeLastExitTime_le_iff_of_bddAbove z.2 z.1 hb s
    · have hzero : negativeLastExitTime z.2 z.1 = 0 := by
        rw [negativeLastExitTime,csSup_of_not_bddAbove hb,csSup_empty]
        rfl
      simp only [hzero,zero_le,hb,not_false_eq_true,true_or]
  rw [he]
  exact measurableSet_brownianPath_levelHits_bddAbove.compl.union
    (measurableSet_brownianPath_levelHit_after s).compl

/-- Every literal conditioned last-exit segment is measurable on the actual path carrier. -/
theorem measurable_negativeConditionedLastExitSegment (c : ℝ) :
    Measurable (negativeConditionedLastExitSegment c) := by
  have hmτ : Measurable (fun p : BrownianPath => negativeLastExitTime p c) :=
    measurable_negativeLastExitTime_joint.comp ((measurable_const (a := c)).prodMk measurable_id)
  exact hmτ.prodMk (continuous_stopBrownianPath.measurable.comp (hmτ.prodMk measurable_id))
/-- Once a hit occurs before the cap, the capped and uncapped first-passage times are literally
equal. -/
theorem firstPassageTime_eq_capped_of_hit (p : BrownianPath) (c : ℝ) (T : ℝ≥0)
    (h : ∃ u ≤ T, c ≤ p u) : firstPassageTime p c = cappedBrownianFirstPassage c T p := by
  obtain ⟨u,hu,hcu⟩ := h
  have hh : ∃ u : ℝ≥0, c ≤ p u := ⟨u,hcu⟩
  have hτu : firstPassageTime p c ≤ u :=
    csInf_le (s := {u : ℝ≥0 | c ≤ p u}) (OrderBot.bddBelow _) hcu
  have hτT := hτu.trans hu
  apply le_antisymm
  · rcases cappedBrownianFirstPassage_mem c T p with hv | he
    · exact csInf_le (s := {u : ℝ≥0 | c ≤ p u}) (OrderBot.bddBelow _) hv.2
    · rw [he]
      exact hτT
  · exact csInf_le (s := {u : ℝ≥0 | u ≤ T ∧ c ≤ p u} ∪ {T})
      (OrderBot.bddBelow _) (Or.inl ⟨hτT,firstPassageTime_mem p c hh⟩)


/-- The literal lifetime-marked first-hit kernel is measurable for every nonnegative measurable test. -/
theorem measurable_positiveFirstHit_kernel (P : Measure BrownianPath) [SFinite P]
    (ν : ℝ) (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun m : ℝ => ∫⁻ u, F (m,u) ∂P.map (positiveDriftFirstHitSegment ν m)) := by
  have hm : Measurable (fun z : ℝ × BrownianPath => F (z.1,positiveDriftFirstHitSegment ν z.1 z.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_positiveDriftFirstHitSegment_joint ν))
  convert hm.lintegral_prod_right' (ν := P) using 1
  funext m
  exact lintegral_map (hF.comp (measurable_const.prodMk measurable_id))
    (measurable_positiveDriftFirstHitSegment ν m)

/-- The exact measurability conjunct of Williams' kernel identity follows on the maximum reference
law. -/
theorem aemeasurable_positiveFirstHit_kernel (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F) :
    AEMeasurable (fun m : ℝ => ∫⁻ u, F (m,u) ∂P.map (positiveDriftFirstHitSegment ν m))
      (brownianMaximumReferenceLaw ν) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (measurable_positiveFirstHit_kernel P ν F hF).aemeasurable


end DOZZ.Proofs
