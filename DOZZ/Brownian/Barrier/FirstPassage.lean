/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.Restart
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.Monotone
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
/-- A nonnegative compact initial interval is compact. -/
theorem isCompact_nnreal_Iic (s : ℝ≥0) : IsCompact (Iic s) := by
  have he : Iic s = Icc (0 : ℝ≥0) s := by
    ext u
    exact ⟨fun h => ⟨zero_le,h⟩,fun h => h.2⟩
  rw [he]
  exact isCompact_Icc

/-- Every continuous path is bounded above on a compact initial interval. -/
theorem brownianPath_Iic_bddAbove (p : BrownianPath) (s : ℝ≥0) :
    BddAbove (range (fun u : Iic s => p u)) := by
  have h := ((isCompact_nnreal_Iic s).image p.continuous).bddAbove
  have he : range (fun u : Iic s => p u) = p '' Iic s := by
    ext y
    simp only [mem_range,mem_image,SetCoe.exists]
    constructor
    · rintro ⟨u,hu,h⟩; exact ⟨u,hu,h⟩
    · rintro ⟨u,hu,h⟩; exact ⟨u,hu,h⟩
  rwa [he]

/-- The compact running maximum depends measurably only on the raw history. -/
theorem measurable_brownianPath_runningMaximum (s : ℝ≥0) :
    Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s]
      (fun p : BrownianPath => ⨆ u : Iic s, p u) := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (Iic s)
  let _ := hDc.to_subtype
  have hm (u : D) : Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s] (fun p : BrownianPath => p u.1.1) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le u.1.1 (le_iSup_of_le u.1.2 le_rfl)
  have hmeas := Measurable.iSup hm
  convert hmeas using 1
  funext p
  exact (hDd.ciSup (p.continuous.comp continuous_subtype_val) (brownianPath_Iic_bddAbove p s)).symm

/-- The maximum on a compact initial interval is actually attained. -/
theorem brownianPath_runningMaximum_attained (p : BrownianPath) (s : ℝ≥0) :
    ∃ u : Iic s, (⨆ v : Iic s, p v) = p u := by
  obtain ⟨u,hu,hmax⟩ := (isCompact_nnreal_Iic s).exists_isMaxOn (f := fun u : ℝ≥0 => p u) ⟨s,le_rfl⟩ p.continuous.continuousOn
  refine ⟨⟨u,hu⟩,le_antisymm ?_ (le_ciSup (brownianPath_Iic_bddAbove p s) ⟨u,hu⟩)⟩
  exact ciSup_le (fun v : Iic s => hmax v.2)

/-- The compact crossing event is measurable in the raw history sigma algebra. -/
theorem measurableSet_brownianPath_crossing (s : ℝ≥0) (β : ℝ) :
    MeasurableSet[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s] {p : BrownianPath | ∃ u ≤ s, β ≤ p u} := by
  have he : {p : BrownianPath | ∃ u ≤ s, β ≤ p u} = {p : BrownianPath | β ≤ ⨆ u : Iic s, p u} := by
    ext p
    constructor
    · rintro ⟨u,hu,hβ⟩
      exact hβ.trans (le_ciSup (brownianPath_Iic_bddAbove p s) ⟨u,hu⟩)
    · intro hβ
      obtain ⟨u,hu⟩ := brownianPath_runningMaximum_attained p s
      exact ⟨u.1,u.2,hu ▸ hβ⟩
  rw [he]
  exact measurableSet_le measurable_const (measurable_brownianPath_runningMaximum s)

/-- First passage capped at a finite horizon, with a literal terminal point ensuring nonemptiness. -/
noncomputable def cappedBrownianFirstPassage (β : ℝ) (T : ℝ≥0) (p : BrownianPath) : ℝ≥0 :=
  sInf ({u : ℝ≥0 | u ≤ T ∧ β ≤ p u} ∪ {T})

/-- The capped hit is bounded by its terminal horizon. -/
theorem cappedBrownianFirstPassage_le (β : ℝ) (T : ℝ≥0) (p : BrownianPath) :
    cappedBrownianFirstPassage β T p ≤ T :=
  csInf_le (OrderBot.bddBelow _) (Or.inr (mem_singleton T))

/-- The capped first passage belongs to the compact hitting set or is the terminal horizon. -/
theorem cappedBrownianFirstPassage_mem (β : ℝ) (T : ℝ≥0) (p : BrownianPath) :
    (cappedBrownianFirstPassage β T p ≤ T ∧ β ≤ p (cappedBrownianFirstPassage β T p)) ∨
      cappedBrownianFirstPassage β T p = T := by
  have hclosed : IsClosed ({u : ℝ≥0 | u ≤ T ∧ β ≤ p u} ∪ {T}) :=
    (isClosed_Iic.inter (isClosed_le continuous_const p.continuous)).union isClosed_singleton
  exact hclosed.csInf_mem ⟨T,Or.inr (mem_singleton T)⟩ (OrderBot.bddBelow _)

/-- Capped hitting sublevels are exactly compact crossing events before the horizon. -/
theorem cappedBrownianFirstPassage_le_iff (β : ℝ) (T s : ℝ≥0) (p : BrownianPath) :
    cappedBrownianFirstPassage β T p ≤ s ↔ T ≤ s ∨ ∃ u ≤ s, u ≤ T ∧ β ≤ p u := by
  constructor
  · intro hs
    rcases cappedBrownianFirstPassage_mem β T p with hhit | hT
    · exact Or.inr ⟨_,hs,hhit⟩
    · exact Or.inl (hT ▸ hs)
  · rintro (hT | ⟨u,hus,huT,hβ⟩)
    · exact (cappedBrownianFirstPassage_le β T p).trans hT
    · exact (csInf_le (s := {u : ℝ≥0 | u ≤ T ∧ β ≤ p u} ∪ {T}) (OrderBot.bddBelow _) (Or.inl ⟨huT,hβ⟩)).trans hus

/-- Capped first passage is a stopping time of the raw natural Brownian filtration. -/
theorem cappedBrownianFirstPassage_isStoppingTime (β : ℝ) (T : ℝ≥0) :
    IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t))
      (fun p => (cappedBrownianFirstPassage β T p : WithTop ℝ≥0)) := by
  intro s
  have he : {p : BrownianPath | (cappedBrownianFirstPassage β T p : WithTop ℝ≥0) ≤ s} =
      if T ≤ s then univ else {p : BrownianPath | ∃ u ≤ s, β ≤ p u} := by
    ext p
    simp only [WithTop.coe_le_coe,cappedBrownianFirstPassage_le_iff]
    by_cases hTs : T ≤ s
    · simp [hTs]
    · simp only [hTs,mem_ofPred_eq,false_or]
      exact ⟨fun ⟨u,hus,_,hβ⟩ => ⟨u,hus,hβ⟩,
        fun ⟨u,hus,hβ⟩ => ⟨u,hus,hus.trans (lt_of_not_ge hTs).le,hβ⟩⟩
  rw [he]
  split_ifs
  · exact MeasurableSet.univ
  · exact measurableSet_brownianPath_crossing s β
/-- Before the cap, a path starting strictly below the barrier hits it without overshoot. -/
theorem cappedBrownianFirstPassage_value (β : ℝ) (T : ℝ≥0) (p : BrownianPath)
    (h0 : p 0 < β) (hτ : cappedBrownianFirstPassage β T p < T) :
    p (cappedBrownianFirstPassage β T p) = β := by
  let τ := cappedBrownianFirstPassage β T p
  have hτT : τ ≤ T := cappedBrownianFirstPassage_le β T p
  have hβ : β ≤ p τ := by
    rcases cappedBrownianFirstPassage_mem β T p with h | h
    · exact h.2
    · exact (hτ.ne h).elim
  obtain ⟨u,hu,hpu⟩ := intermediate_value_Icc (a := (0 : ℝ≥0)) (b := τ)
    (f := fun v : ℝ≥0 => p v) zero_le p.continuous.continuousOn ⟨h0.le,hβ⟩
  have hτu : τ ≤ u := csInf_le (s := {u : ℝ≥0 | u ≤ T ∧ β ≤ p u} ∪ {T})
    (OrderBot.bddBelow _) (Or.inl ⟨hu.2.trans hτT,hpu ▸ le_rfl⟩)
  have he : u = τ := le_antisymm hu.2 hτu
  simpa only [he] using hpu

/-- A strict terminal crossing forces the capped hit strictly before the cap. -/
theorem cappedBrownianFirstPassage_lt_of_terminal (β : ℝ) (T : ℝ≥0)
    (p : BrownianPath) (h0 : p 0 < β) (hT : β < p T) :
    cappedBrownianFirstPassage β T p < T := by
  obtain ⟨u,hu,hpu⟩ := intermediate_value_Icc (a := (0 : ℝ≥0)) (b := T)
    (f := fun v : ℝ≥0 => p v) zero_le p.continuous.continuousOn ⟨h0.le,hT.le⟩
  have huT : u < T := lt_of_le_of_ne hu.2 (by intro he; exact hT.ne (he ▸ hpu).symm)
  exact lt_of_le_of_lt (csInf_le (s := {u : ℝ≥0 | u ≤ T ∧ β ≤ p u} ∪ {T})
    (OrderBot.bddBelow _) (Or.inl ⟨hu.2,hpu ▸ le_rfl⟩)) huT

/-- The finite stopping time itself is measurable for its stopped sigma algebra. -/
theorem measurable_finite_stoppingTime_stopped {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Φ : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime Φ (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] τ := by
  apply measurable_of_Iic
  intro s
  simpa only [preimage,mem_Iic,WithTop.coe_le_coe] using hτ.measurableSet_le' s

/-- The full continuous future path is independent of the raw stopped sigma algebra. -/
theorem brownianPath_bounded_restart_indep (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun (t : ℝ≥0) (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) :
    Indep hτ.measurableSpace (MeasurableSpace.comap (fun p => brownianShiftPath (τ p) p)
      (inferInstance : MeasurableSpace BrownianPath)) P := by
  rw [brownianPath_measurableSpace_eq_comap,MeasurableSpace.comap_comp]
  exact brownian_bounded_stopped_process_indep hB (fun t => ContinuousMap.measurable_eval t)
    measurable_brownianPath_evaluation τ hτ T hτT

/-- A stopping-time observable and the full continuous future path are independent. -/
theorem brownianPath_bounded_restart_indepFun {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun (t : ℝ≥0) (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) (X : BrownianPath → E)
    (hX : Measurable[hτ.measurableSpace] X) :
    IndepFun X (fun p => brownianShiftPath (τ p) p) P := by
  apply (Indep_iff _ _ P).mpr
  intro A S hA hS
  exact (Indep_iff _ _ P).mp (brownianPath_bounded_restart_indep P hB τ hτ T hτT)
    A S (hX.comap_le A hA) hS

/-- The joint law of a stopped observable and the future path factors into its actual marginal laws. -/
theorem brownianPath_bounded_restart_joint_map {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun (t : ℝ≥0) (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) (X : BrownianPath → E)
    (hX : Measurable[hτ.measurableSpace] X) :
    P.map (fun p => (X p,brownianShiftPath (τ p) p)) = (P.map X).prod P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  rw [(brownianPath_bounded_restart_indepFun P hB τ hτ T hτT X hX).map_prod_eq_prod_map_map
    (hX.mono hτ.measurableSpace_le le_rfl).aemeasurable hmV.aemeasurable,
    brownianPath_bounded_restart_map P hB τ hτ T hτT]
/-- Centered Brownian motion is symmetric as an actual continuous-path law. -/
theorem brownianPath_neg_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) : P.map (fun p => -p) = P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply brownianPath_measure_eq_of_process_map_eq
  rw [Measure.map_map (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)) measurable_neg]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    ((Measurable.of_eval (fun t => (ContinuousMap.measurable_eval t).neg)).aemeasurable)
    ((Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)).aemeasurable)).mpr
  intro I
  exact (hB.neg.hasLaw I).map_eq.trans (hB.hasLaw I).map_eq.symm

/-- A stopped observable cannot distinguish the future path from its negative. -/
theorem brownianPath_bounded_restart_joint_neg {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun (t : ℝ≥0) (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) (X : BrownianPath → E)
    (hX : Measurable[hτ.measurableSpace] X) :
    P.map (fun p => (X p,brownianShiftPath (τ p) p)) =
      P.map (fun p => (X p,-brownianShiftPath (τ p) p)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  have hn : P.map (fun p => -brownianShiftPath (τ p) p) = P := by
    have he := (Measure.map_map (μ := P) measurable_neg hmV).symm
    rw [brownianPath_bounded_restart_map P hB τ hτ T hτT,brownianPath_neg_map P hB] at he
    simpa only [Function.comp_def] using he
  have he := (brownianPath_bounded_restart_indepFun P hB τ hτ T hτT X hX).neg_right.map_prod_eq_prod_map_map
    (hX.mono hτ.measurableSpace_le le_rfl).aemeasurable hmV.neg.aemeasurable
  simp only [Pi.neg_apply,Pi.neg_def] at he
  rw [hn] at he
  exact (brownianPath_bounded_restart_joint_map P hB τ hτ T hτT X hX).trans he.symm

/-- Evaluating a future path at the random remaining horizon preserves its sign symmetry. -/
theorem brownianPath_bounded_restart_remaining_sign (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun (t : ℝ≥0) (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) :
    P {p | τ p < T ∧ 0 < brownianShiftPath (τ p) p (T-τ p)} =
      P {p | τ p < T ∧ brownianShiftPath (τ p) p (T-τ p) < 0} := by
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  let S : Set (ℝ≥0 × BrownianPath) := {z | z.1 < T ∧ 0 < z.2 (T-z.1)}
  have hS : MeasurableSet S := by
    apply (measurableSet_lt measurable_fst measurable_const).inter
    exact measurableSet_lt measurable_const (measurable_brownianPath_evaluation.comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))
  have he := congrArg (fun μ : Measure (ℝ≥0 × BrownianPath) => μ S)
    (brownianPath_bounded_restart_joint_neg P hB τ hτ T hτT τ
      (measurable_finite_stoppingTime_stopped _ τ hτ))
  rw [Measure.map_apply (hmτ.prodMk hmV) hS,
    Measure.map_apply (show Measurable (fun p => (τ p,-brownianShiftPath (τ p) p)) from hmτ.prodMk hmV.neg) hS] at he
  simpa only [S,preimage,mem_ofPred_eq,ContinuousMap.neg_apply,neg_pos] using he

/-- Reflection at the first hit exchanges strict terminal positions above and below the barrier. -/
theorem brownianPath_firstHit_terminal_reflection (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β) (T : ℝ≥0) :
    P {p | β < p T} =
      P {p | cappedBrownianFirstPassage β T p < T ∧ p T < β} := by
  let τ := cappedBrownianFirstPassage β T
  have hs := brownianPath_bounded_restart_remaining_sign P hB τ
    (cappedBrownianFirstPassage_isStoppingTime β T) T (cappedBrownianFirstPassage_le β T)
  have hupper : {p : BrownianPath | τ p < T ∧ 0 < brownianShiftPath (τ p) p (T-τ p)}
      =ᵐ[P] {p | β < p T} := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    have h0 : p 0 < β := hp ▸ hβ
    have hv (hτ : τ p < T) : brownianShiftPath (τ p) p (T-τ p) = p T-β := by
      dsimp [brownianShiftPath]
      rw [add_tsub_cancel_of_le (cappedBrownianFirstPassage_le β T p),
        cappedBrownianFirstPassage_value β T p h0 hτ]
    apply propext
    constructor
    · rintro ⟨hτ,hv'⟩; rwa [hv hτ,sub_pos] at hv'
    · intro h; have hτ := cappedBrownianFirstPassage_lt_of_terminal β T p h0 h
      exact ⟨hτ,by rw [hv hτ,sub_pos]; exact h⟩
  have hlower : {p : BrownianPath | τ p < T ∧ brownianShiftPath (τ p) p (T-τ p) < 0}
      =ᵐ[P] {p | τ p < T ∧ p T < β} := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    have h0 : p 0 < β := hp ▸ hβ
    by_cases hτ : τ p < T
    · apply propext
      dsimp [brownianShiftPath]
      rw [add_tsub_cancel_of_le (cappedBrownianFirstPassage_le β T p),
        cappedBrownianFirstPassage_value β T p h0 hτ,sub_neg]
    · simp only [hτ,false_and]
  exact (measure_congr hupper).symm.trans (hs.trans (measure_congr hlower))
/-- A nondegenerate Brownian time marginal has no atom at any barrier. -/
theorem brownianPath_terminal_ne_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (T : ℝ≥0) (hT : T ≠ 0) (β : ℝ) :
    ∀ᵐ p ∂P, p T ≠ β := by
  let _ := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hT
  have he : P {p | p T = β} = 0 := by
    have he := (hB.hasLaw_eval T).measure_eq (p := fun x : ℝ => x = β)
      (show MeasurableSet {x : ℝ | x = β} from measurableSet_singleton β)
    exact he.trans (measure_singleton β)
  apply ae_iff.mpr
  simpa only [not_not] using he

/-- The capped first-hit event has twice the upper Gaussian terminal tail. -/
theorem brownianPath_firstHit_probability (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | cappedBrownianFirstPassage β T p < T} = 2*P {p | β < p T} := by
  let τ := cappedBrownianFirstPassage β T
  have hmτ := measurable_finite_brownian_stoppingTime _ τ
    (cappedBrownianFirstPassage_isStoppingTime β T)
  have hu : {p : BrownianPath | τ p < T} =ᵐ[P]
      ({p | β < p T} ∪ {p | τ p < T ∧ p T < β}) := by
    filter_upwards [hB.eval_zero_ae_eq_zero,brownianPath_terminal_ne_ae P hB T hT β] with p hp hn
    apply propext
    constructor
    · intro hτ
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact Or.inr ⟨hτ,hlt⟩
      · exact Or.inl hgt
    · rintro (hgt | ⟨hτ,_⟩)
      · exact cappedBrownianFirstPassage_lt_of_terminal β T p (hp ▸ hβ) hgt
      · exact hτ
  have hd : Disjoint {p : BrownianPath | β < p T} {p | τ p < T ∧ p T < β} := by
    apply disjoint_left.mpr
    intro p hup hlo
    exact (hup.trans hlo.2).false
  rw [measure_congr hu,measure_union hd
    ((measurableSet_lt hmτ measurable_const).inter
      (measurableSet_lt (ContinuousMap.measurable_eval T) measurable_const)),
    ← brownianPath_firstHit_terminal_reflection P hB β hβ T,two_mul]

/-- Crossing by the terminal horizon differs from crossing before it only on an endpoint atom. -/
theorem brownianPath_crossing_ae_firstHit (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    {p : BrownianPath | ∃ u ≤ T, β ≤ p u} =ᵐ[P]
      {p | cappedBrownianFirstPassage β T p < T} := by
  filter_upwards [hB.eval_zero_ae_eq_zero,brownianPath_terminal_ne_ae P hB T hT β] with p hp hn
  apply propext
  constructor
  · rintro ⟨u,hu,hβu⟩
    have hτu : cappedBrownianFirstPassage β T p ≤ u :=
      csInf_le (s := {u : ℝ≥0 | u ≤ T ∧ β ≤ p u} ∪ {T}) (OrderBot.bddBelow _)
        (Or.inl ⟨hu,hβu⟩)
    by_cases hτT : cappedBrownianFirstPassage β T p < T
    · exact hτT
    · have he : cappedBrownianFirstPassage β T p = T :=
        le_antisymm (cappedBrownianFirstPassage_le β T p) (le_of_not_gt hτT)
      have huT : u = T := le_antisymm hu (he ▸ hτu)
      have hbT : β < p T := lt_of_le_of_ne (huT ▸ hβu) hn.symm
      exact cappedBrownianFirstPassage_lt_of_terminal β T p (hp ▸ hβ) hbT
  · intro hτ
    refine ⟨_,(cappedBrownianFirstPassage_le β T p),?_⟩
    exact (cappedBrownianFirstPassage_value β T p (hp ▸ hβ) hτ).ge

/-- The reflection principle for the running maximum of the canonical continuous Brownian path. -/
theorem brownianPath_runningMaximum_reflection (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∃ u ≤ T, β ≤ p u} = 2*P {p | β < p T} := by
  rw [measure_congr (brownianPath_crossing_ae_firstHit P hB β hβ T hT)]
  exact brownianPath_firstHit_probability P hB β hβ T hT
/-- The barrier event is the closed sublevel of the compact running maximum. -/
theorem brownianPath_barrier_iff_runningMaximum (p : BrownianPath) (T : ℝ≥0) (β : ℝ) :
    (∀ u : ℝ≥0, u ≤ T → p u ≤ β) ↔ (⨆ u : Iic T, p u) ≤ β := by
  constructor
  · intro h
    exact ciSup_le (fun u : Iic T => h u.1 u.2)
  · intro h u hu
    exact (le_ciSup (brownianPath_Iic_bddAbove p T) ⟨u,hu⟩).trans h

/-- The barrier event is measurable in the raw terminal history. -/
theorem measurableSet_brownianPath_barrier (T : ℝ≥0) (β : ℝ) :
    MeasurableSet[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) T]
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} := by
  have he : {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} =
      {p | (⨆ u : Iic T, p u) ≤ β} := by
    ext p
    exact brownianPath_barrier_iff_runningMaximum p T β
  rw [he]
  exact measurableSet_le (measurable_brownianPath_runningMaximum T) measurable_const

/-- A strict maximum above the barrier is witnessed by a time in the compact interval. -/
theorem brownianPath_runningMaximum_gt_iff (p : BrownianPath) (T : ℝ≥0) (β : ℝ) :
    β < (⨆ u : Iic T, p u) ↔ ∃ u ≤ T, β < p u := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := brownianPath_runningMaximum_attained p T
    exact ⟨u.1,u.2,hu ▸ h⟩
  · rintro ⟨u,hu,hβ⟩
    exact hβ.trans_le (le_ciSup (brownianPath_Iic_bddAbove p T) ⟨u,hu⟩)

/-- The strict crossing event is measurable in the raw terminal history. -/
theorem measurableSet_brownianPath_strict_crossing (T : ℝ≥0) (β : ℝ) :
    MeasurableSet[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) T]
      {p : BrownianPath | ∃ u ≤ T, β < p u} := by
  have he : {p : BrownianPath | ∃ u ≤ T, β < p u} = {p | β < (⨆ u : Iic T, p u)} := by
    ext p
    exact (brownianPath_runningMaximum_gt_iff p T β).symm
  rw [he]
  exact measurableSet_lt measurable_const (measurable_brownianPath_runningMaximum T)
end DOZZ.Proofs
