/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.FirstHitSelector
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual lifetime-indexed first-hit reversal density

This module closes the first density calculation in the first-hit reversal.
It uses the existing exact dyadic lifetime-cell law and the pathwise
convergence of the complete observation/lifetime tuple. No restart is applied
at a random observation time.

The density is kept in forward coordinate order: coordinate `i` corresponds
to reversed time `ss i.rev`. Its elapsed times are the differences of
`T - ss i.rev`; the finite killed/hitting density therefore retains the final
elapsed time of the source cell formula before taking its limit.

All analytic helpers here are private to that limit. The killed kernel is
jointly continuous at positive elapsed time even on the state boundary: its
Gaussian difference can be written using the positive parts of both states.
Continuity of the complete finite density gives a uniform bound on each
compact observation/lifetime set and a small compact ceiling-offset interval.
Fatou first proves finite mass of the limiting density. Dominated convergence
then identifies every compactly supported nonnegative continuous test.
Regular-measure uniqueness gives the localized pushforward identity, and a
countable exhaustion removes the lifetime gap above the last observation.

The main conclusion is the actual random-lifetime reversed observation
measure, including its lifetime mark. Identifying the conditioned last-exit
measure with the same density and assembling the final stopped-path statement
are separate steps; this module does not assert that statement.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology BigOperators CompactlySupported
namespace DOZZ.Proofs

private theorem killed_eq_positiveParts (a : ℝ) (T : ℝ≥0) (x y : ℝ) :
    brownianKilledTransitionPDF a T x y =
      Real.exp (a*(y-x)-a^2*(T : ℝ)/2)*
        (gaussianPDFReal 0 T (max y 0-max x 0)-gaussianPDFReal 0 T (max y 0+max x 0)) := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · simp only [brownianKilledTransitionPDF,ite_eq_left (show 0 < x ∧ 0 < y from ⟨hx,hy⟩),max_eq_left hx.le,max_eq_left hy.le]
    · have hy0 : y ≤ 0 := not_lt.mp hy
      simp only [brownianKilledTransitionPDF,ite_eq_right (show ¬ (0 < x ∧ 0 < y) from fun h => hy h.2),max_eq_right hy0,
        zero_sub,zero_add,gaussianPDFReal,sub_zero,neg_sq,sub_self,mul_zero]
  · have hx0 : x ≤ 0 := not_lt.mp hx
    simp only [brownianKilledTransitionPDF,ite_eq_right (show ¬ (0 < x ∧ 0 < y) from fun h => hx h.1),max_eq_right hx0,
      sub_zero,add_zero,sub_self,mul_zero]

private theorem killed_continuousAt (a : ℝ) (T : ℝ≥0) (x y : ℝ) (hT : T ≠ 0) :
    ContinuousAt (fun z : ℝ≥0 × (ℝ × ℝ) => brownianKilledTransitionPDF a z.1 z.2.1 z.2.2) (T,(x,y)) := by
  simp_rw [killed_eq_positiveParts]
  have h1 : ContinuousAt (fun z : ℝ≥0 × (ℝ × ℝ) =>
      gaussianPDFReal 0 z.1 (max z.2.2 0-max z.2.1 0)) (T,(x,y)) :=
    (continuousAt_brownian_heatPDF T (max y 0-max x 0) hT).comp_of_eq
      (f := fun z : ℝ≥0 × (ℝ × ℝ) => (z.1, max z.2.2 0-max z.2.1 0))
      (continuous_fst.prodMk ((continuous_snd.snd.max continuous_const).sub
        (continuous_snd.fst.max continuous_const))).continuousAt rfl
  have h2 : ContinuousAt (fun z : ℝ≥0 × (ℝ × ℝ) =>
      gaussianPDFReal 0 z.1 (max z.2.2 0+max z.2.1 0)) (T,(x,y)) :=
    (continuousAt_brownian_heatPDF T (max y 0+max x 0) hT).comp_of_eq
      (f := fun z : ℝ≥0 × (ℝ × ℝ) => (z.1, max z.2.2 0+max z.2.1 0))
      (continuous_fst.prodMk ((continuous_snd.snd.max continuous_const).add
        (continuous_snd.fst.max continuous_const))).continuousAt rfl
  have he : Continuous (fun z : ℝ≥0 × (ℝ × ℝ) => Real.exp (a*(z.2.2-z.2.1)-a^2*(z.1 : ℝ)/2)) := by fun_prop
  exact he.continuousAt.mul (h1.sub h2)

private theorem finiteDensity_continuousAt (a : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0)
    (c : ℝ) (xs : Fin n → ℝ) (t : ℝ) (hds : ∀ i, 0 < ds i)
    (ht : (brownianFirstHitHorizon n ds : ℝ) < t) :
    ContinuousAt (fun z : (Fin n → ℝ≥0) × (ℝ × ((Fin n → ℝ) × ℝ)) =>
      (brownianFirstHitFinitePDF a n z.1 z.2.1 z.2.2.1 z.2.2.2).toReal) (ds,(c,(xs,t))) := by
  induction n generalizing c t with
  | zero =>
    change ContinuousAt (fun z : (Fin 0 → ℝ≥0) × (ℝ × ((Fin 0 → ℝ) × ℝ)) =>
      (ENNReal.ofReal (brownianFirstHitDensity a z.2.1 z.2.2.2)).toReal) _
    simp_rw [ENNReal.toReal_ofReal']
    exact ((continuousAt_brownianFirstHitDensity_joint a c t ht).comp_of_eq
      (continuous_snd.fst.prodMk continuous_snd.snd.snd).continuousAt rfl).max continuousAt_const
  | succ n ih =>
    have hd : Continuous (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => z.1 0) := by fun_prop
    have hx : Continuous (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => z.2.2.1 0) := by fun_prop
    have htaild : Continuous (Fin.tail : (Fin (n+1) → ℝ≥0) → Fin n → ℝ≥0) := by
      apply continuous_pi
      intro i
      exact continuous_apply i.succ
    have htailx : Continuous (Fin.tail : (Fin (n+1) → ℝ) → Fin n → ℝ) := by
      apply continuous_pi
      intro i
      exact continuous_apply i.succ
    have ht' : (brownianFirstHitHorizon n (Fin.tail ds) : ℝ) < t-(ds 0 : ℝ) := by
      change ((ds 0+brownianFirstHitHorizon n (Fin.tail ds) : ℝ≥0) : ℝ) < t at ht
      rw [NNReal.coe_add] at ht
      linarith
    have hk := (killed_continuousAt (-a) (ds 0) c (xs 0) (ne_of_gt (hds 0))).comp_of_eq (x := (ds,(c,(xs,t))))
      (hd.prodMk (continuous_snd.fst.prodMk hx)).continuousAt rfl
    have hr := (ih (Fin.tail ds) (xs 0) (Fin.tail xs) (t-(ds 0 : ℝ)) (fun i => hds i.succ) ht').comp_of_eq (x := (ds,(c,(xs,t))))
      ((htaild.comp continuous_fst).prodMk
        (hx.prodMk ((htailx.comp continuous_snd.snd.fst).prodMk
          (continuous_snd.snd.snd.sub (NNReal.continuous_coe.comp hd))))).continuousAt rfl
    simp_rw [brownianFirstHitFinitePDF,ENNReal.toReal_mul,ENNReal.toReal_ofReal']
    exact (hk.max continuousAt_const).mul hr

/-- Tailing a finite tuple of nonnegative elapsed times is continuous. -/
private theorem continuous_fin_tail_nnreal (n : ℕ) : Continuous (Fin.tail : (Fin (n+1) → ℝ≥0) → Fin n → ℝ≥0) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.succ

/-- Tailing a finite tuple of sampled real states is continuous. -/
private theorem continuous_fin_tail_real (n : ℕ) : Continuous (Fin.tail : (Fin (n+1) → ℝ) → Fin n → ℝ) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.succ

/-- The complete finite density is jointly measurable in every elapsed time, starting level, state and absolute lifetime. -/
private theorem measurable_brownianFirstHitFinitePDF_all (a : ℝ) (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ≥0) × (ℝ × ((Fin n → ℝ) × ℝ)) =>
      brownianFirstHitFinitePDF a n z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  induction n with
  | zero =>
      exact (measurable_brownianFirstHitDensity_joint.comp
        (measurable_const.prodMk ((measurable_fst.comp measurable_snd).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd))))).ennreal_ofReal
  | succ n ih =>
      have hd : Measurable (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => z.1 0) :=
        (measurable_pi_apply 0).comp measurable_fst
      have hx : Measurable (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => z.2.2.1 0) :=
        (measurable_pi_apply 0).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
      have hdTail : Measurable (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => Fin.tail z.1) :=
        (continuous_fin_tail_nnreal n).measurable.comp measurable_fst
      have hxTail : Measurable (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => Fin.tail z.2.2.1) :=
        (continuous_fin_tail_real n).measurable.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
      have ht : Measurable (fun z : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) => z.2.2.2-(z.1 0 : ℝ)) :=
        (measurable_snd.comp (measurable_snd.comp measurable_snd)).sub (NNReal.continuous_coe.measurable.comp hd)
      exact ((measurable_brownianKilledTransitionPDF_time (-a)).comp
        (hd.prodMk ((measurable_fst.comp measurable_snd).prodMk hx))).ennreal_ofReal.mul
        (ih.comp (hdTail.prodMk (hx.prodMk (hxTail.prodMk ht))))

private theorem elapsed_continuous (n : ℕ) :
    Continuous (brownianFirstHitElapsed n) := by
  cases n with
  | zero =>
    apply continuous_pi
    intro i
    exact Fin.elim0 i
  | succ n =>
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_apply 0
    · exact (continuous_apply j.succ).sub (continuous_apply j.castSucc)

private theorem reversal_times_pos (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (v : ℝ≥0) (hv : ss (Fin.last n) < v) (i : Fin (n+1)) :
    0 < v-ss i.rev :=
  tsub_pos_iff_lt.mpr ((hss.monotone (Fin.le_last i.rev)).trans_lt hv)

private theorem reversal_times_strictMono (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (v : ℝ≥0) (hv : ss (Fin.last n) < v) :
    StrictMono (fun i : Fin (n+1) => v-ss i.rev) := by
  intro i j hij
  exact tsub_lt_tsub_left_of_le ((hss.monotone (Fin.le_last i.rev)).trans hv.le)
    (hss (Fin.rev_lt_rev.mpr hij))

/-- The source reversal density, in forward coordinate order, with its absolute lifetime retained. -/
noncomputable def brownianFirstHitReversedPDF (a c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (z : (Fin (n+1) → ℝ) × ℝ) : ℝ≥0∞ :=
  brownianFirstHitFinitePDF a (n+1)
    (brownianFirstHitElapsed (n+1) (fun i => Real.toNNReal z.2-ss i.rev)) c z.1 z.2

theorem measurable_brownianFirstHitReversedPDF (a c : ℝ) (n : ℕ) (ss : Fin (n+1) → ℝ≥0) :
    Measurable (brownianFirstHitReversedPDF a c n ss) := by
  have htimes : Measurable (fun z : (Fin (n+1) → ℝ) × ℝ => fun i : Fin (n+1) =>
      Real.toNNReal z.2-ss i.rev) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_real_toNNReal.comp measurable_snd).sub measurable_const
  exact (measurable_brownianFirstHitFinitePDF_all a (n+1)).comp
    (f := fun z : (Fin (n+1) → ℝ) × ℝ =>
      (brownianFirstHitElapsed (n+1) (fun i => Real.toNNReal z.2-ss i.rev), (c, z)))
    (((elapsed_continuous (n+1)).measurable.comp htimes).prodMk (measurable_const.prodMk measurable_id))

private theorem tendsto_gridPDF (a c : ℝ) (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (hs0 : 0 < ss 0) (b : ℝ≥0) (hb : ss (Fin.last n) < b)
    (z : (Fin (n+1) → ℝ) × ℝ) (hz : (b : ℝ) < z.2) :
    Tendsto (fun m => brownianFirstHitFinitePDF a (n+1)
      (brownianFirstHitElapsed (n+1)
        (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2))) c z.1 z.2)
      atTop (𝓝 (brownianFirstHitReversedPDF a c n ss z)) := by
  let ts : Fin (n+1) → ℝ≥0 := fun i => Real.toNNReal z.2-ss i.rev
  have ht : ss (Fin.last n) < Real.toNNReal z.2 := by
    apply hb.trans
    apply NNReal.coe_lt_coe.mp
    rwa [Real.coe_toNNReal z.2 ((NNReal.coe_nonneg b).trans hz.le)]
  have hts : StrictMono ts := reversal_times_strictMono n ss hss _ ht
  have hd := brownianFirstHitElapsed_pos (n+1) ts (reversal_times_pos n ss hss _ ht) hts
  have hh : (brownianFirstHitHorizon (n+1) (brownianFirstHitElapsed (n+1) ts) : ℝ) < z.2 := by
    rw [brownianFirstHitHorizon_elapsed n ts hts.monotone]
    change ((Real.toNNReal z.2-ss (Fin.last n).rev : ℝ≥0) : ℝ) < z.2
    rw [Fin.rev_last,NNReal.coe_sub ((hss.monotone (Fin.zero_le _)).trans ht.le),
      Real.coe_toNNReal z.2 ((NNReal.coe_nonneg b).trans hz.le)]
    have hs : 0 < (ss 0 : ℝ) := NNReal.coe_pos.mpr hs0
    linarith
  have hgrid : Tendsto (fun m => brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2))
      atTop (𝓝 ts) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_brownianReversalGridTimes_selected n ss b z.2 hz i)
  have hparam : Tendsto (fun m => (brownianFirstHitElapsed (n+1)
      (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2)),(c,(z.1,z.2))))
      atTop (𝓝 (brownianFirstHitElapsed (n+1) ts,(c,(z.1,z.2)))) :=
    (((elapsed_continuous (n+1)).tendsto _).comp hgrid).prodMk_nhds tendsto_const_nhds
  have hreal := (finiteDensity_continuousAt a (n+1) _ c z.1 z.2 hd hh).tendsto.comp hparam
  have he := ENNReal.continuous_ofReal.tendsto _ |>.comp hreal
  simpa only [Function.comp_def,ENNReal.ofReal_toReal (brownianFirstHitFinitePDF_ne_top a c (n+1) _ _ _),
    brownianFirstHitReversedPDF,ts] using he

private theorem offsetPDF_continuousAt (a c : ℝ) (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (b : ℝ≥0) (hb : ss (Fin.last n) < b)
    (r : ℝ≥0) (hr : r < ss 0) (z : (Fin (n+1) → ℝ) × ℝ) (hz : (b : ℝ) ≤ z.2) :
    ContinuousAt (fun w : ℝ≥0 × ((Fin (n+1) → ℝ) × ℝ) =>
      (brownianFirstHitFinitePDF a (n+1)
        (brownianFirstHitElapsed (n+1) (fun i => (Real.toNNReal w.2.2+w.1)-ss i.rev))
        c w.2.1 w.2.2).toReal) (r,z) := by
  let v : ℝ≥0 := Real.toNNReal z.2+r
  let ts : Fin (n+1) → ℝ≥0 := fun i => v-ss i.rev
  have hz0 : 0 ≤ z.2 := (NNReal.coe_nonneg b).trans hz
  have ht : ss (Fin.last n) < v := by
    apply hb.trans_le
    have hb' : b ≤ Real.toNNReal z.2 := by
      apply NNReal.coe_le_coe.mp
      rwa [Real.coe_toNNReal z.2 hz0]
    exact hb'.trans (show Real.toNNReal z.2 ≤ Real.toNNReal z.2+r from le_self_add)
  have hts : StrictMono ts := reversal_times_strictMono n ss hss v ht
  have hd := brownianFirstHitElapsed_pos (n+1) ts (reversal_times_pos n ss hss v ht) hts
  have hh : (brownianFirstHitHorizon (n+1) (brownianFirstHitElapsed (n+1) ts) : ℝ) < z.2 := by
    rw [brownianFirstHitHorizon_elapsed n ts hts.monotone]
    change ((v-ss (Fin.last n).rev : ℝ≥0) : ℝ) < z.2
    rw [Fin.rev_last,NNReal.coe_sub ((hss.monotone (Fin.zero_le _)).trans ht.le)]
    have hv : (v : ℝ) = z.2+(r : ℝ) := by
      simp only [v,NNReal.coe_add,Real.coe_toNNReal z.2 hz0]
    have hrr := NNReal.coe_lt_coe.mpr hr
    linarith
  have hm : Continuous (fun w : ℝ≥0 × ((Fin (n+1) → ℝ) × ℝ) =>
      (brownianFirstHitElapsed (n+1) (fun i => (Real.toNNReal w.2.2+w.1)-ss i.rev),
        (c,(w.2.1,w.2.2)))) := by
    have htimes : Continuous (fun w : ℝ≥0 × ((Fin (n+1) → ℝ) × ℝ) =>
        fun i : Fin (n+1) => (Real.toNNReal w.2.2+w.1)-ss i.rev) := by
      apply continuous_pi
      intro i
      fun_prop
    exact ((elapsed_continuous (n+1)).comp htimes).prodMk
      (continuous_const.prodMk (continuous_snd.fst.prodMk continuous_snd.snd))
  exact ContinuousAt.comp' (g := fun d : (Fin (n+1) → ℝ≥0) × (ℝ × ((Fin (n+1) → ℝ) × ℝ)) =>
      (brownianFirstHitFinitePDF a (n+1) d.1 d.2.1 d.2.2.1 d.2.2.2).toReal) (f := fun w : ℝ≥0 × ((Fin (n+1) → ℝ) × ℝ) =>
      (brownianFirstHitElapsed (n+1) (fun i => (Real.toNNReal w.2.2+w.1)-ss i.rev),
        (c,(w.2.1,w.2.2))))
    (finiteDensity_continuousAt a (n+1) (brownianFirstHitElapsed (n+1) ts) c z.1 z.2 hd hh)
    hm.continuousAt

private theorem gridPDF_compact_bound (a c : ℝ) (n : ℕ) (ss : Fin (n+1) → ℝ≥0)
    (hss : StrictMono ss) (hs0 : 0 < ss 0) (b : ℝ≥0) (hb : ss (Fin.last n) < b)
    (K : Set ((Fin (n+1) → ℝ) × ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m in atTop, ∀ z ∈ K, (b : ℝ) < z.2 →
      (brownianFirstHitFinitePDF a (n+1)
        (brownianFirstHitElapsed (n+1)
          (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2))) c z.1 z.2).toReal ≤ C := by
  let ε : ℝ≥0 := ss 0/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεs : ε < ss 0 := by
    apply NNReal.coe_lt_coe.mp
    change (ss 0 : ℝ)/2 < (ss 0 : ℝ)
    have h := NNReal.coe_pos.mpr hs0
    linarith
  let L : Set ((Fin (n+1) → ℝ) × ℝ) := K ∩ {z | (b : ℝ) ≤ z.2}
  have hL : IsCompact L := hK.inter_right (isClosed_le continuous_const continuous_snd)
  let D : Set (ℝ≥0 × ((Fin (n+1) → ℝ) × ℝ)) := Icc 0 ε ×ˢ L
  have hD : IsCompact D := isCompact_Icc.prod hL
  let F : (ℝ≥0 × ((Fin (n+1) → ℝ) × ℝ)) → ℝ := fun w =>
    (brownianFirstHitFinitePDF a (n+1)
      (brownianFirstHitElapsed (n+1) (fun i => (Real.toNNReal w.2.2+w.1)-ss i.rev)) c w.2.1 w.2.2).toReal
  have hF : ContinuousOn F D := by
    intro w hw
    exact (offsetPDF_continuousAt a c n ss hss b hb w.1 (hw.1.2.trans_lt hεs) w.2 hw.2.2).continuousWithinAt
  obtain ⟨C,hC⟩ := hD.bddAbove_image hF
  refine ⟨max C 0,le_max_right _ _,?_⟩
  filter_upwards [tendsto_brownianLifetimeMesh_zero.eventually (gt_mem_nhds hε)] with m hm
  intro z hz hzt
  let r : ℝ≥0 := brownianLifetimeCeiling m z.2-Real.toNNReal z.2
  have hr : r ≤ ε := by
    apply (tsub_le_iff_right).mpr
    exact (brownianLifetimeCeiling_upper m z.2).trans (by simpa only [add_comm] using add_le_add_left hm.le (Real.toNNReal z.2))
  have hw : (r,z) ∈ D := ⟨⟨zero_le,hr⟩,hz,hzt.le⟩
  have he : Real.toNNReal z.2+r = brownianLifetimeCeiling m z.2 :=
    add_tsub_cancel_of_le (brownianLifetimeCeiling_lower m z.2)
  have hf : F (r,z) = (brownianFirstHitFinitePDF a (n+1)
      (brownianFirstHitElapsed (n+1)
        (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2))) c z.1 z.2).toReal := by
    dsimp [F]
    rw [he]
    congr 3
    funext i
    simp only [brownianReversalGridTimes,brownianLifetimeGridHorizon_selected b m z.2 hzt]
  rw [← hf]
  exact (hC (mem_image_of_mem F hw)).trans (le_max_left _ _)

private theorem reversedPDF_mass_le_one (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0)
    (b : ℝ≥0) (hb : ss (Fin.last n) < b) :
    (∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | (b : ℝ) < z.2},
      brownianFirstHitReversedPDF a c n ss z ∂volume.prod volume) ≤ 1 := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let μ : Measure ((Fin (n+1) → ℝ) × ℝ) :=
    (volume.prod volume).restrict {z | (b : ℝ) < z.2}
  let F : ℕ → ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞ := fun m z =>
    brownianFirstHitFinitePDF a (n+1)
      (brownianFirstHitElapsed (n+1)
        (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2))) c z.1 z.2
  have hF (m : ℕ) : Measurable (F m) :=
    measurable_brownianSelectedFirstHitPDF a c (n+1) (brownianLifetimeCellIndex m)
      (measurable_brownianLifetimeCellIndex m) (brownianReversalGridTimes n ss b m)
  have hA : MeasurableSet {z : (Fin (n+1) → ℝ) × ℝ | (b : ℝ) < z.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hconv : ∀ᵐ z ∂μ, Tendsto (fun m => F m z) atTop (𝓝 (brownianFirstHitReversedPDF a c n ss z)) := by
    filter_upwards [ae_restrict_mem hA] with z hz
    exact tendsto_gridPDF a c n ss hss hs0 b hb z hz
  have hmass : Tendsto (fun m => ∫⁻ z, F m z ∂μ) atTop
      (𝓝 (P {p : BrownianPath | (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)})) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_brownianLifetimeMesh_zero.eventually (gt_mem_nhds hs0)] with m hm
    have he := brownianPath_firstHit_reversal_grid_lintegral P hB a c ha hc n ss hss b hb m hm
      (fun _ => 1) measurable_const
    simpa only [mul_one,lintegral_one,Measure.restrict_apply MeasurableSet.univ,univ_inter] using he
  calc
    _ = ∫⁻ z, liminf (fun m => F m z) atTop ∂μ :=
      lintegral_congr_ae (hconv.mono (fun _ h => h.liminf_eq.symm))
    _ ≤ liminf (fun m => ∫⁻ z, F m z ∂μ) atTop := lintegral_liminf_le hF
    _ = _ := hmass.liminf_eq
    _ ≤ 1 := prob_le_one

/-- The actual lifetime-indexed observations in the forward coordinate order used by the cell law. -/
noncomputable def brownianFirstHitReversedObservation (a c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (p : BrownianPath) : (Fin (n+1) → ℝ) × ℝ :=
  ((fun i => c-(p (firstPassageTime (driftedBrownianPath a p) c-ss i.rev)+
    a*((firstPassageTime (driftedBrownianPath a p) c-ss i.rev : ℝ≥0) : ℝ))),
    (firstPassageTime (driftedBrownianPath a p) c : ℝ))

private theorem measurable_reversedObservation (a c : ℝ) (n : ℕ) (ss : Fin (n+1) → ℝ≥0) :
    Measurable (brownianFirstHitReversedObservation a c n ss) := by
  have hτ : Measurable (fun p : BrownianPath => firstPassageTime (driftedBrownianPath a p) c) :=
    (measurable_firstPassageTime c).comp (continuous_brownianDriftPath.comp (continuous_const.prodMk continuous_id)).measurable
  have hs : Measurable (fun p : BrownianPath => fun i : Fin (n+1) =>
      c-(p (firstPassageTime (driftedBrownianPath a p) c-ss i.rev)+
        a*((firstPassageTime (driftedBrownianPath a p) c-ss i.rev : ℝ≥0) : ℝ))) := by
    apply measurable_pi_iff.mpr
    intro i
    have ht := hτ.sub (measurable_const (a := ss i.rev))
    exact measurable_const.sub (((continuous_eval.measurable).comp (measurable_id.prodMk ht)).add
      (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht)))
  exact hs.prodMk (NNReal.continuous_coe.measurable.comp hτ)

private theorem reversed_observation_compactTest (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0)
    (b : ℝ≥0) (hb : ss (Fin.last n) < b) (f : C_c(((Fin (n+1) → ℝ) × ℝ), ℝ≥0)) :
    (∫⁻ p in {p : BrownianPath | (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)},
      (f (brownianFirstHitReversedObservation a c n ss p) : ℝ≥0∞) ∂P) =
      ∫⁻ z : (Fin (n+1) → ℝ) × ℝ in {z | (b : ℝ) < z.2},
        brownianFirstHitReversedPDF a c n ss z*(f z : ℝ≥0∞) ∂volume.prod volume := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A : Set BrownianPath := {p | (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)}
  let μ : Measure ((Fin (n+1) → ℝ) × ℝ) :=
    (volume.prod volume).restrict {z | (b : ℝ) < z.2}
  let G : ℕ → BrownianPath → (Fin (n+1) → ℝ) × ℝ := fun m =>
    brownianSelectedFirstHitObservation a c (n+1) (brownianLifetimeCellIndex m) (brownianReversalGridTimes n ss b m)
  let F : ℕ → ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞ := fun m z =>
    brownianFirstHitFinitePDF a (n+1)
      (brownianFirstHitElapsed (n+1)
        (brownianReversalGridTimes n ss b m (brownianLifetimeCellIndex m z.2))) c z.1 z.2
  have hG (m : ℕ) : Measurable (G m) := measurable_brownianSelectedFirstHitObservation a c (n+1)
    (brownianLifetimeCellIndex m) (measurable_brownianLifetimeCellIndex m) (brownianReversalGridTimes n ss b m)
  have hF (m : ℕ) : Measurable (F m) := measurable_brownianSelectedFirstHitPDF a c (n+1)
    (brownianLifetimeCellIndex m) (measurable_brownianLifetimeCellIndex m) (brownianReversalGridTimes n ss b m)
  have hH : Continuous (fun z => (f z : ℝ≥0∞)) := ENNReal.continuous_coe.comp f.continuous
  obtain ⟨M,hM⟩ := (f.hasCompactSupport.isCompact_range f.continuous).bddAbove
  have hMz (z) : f z ≤ M := hM (mem_range_self z)
  have hAm : MeasurableSet A := measurableSet_lt measurable_const
    (NNReal.continuous_coe.measurable.comp ((measurable_firstPassageTime c).comp
      (continuous_brownianDriftPath.comp (continuous_const.prodMk continuous_id)).measurable))
  have hleft : Tendsto (fun m => ∫⁻ p in A, (f (G m p) : ℝ≥0∞) ∂P) atTop
      (𝓝 (∫⁻ p in A, (f (brownianFirstHitReversedObservation a c n ss p) : ℝ≥0∞) ∂P)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => (M : ℝ≥0∞))
    · intro m
      exact hH.measurable.comp (hG m)
    · intro m
      exact ae_of_all _ (fun p => ENNReal.coe_le_coe.mpr (hMz (G m p)))
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
    · filter_upwards [ae_restrict_mem hAm] with p hp
      exact (hH.tendsto _).comp (tendsto_brownianSelectedFirstHitObservation_grid a c n ss b p hp)
  obtain ⟨C,hC,hbound⟩ := gridPDF_compact_bound a c n ss hss hs0 b hb (tsupport f) f.hasCompactSupport
  let B : ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞ :=
    (tsupport f).indicator (fun _ => ENNReal.ofReal C*(M : ℝ≥0∞))
  have hfin : ∫⁻ z, B z ∂μ ≠ ∞ := by
    rw [lintegral_indicator f.hasCompactSupport.measurableSet,setLIntegral_const]
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
    exact ne_top_of_le_ne_top f.hasCompactSupport.measure_lt_top.ne (Measure.restrict_apply_le _ _)
  have hμA : MeasurableSet {z : (Fin (n+1) → ℝ) × ℝ | (b : ℝ) < z.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hright : Tendsto (fun m => ∫⁻ z, F m z*(f z : ℝ≥0∞) ∂μ) atTop
      (𝓝 (∫⁻ z, brownianFirstHitReversedPDF a c n ss z*(f z : ℝ≥0∞) ∂μ)) := by
    apply tendsto_lintegral_filter_of_dominated_convergence B
    · exact Eventually.of_forall (fun m => (hF m).mul hH.measurable)
    · filter_upwards [hbound] with m hm
      filter_upwards [ae_restrict_mem hμA] with z hz
      by_cases hk : z ∈ tsupport f
      · rw [show B z = ENNReal.ofReal C*(M : ℝ≥0∞) from Set.indicator_of_mem hk _]
        have hd : F m z ≤ ENNReal.ofReal C := by
          have hne : F m z ≠ ∞ := brownianFirstHitFinitePDF_ne_top a c (n+1) _ _ _
          rw [← ENNReal.ofReal_toReal hne]
          exact ENNReal.ofReal_le_ofReal (hm z hk hz)
        exact mul_le_mul' hd (ENNReal.coe_le_coe.mpr (hMz z))
      · rw [image_eq_zero_of_notMem_tsupport hk,ENNReal.coe_zero,mul_zero]
        exact zero_le
    · exact hfin
    · filter_upwards [ae_restrict_mem hμA] with z hz
      exact ENNReal.Tendsto.mul_const (tendsto_gridPDF a c n ss hss hs0 b hb z hz) (Or.inr ENNReal.coe_ne_top)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [tendsto_brownianLifetimeMesh_zero.eventually (gt_mem_nhds hs0)] with m hm
  exact (brownianPath_firstHit_reversal_grid_lintegral P hB a c ha hc n ss hss b hb m hm
    (fun z => (f z : ℝ≥0∞)) hH.measurable).symm

/-- Actual random-lifetime reversed samples have the killed/hitting density obtained from the source ceiling-cell calculation. -/
theorem brownianPath_firstHit_reversed_observation_density_map_localized (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0)
    (b : ℝ≥0) (hb : ss (Fin.last n) < b) :
    (P.restrict {p : BrownianPath | (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)}).map
      (brownianFirstHitReversedObservation a c n ss) =
      ((volume.prod volume).restrict {z : (Fin (n+1) → ℝ) × ℝ | (b : ℝ) < z.2}).withDensity
        (brownianFirstHitReversedPDF a c n ss) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have := isFiniteMeasure_withDensity (ne_top_of_le_ne_top ENNReal.one_ne_top
    (reversedPDF_mass_le_one P hB a c ha hc n ss hss hs0 b hb))
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  have he := reversed_observation_compactTest P hB a c ha hc n ss hss hs0 b hb f
  have hH : Measurable (fun z => (f z : ℝ≥0∞)) := (ENNReal.continuous_coe.comp f.continuous).measurable
  rw [← lintegral_map hH
      (measurable_reversedObservation a c n ss)] at he
  have hden := lintegral_withDensity_eq_lintegral_mul
    ((volume.prod volume).restrict {z : (Fin (n+1) → ℝ) × ℝ | (b : ℝ) < z.2})
    (measurable_brownianFirstHitReversedPDF a c n ss) hH
  simp only [Pi.mul_apply] at hden
  rw [← hden] at he
  have hl : Integrable (fun z => (f z : ℝ))
      ((P.restrict {p : BrownianPath | (b : ℝ) < (firstPassageTime (driftedBrownianPath a p) c : ℝ)}).map
        (brownianFirstHitReversedObservation a c n ss)) :=
    (NNReal.continuous_coe.comp f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left f.hasCompactSupport (show ((0 : ℝ≥0) : ℝ) = 0 from rfl))
  have hr : Integrable (fun z => (f z : ℝ))
      (((volume.prod volume).restrict {z : (Fin (n+1) → ℝ) × ℝ | (b : ℝ) < z.2}).withDensity
        (brownianFirstHitReversedPDF a c n ss)) :=
    (NNReal.continuous_coe.comp f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left f.hasCompactSupport (show ((0 : ℝ≥0) : ℝ) = 0 from rfl))
  rw [lintegral_coe_eq_integral _ hl,lintegral_coe_eq_integral _ hr] at he
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun z => (f z).coe_nonneg)) (integral_nonneg (fun z => (f z).coe_nonneg))).mp he

/-- Exhausting the lifetime cutoffs gives the exact reversed observation/lifetime density on its full source domain. -/
theorem brownianPath_firstHit_reversed_observation_density_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0) :
    (P.restrict {p : BrownianPath | ss (Fin.last n) < firstPassageTime (driftedBrownianPath a p) c}).map
      (brownianFirstHitReversedObservation a c n ss) =
      ((volume.prod volume).restrict {z : (Fin (n+1) → ℝ) × ℝ | (ss (Fin.last n) : ℝ) < z.2}).withDensity
        (brownianFirstHitReversedPDF a c n ss) := by
  let b : ℕ → ℝ≥0 := fun m => ss (Fin.last n)+(brownianDyadicMesh m)⁻¹
  let A : ℝ≥0 → Set ((Fin (n+1) → ℝ) × ℝ) := fun u => {z | (u : ℝ) < z.2}
  have hA (u : ℝ≥0) : MeasurableSet (A u) := measurableSet_lt measurable_const measurable_snd
  have hb (m : ℕ) : ss (Fin.last n) < b m := by
    apply lt_add_of_pos_right
    apply inv_pos.mpr
    unfold brownianDyadicMesh
    positivity
  have htend : Tendsto (fun m => (b m : ℝ)) atTop (𝓝 (ss (Fin.last n) : ℝ)) := by
    have hd := (NNReal.continuous_coe.tendsto 0).comp tendsto_brownianLifetimeMesh_zero
    simpa only [b,Function.comp_def,NNReal.coe_add,NNReal.coe_zero,add_zero,NNReal.coe_inv] using
      (tendsto_const_nhds (x := (ss (Fin.last n) : ℝ))).add hd
  have hUnion : (⋃ m, A (b m)) = A (ss (Fin.last n)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨m,hm⟩ := mem_iUnion.mp hz
      exact (NNReal.coe_lt_coe.mpr (hb m)).trans hm
    · intro hz
      obtain ⟨m,hm⟩ := (htend.eventually (Iio_mem_nhds hz)).exists
      exact mem_iUnion.mpr ⟨m,hm⟩
  have hobs := measurable_reversedObservation a c n ss
  have he : (P.map (brownianFirstHitReversedObservation a c n ss)).restrict (A (ss (Fin.last n))) =
      ((volume.prod volume).withDensity (brownianFirstHitReversedPDF a c n ss)).restrict (A (ss (Fin.last n))) := by
    rw [← hUnion,Measure.restrict_iUnion_congr]
    intro m
    rw [Measure.restrict_map hobs (hA (b m)),restrict_withDensity (hA (b m))]
    exact brownianPath_firstHit_reversed_observation_density_map_localized P hB a c ha hc n ss hss hs0 (b m) (hb m)
  rw [Measure.restrict_map hobs (hA (ss (Fin.last n))),restrict_withDensity (hA (ss (Fin.last n)))] at he
  have hpre : {p : BrownianPath | ss (Fin.last n) < firstPassageTime (driftedBrownianPath a p) c} =
      brownianFirstHitReversedObservation a c n ss ⁻¹' A (ss (Fin.last n)) := by
    ext p
    exact NNReal.coe_lt_coe.symm
  rw [hpre]
  exact he

end DOZZ.Proofs
