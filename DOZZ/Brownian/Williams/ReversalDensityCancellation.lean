/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.FirstHitReversal
public import DOZZ.Brownian.Williams.ConditionedBandFinite
public import DOZZ.Brownian.ConditionedFDDMeasure

/-!
# Harmonic cancellation in the first-hit reversal density

Transposing each killed transition and telescoping the Doob harmonic factors gives
exactly the conditioned entrance density with its final last-exit boundary factor.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DOZZ.Proofs

private theorem harmonic_pos {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [hν, hx]))

/-- Appending an observation multiplies an entrance FDD by the final transition. -/
theorem conditionedPositiveFDDDensity_ofFn_snoc (ν : ℝ) (n : ℕ)
    (ts xs : Fin (n+1) → ℝ) (t x : ℝ) :
    conditionedPositiveFDDDensity ν ((List.ofFn ts) ++ [t]) ((List.ofFn xs) ++ [x]) =
      conditionedPositiveFDDDensity ν (List.ofFn ts) (List.ofFn xs) *
        conditionedPositiveTransitionDensity ν (t-ts (Fin.last n)) (xs (Fin.last n)) x := by
  rw [List.ofFn_succ (f := ts), List.ofFn_succ (f := xs)]
  simp only [List.cons_append]
  rw [conditionedPositiveFDDDensity_append_split ν (ts 0) (xs 0)
    (List.ofFn fun i : Fin n => ts i.succ) (List.ofFn fun i : Fin n => xs i.succ)
    [t] [x] (by simp)]
  rw [conditionedPositiveLastTime_ofFn_tail, conditionedPositiveLastState_ofFn_tail]
  simp only [conditionedPositiveTimeChainDensity, mul_one]

/-- The finite killed/hitting density equals the entrance chain in reversed order, including
the last-exit boundary factor. All observation coordinates are kept. -/
theorem brownianFirstHitFinitePDF_reverse_cancel
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (n : ℕ)
    (ds : Fin (n+1) → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (xs : Fin (n+1) → ℝ) (hxs : ∀ i, 0 < xs i)
    (t : ℝ) (ht : (brownianFirstHitHorizon (n+1) ds : ℝ) < t) :
    brownianFirstHitFinitePDF ν (n+1) ds c xs t =
      ENNReal.ofReal (conditionedPositiveFDDDensity ν
        (List.ofFn fun i => t-(brownianFirstHitTimes (n+1) ds i.rev : ℝ))
        (List.ofFn fun i => xs i.rev) *
        conditionedPositiveTransitionDensity ν (ds 0) (xs 0) c * ν / conditionedH ν c) := by
  induction n generalizing c t with
  | zero =>
    have ht' : 0 < t-(ds 0 : ℝ) := by
      simpa only [brownianFirstHitHorizon, add_zero] using sub_pos.mpr ht
    have hH := (harmonic_pos hν (hxs 0)).ne'
    have hC := (harmonic_pos hν hc).ne'
    simp only [brownianFirstHitFinitePDF, List.ofFn_succ, List.ofFn_zero,
      Fin.rev_zero, Fin.last_zero, brownianFirstHitTimes, Fin.cons_zero,
      conditionedPositiveFDDDensity, conditionedPositiveTimeChainDensity, mul_one]
    rw [brownianKilledTransitionPDF_transpose,
      conditionedPositiveTransitionDensity_eq_killed ν hν (ds 0) (hds 0) (xs 0) c (hxs 0),
      conditionedPositiveEntranceDensity_eq_firstHit ν _ _ hν ht' (hxs 0),
      ← ENNReal.ofReal_mul (brownianKilledTransitionPDF_nonneg ν _ (hds 0).ne' _ _)]
    congr 1
    field_simp
  | succ n ih =>
    have ht' : (brownianFirstHitHorizon (n+1) (Fin.tail ds) : ℝ) < t-(ds 0 : ℝ) := by
      change ((ds 0 + brownianFirstHitHorizon (n+1) (Fin.tail ds) : ℝ≥0) : ℝ) < t at ht
      rw [NNReal.coe_add] at ht
      linarith
    have ih' := ih (xs 0) (hxs 0) (Fin.tail ds) (fun i => hds i.succ)
      (Fin.tail xs) (fun i => hxs i.succ) (t-(ds 0 : ℝ)) ht'
    let ts : Fin (n+1) → ℝ := fun i =>
      (t-(ds 0 : ℝ))-(brownianFirstHitTimes (n+1) (Fin.tail ds) i.rev : ℝ)
    let ys : Fin (n+1) → ℝ := fun i => xs i.rev.succ
    have htimes :
        (List.ofFn fun i : Fin (n+2) => t-(brownianFirstHitTimes (n+2) ds i.rev : ℝ)) =
          (List.ofFn ts) ++ [t-(ds 0 : ℝ)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      congr 1
      · congr 1
        funext i
        simp only [Fin.rev_castSucc, brownianFirstHitTimes, Fin.cons_succ, NNReal.coe_add, ts]
        ring
      · simp only [Fin.rev_last, brownianFirstHitTimes, Fin.cons_zero]
    have hvalues : (List.ofFn fun i : Fin (n+2) => xs i.rev) =
        (List.ofFn ys) ++ [xs 0] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp only [Fin.rev_castSucc, Fin.rev_last, ys]
    have hstep : (t-(ds 0 : ℝ))-ts (Fin.last n) = (ds 1 : ℝ) := by
      simp only [ts, Fin.rev_last, brownianFirstHitTimes, Fin.cons_zero, Fin.tail]
      ring_nf
      rfl
    have hlast : ys (Fin.last n) = xs 1 := by simp [ys]
    rw [brownianFirstHitFinitePDF, ih', brownianKilledTransitionPDF_transpose,
      ← ENNReal.ofReal_mul (brownianKilledTransitionPDF_nonneg ν _ (hds 0).ne' _ _),
      htimes, hvalues, conditionedPositiveFDDDensity_ofFn_snoc, hstep, hlast]
    change ENNReal.ofReal (_ * (conditionedPositiveFDDDensity ν (List.ofFn ts) (List.ofFn ys) *
      conditionedPositiveTransitionDensity ν (ds 1) (xs 1) (xs 0) * ν / conditionedH ν (xs 0))) = _
    rw [conditionedPositiveTransitionDensity_eq_killed ν hν (ds 0) (hds 0) (xs 0) c (hxs 0)]
    congr 1
    have hH := (harmonic_pos hν (hxs 0)).ne'
    have hC := (harmonic_pos hν hc).ne'
    field_simp

/-- An entrance FDD has no mass density at a nonpositive observation coordinate. -/
theorem conditionedPositiveFDDDensity_ofFn_of_state_le_zero
    (ν : ℝ) (n : ℕ) (ts xs : Fin (n+1) → ℝ) (i : Fin (n+1)) (hi : xs i ≤ 0) :
    conditionedPositiveFDDDensity ν (List.ofFn ts) (List.ofFn xs) = 0 := by
  induction n with
  | zero =>
    have hi0 : xs 0 ≤ 0 := by rwa [Fin.eq_zero i] at hi
    simp [List.ofFn_succ, conditionedPositiveFDDDensity,
      conditionedPositiveEntranceDensity, not_lt.mpr hi0]
  | succ n ih =>
    rw [List.ofFn_succ' (f := ts), List.ofFn_succ' (f := xs), List.concat_eq_append, List.concat_eq_append,
      conditionedPositiveFDDDensity_ofFn_snoc]
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hlast
      simp only [conditionedPositiveTransitionDensity, not_lt.mpr hlast, and_false,
        ite_false, mul_zero]
    · intro hj
      rw [ih (fun j => ts j.castSucc) (fun j => xs j.castSucc) j hj, zero_mul]

/-- The literal lifetime-indexed reversal PDF is the entrance FDD times the last-exit
boundary density, including the zero density outside the positive orthant. -/
theorem brownianFirstHitReversedPDF_eq_lastExitDensity
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0)
    (z : (Fin (n+1) → ℝ) × ℝ) (hz : (ss (Fin.last n) : ℝ) < z.2) :
    brownianFirstHitReversedPDF ν c n ss z =
      ENNReal.ofReal (conditionedPositiveFDDDensity ν
        (List.ofFn fun i => (ss i : ℝ)) (List.ofFn fun i => z.1 i.rev) *
        conditionedPositiveTransitionDensity ν (z.2-(ss (Fin.last n) : ℝ))
          (z.1 0) c * ν / conditionedH ν c) := by
  classical
  let ts : Fin (n+1) → ℝ≥0 := fun i => Real.toNNReal z.2-ss i.rev
  have hz0 : 0 ≤ z.2 := (NNReal.coe_nonneg _).trans hz.le
  have hv : ss (Fin.last n) < Real.toNNReal z.2 := by
    apply NNReal.coe_lt_coe.mp
    rwa [Real.coe_toNNReal _ hz0]
  have hle (i : Fin (n+1)) : ss i ≤ Real.toNNReal z.2 :=
    (hss.monotone (Fin.le_last i)).trans hv.le
  have hts : StrictMono ts := by
    intro i j hij
    exact tsub_lt_tsub_left_of_le (hle i.rev) (hss (Fin.rev_lt_rev.mpr hij))
  have hts0 (i : Fin (n+1)) : 0 < ts i :=
    tsub_pos_iff_lt.mpr ((hss.monotone (Fin.le_last i.rev)).trans_lt hv)
  have hd := brownianFirstHitElapsed_pos (n+1) ts hts0 hts
  have ht : (brownianFirstHitHorizon (n+1) (brownianFirstHitElapsed (n+1) ts) : ℝ) < z.2 := by
    rw [brownianFirstHitHorizon_elapsed n ts hts.monotone]
    simp only [ts, Fin.rev_last, NNReal.coe_sub (hle 0), Real.coe_toNNReal _ hz0]
    have hs : 0 < (ss 0 : ℝ) := hs0
    linarith
  by_cases hpos : ∀ i, 0 < z.1 i
  · rw [brownianFirstHitReversedPDF,
      brownianFirstHitFinitePDF_reverse_cancel ν c hν hc n _ hd _ hpos _ ht,
      brownianFirstHitTimes_elapsed n ts hts.monotone]
    have htup : (fun i : Fin (n+1) => z.2-(ts i.rev : ℝ)) = fun i => (ss i : ℝ) := by
      funext i
      simp only [ts, Fin.rev_rev, NNReal.coe_sub (hle i), Real.coe_toNNReal _ hz0]
      ring
    rw [htup]
    have hd0 : (brownianFirstHitElapsed (n+1) ts 0 : ℝ) = z.2-(ss (Fin.last n) : ℝ) := by
      simp only [brownianFirstHitElapsed, Fin.cons_zero, ts, Fin.rev_zero,
        NNReal.coe_sub (hle (Fin.last n)), Real.coe_toNNReal _ hz0]
    rw [hd0]
  · obtain ⟨i, hi⟩ := not_forall.mp hpos
    have hi' : z.1 i ≤ 0 := not_lt.mp hi
    rw [brownianFirstHitReversedPDF,
      brownianFirstHitFinitePDF_of_state_le_zero ν c (n+1) _ z.1 z.2 i hi',
      conditionedPositiveFDDDensity_ofFn_of_state_le_zero ν n _ _ i.rev (by simpa using hi')]
    simp

end DOZZ.Proofs
end
