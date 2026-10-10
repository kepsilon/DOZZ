/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.FirstHitFinite
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Explicit finite first-hit density measures

The iterated killed/hitting integrals are converted into product-density
measures with the absolute lifetime as a real coordinate. Separating the
first coordinate of a finite real tuple preserves Lebesgue volume. Translating
remaining lifetime to absolute lifetime also preserves volume. Tonelli and
these two transformations identify the entire finite density, with every
killed transition factor and the final hitting factor retained.

Joint measurability is proved in the starting level, sampled states and
absolute lifetime. The density vanishes if any observed state is nonpositive
or the lifetime is no later than the complete observation horizon. Every
pointwise density value is finite directly from its scalar formula.

The resulting actual finite marked pushforward equals Lebesgue product
volume with this explicit density. Positive strictly ordered absolute times
are converted to their positive elapsed times; the cumulative reconstruction
recovers every original observation time and its exact last-time horizon.
Thus the density law applies at the exact absolute times in the source.

The finite density has exactly the actual pre-hit probability as its mass
and defines a finite subprobability measure. Its lifetime marginal is the
proved full first-hit density restricted beyond the last observation horizon.
Every measurable lifetime cell consequently has its exact restricted hitting
density mass. No independent normalization premise is introduced.

The killed kernel is jointly measurable in elapsed time and both states.
The heat density is jointly continuous at positive times, and the first-hit
density is jointly continuous in level and positive remaining time. These
are analytic inputs for the later localized ceiling-cell limit.

The lifetime-indexed reversed samples and the conditioned last-exit marked
law still require that limit and their separate identification. This module
asserts only the actual deterministic finite density laws proved here.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace DOZZ.Proofs

/-- Tail projection of a finite real tuple is measurable. -/
theorem measurable_fin_tail_real (n : ℕ) : Measurable (Fin.tail : (Fin (n+1) → ℝ) → Fin n → ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i.succ

/-- The explicit finite killed/hitting density in absolute lifetime coordinates. -/
noncomputable def brownianFirstHitFinitePDF (a : ℝ) :
    (n : ℕ) → (Fin n → ℝ≥0) → ℝ → (Fin n → ℝ) → ℝ → ℝ≥0∞
  | 0, _, c, _, t => ENNReal.ofReal (brownianFirstHitDensity a c t)
  | n+1, ds, c, xs, t => ENNReal.ofReal (brownianKilledTransitionPDF (-a) (ds 0) c (xs 0))*
      brownianFirstHitFinitePDF a n (Fin.tail ds) (xs 0) (Fin.tail xs) (t-(ds 0 : ℝ))

/-- Joint measurability of the finite killed/hitting density in the starting level, finite states and absolute lifetime. -/
theorem measurable_brownianFirstHitFinitePDF (a : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0) :
    Measurable (fun z : ℝ × ((Fin n → ℝ) × ℝ) => brownianFirstHitFinitePDF a n ds z.1 z.2.1 z.2.2) := by
  induction n with
  | zero =>
      exact (measurable_brownianFirstHitDensity_joint.comp
        (measurable_const.prodMk (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).ennreal_ofReal
  | succ n ih =>
      have hmX : Measurable (fun z : ℝ × ((Fin (n+1) → ℝ) × ℝ) => z.2.1 0) :=
        (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
      have hmTail : Measurable (fun z : ℝ × ((Fin (n+1) → ℝ) × ℝ) => Fin.tail z.2.1) :=
        (measurable_fin_tail_real n).comp (measurable_fst.comp measurable_snd)
      exact (((measurable_brownianKilledTransitionPDF (-a) (ds 0)).comp (measurable_fst.prodMk hmX)).ennreal_ofReal).mul
        ((ih (Fin.tail ds)).comp (hmX.prodMk (hmTail.prodMk ((measurable_snd.comp measurable_snd).sub measurable_const))))

/-- Nonnegative integration over a finite real tuple separates its first coordinate and tail. -/
theorem brownian_lintegral_fin_cons (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ xs, F xs) = ∫⁻ y, ∫⁻ ys : Fin n → ℝ, F (Fin.cons y ys) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he := hp.lintegral_comp hF
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero,Fin.zero_succAbove,
    cast_eq] at he
  rw [← he]
  exact lintegral_prod _ (hF.comp (measurable_fin_cons_real n)).aemeasurable

/-- Real Lebesgue translation changes a remaining lifetime into its absolute clock without a Jacobian factor. -/
theorem brownian_lintegral_lifetime_translate (s : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, F (s+u)) = ∫⁻ t, F t :=
  (measurePreserving_add_left (volume : Measure ℝ) s).lintegral_comp hF

/-- With a fixed starting level, the explicit finite density remains jointly measurable in all states and the absolute lifetime. -/
theorem measurable_brownianFirstHitFinitePDF_fixed (a c : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => brownianFirstHitFinitePDF a n ds c z.1 z.2) :=
  (measurable_brownianFirstHitFinitePDF a n ds).comp (measurable_const.prodMk measurable_id)

/-- The complete iterated killed/hitting integral equals integration against its explicit finite product density in absolute lifetime coordinates. -/
theorem brownianFirstHitFiniteIntegral_eq_density (a c : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0)
    (H : ((Fin n → ℝ) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    brownianFirstHitFiniteIntegral a n ds c H =
      ∫⁻ z : (Fin n → ℝ) × ℝ, brownianFirstHitFinitePDF a n ds c z.1 z.2*H z ∂volume.prod volume := by
  induction n generalizing c with
  | zero =>
      have hm : Measurable (fun z : (Fin 0 → ℝ) × ℝ => brownianFirstHitFinitePDF a 0 ds c z.1 z.2*H z) :=
        (measurable_brownianFirstHitFinitePDF_fixed a c 0 ds).mul hH
      rw [lintegral_prod_symm _ hm.aemeasurable]
      change (∫⁻ t, ENNReal.ofReal (brownianFirstHitDensity a c t)*H ((fun i : Fin 0 => (Fin.elim0 i : ℝ)),t)) = _
      apply lintegral_congr
      intro t
      rw [lintegral_unique]
      have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
      rw [hv,mul_one]
      simp only [brownianFirstHitFinitePDF]
      apply congrArg (fun xs : Fin 0 → ℝ => ENNReal.ofReal (brownianFirstHitDensity a c t)*H (xs,t))
      exact Subsingleton.elim _ _
  | succ n ih =>
      let W : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (brownianKilledTransitionPDF (-a) (ds 0) c y)
      let K : ℝ → ((Fin n → ℝ) × ℝ) → ℝ≥0∞ := fun y z =>
        brownianFirstHitFinitePDF a n (Fin.tail ds) y z.1 z.2
      let J : ℝ → ((Fin n → ℝ) × ℝ) → ℝ≥0∞ := fun y z =>
        H (Fin.cons y z.1,(ds 0 : ℝ)+z.2)
      have hK (y : ℝ) : Measurable (K y) := measurable_brownianFirstHitFinitePDF_fixed a y n (Fin.tail ds)
      have hJ (y : ℝ) : Measurable (J y) :=
        ((hH.comp (measurable_brownianFirstHit_prepend n (ds 0))).comp (measurable_const.prodMk measurable_id))
      have hD : Measurable (fun z : (Fin (n+1) → ℝ) × ℝ => brownianFirstHitFinitePDF a (n+1) ds c z.1 z.2*H z) :=
        (measurable_brownianFirstHitFinitePDF_fixed a c (n+1) ds).mul hH
      calc
        _ = ∫⁻ y, W y*∫⁻ z : (Fin n → ℝ) × ℝ, K y z*J y z ∂volume.prod volume := by
          change (∫⁻ y, W y*brownianFirstHitFiniteIntegral a n (Fin.tail ds) y (J y)) = _
          apply lintegral_congr
          intro y
          rw [ih y (Fin.tail ds) (J y) (hJ y)]
        _ = ∫⁻ y, ∫⁻ ys : Fin n → ℝ, ∫⁻ u, W y*K y (ys,u)*J y (ys,u) := by
          apply lintegral_congr
          intro y
          rw [← lintegral_const_mul (W y) (show Measurable (fun z => K y z*J y z) from (hK y).mul (hJ y))]
          have hm : Measurable (fun z : (Fin n → ℝ) × ℝ => W y*(K y z*J y z)) :=
            measurable_const.mul ((hK y).mul (hJ y))
          rw [lintegral_prod _ hm.aemeasurable]
          apply lintegral_congr
          intro ys
          apply lintegral_congr
          intro u
          exact (mul_assoc _ _ _).symm
        _ = ∫⁻ y, ∫⁻ ys : Fin n → ℝ, ∫⁻ t,
            W y*K y (ys,t-(ds 0 : ℝ))*H (Fin.cons y ys,t) := by
          apply lintegral_congr
          intro y
          apply lintegral_congr
          intro ys
          have hm : Measurable (fun t : ℝ => W y*K y (ys,t-(ds 0 : ℝ))*H (Fin.cons y ys,t)) :=
            (measurable_const.mul ((hK y).comp (measurable_const.prodMk (measurable_id.sub measurable_const)))).mul
              (hH.comp (measurable_const.prodMk measurable_id))
          have he := brownian_lintegral_lifetime_translate (ds 0 : ℝ)
            (fun t => W y*K y (ys,t-(ds 0 : ℝ))*H (Fin.cons y ys,t)) hm
          calc
            _ = ∫⁻ u, W y*K y (ys,((ds 0 : ℝ)+u)-(ds 0 : ℝ))*H (Fin.cons y ys,(ds 0 : ℝ)+u) := by
              apply lintegral_congr
              intro u
              have hc : ((ds 0 : ℝ)+u)-(ds 0 : ℝ) = u := by ring_nf
              rw [hc]
            _ = _ := he
        _ = ∫⁻ xs : Fin (n+1) → ℝ, ∫⁻ t, brownianFirstHitFinitePDF a (n+1) ds c xs t*H (xs,t) := by
          have ht : Measurable (fun xs : Fin (n+1) → ℝ => ∫⁻ t,
              brownianFirstHitFinitePDF a (n+1) ds c xs t*H (xs,t)) :=
            Measurable.lintegral_prod_right (f := fun xs t => brownianFirstHitFinitePDF a (n+1) ds c xs t*H (xs,t)) hD
          rw [brownian_lintegral_fin_cons n _ ht]
          simp only [brownianFirstHitFinitePDF,Fin.cons_zero,Fin.tail_cons,W,K]
        _ = _ := (lintegral_prod _ hD.aemeasurable).symm

/-- The actual complete finite observation/lifetime measure has the explicit killed/hitting product density. -/
theorem brownianPath_firstHit_finite_density_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    (P.restrict {p : BrownianPath | brownianFirstHitHorizon n ds < firstPassageTime (driftedBrownianPath a p) c}).map
      (fun p => (brownianFirstHitSamples n ds a c p,(firstPassageTime (driftedBrownianPath a p) c : ℝ))) =
      (volume.prod volume).withDensity (fun z : (Fin n → ℝ) × ℝ => brownianFirstHitFinitePDF a n ds c z.1 z.2) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (measurable_brownianFirstHitObservation_fixed n ds a c),
    brownianPath_firstHit_finite_lintegral P hB a c ha hc n ds hds H hH,
    brownianFirstHitFiniteIntegral_eq_density a c n ds H hH,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_brownianFirstHitFinitePDF_fixed a c n ds) hH]
  simp only [Pi.mul_apply]

/-- Absolute ordered observation times are converted to their elapsed times. -/
def brownianFirstHitElapsed : (n : ℕ) → (Fin n → ℝ≥0) → Fin n → ℝ≥0
  | 0, _ => fun i => Fin.elim0 i
  | _n+1, ts => Fin.cons (ts 0) (fun i => ts i.succ-ts i.castSucc)

/-- Successive cumulative observation times differ by their elapsed time. -/
theorem brownianFirstHitTimes_step (n : ℕ) (ds : Fin (n+1) → ℝ≥0) (i : Fin n) :
    brownianFirstHitTimes (n+1) ds i.succ = brownianFirstHitTimes (n+1) ds i.castSucc+ds i.succ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change ds 0+ds 1 = ds 0+ds 1
        rfl
      · change ds 0+brownianFirstHitTimes (n+1) (Fin.tail ds) j.succ =
          (ds 0+brownianFirstHitTimes (n+1) (Fin.tail ds) j.castSucc)+ds j.succ.succ
        rw [ih]
        change ds 0+(brownianFirstHitTimes (n+1) (Fin.tail ds) j.castSucc+ds j.succ.succ) = _
        exact (add_assoc _ _ _).symm

/-- Reconstructing cumulative times from the elapsed times recovers every monotone absolute time tuple. -/
theorem brownianFirstHitTimes_elapsed (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (hts : Monotone ts) :
    brownianFirstHitTimes (n+1) (brownianFirstHitElapsed (n+1) ts) = ts := by
  funext i
  refine Fin.induction ?_ (fun j hj => ?_) i
  · rfl
  · rw [brownianFirstHitTimes_step,hj]
    change ts j.castSucc+(ts j.succ-ts j.castSucc) = ts j.succ
    exact add_tsub_cancel_of_le (hts (Fin.castSucc_le_succ j))

/-- Strictly ordered positive absolute times have strictly positive elapsed times. -/
theorem brownianFirstHitElapsed_pos (n : ℕ) (ts : Fin n → ℝ≥0)
    (ht0 : ∀ i, 0 < ts i) (hts : StrictMono ts) (i : Fin n) :
    0 < brownianFirstHitElapsed n ts i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      refine Fin.cases (ht0 0) (fun j => ?_) i
      change 0 < ts j.succ-ts j.castSucc
      exact tsub_pos_iff_lt.mpr (hts (show j.castSucc < j.succ from Fin.castSucc_lt_succ))

/-- The final horizon reconstructed from ordered absolute times is their last observation time. -/
theorem brownianFirstHitHorizon_elapsed (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (hts : Monotone ts) :
    brownianFirstHitHorizon (n+1) (brownianFirstHitElapsed (n+1) ts) = ts (Fin.last n) := by
  rw [← brownianFirstHitTimes_last,brownianFirstHitTimes_elapsed n ts hts]

/-- The actual finite ordered observation/lifetime law has the explicit density at those exact absolute times. -/
theorem brownianPath_firstHit_ordered_density_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (ht0 : ∀ i, 0 < ts i) (hts : StrictMono ts) :
    (P.restrict {p : BrownianPath | ts (Fin.last n) < firstPassageTime (driftedBrownianPath a p) c}).map
      (fun p => ((fun i => c-(p (ts i)+a*(ts i : ℝ))),
        (firstPassageTime (driftedBrownianPath a p) c : ℝ))) =
      (volume.prod volume).withDensity (fun z : (Fin (n+1) → ℝ) × ℝ =>
        brownianFirstHitFinitePDF a (n+1) (brownianFirstHitElapsed (n+1) ts) c z.1 z.2) := by
  have he := brownianPath_firstHit_finite_density_map P hB a c ha hc (n+1)
    (brownianFirstHitElapsed (n+1) ts) (brownianFirstHitElapsed_pos (n+1) ts ht0 hts)
  rw [brownianFirstHitHorizon_elapsed n ts hts.monotone] at he
  have hs : brownianFirstHitSamples (n+1) (brownianFirstHitElapsed (n+1) ts) a c =
      (fun p : BrownianPath => fun i => c-(p (ts i)+a*(ts i : ℝ))) := by
    funext p i
    simp only [brownianFirstHitSamples,brownianFirstHitTimes_elapsed n ts hts.monotone]
  rw [hs] at he
  exact he


/-- The explicit finite marked density vanishes when any observed remaining level is nonpositive. -/
theorem brownianFirstHitFinitePDF_of_state_le_zero (a c : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0)
    (xs : Fin n → ℝ) (t : ℝ) (i : Fin n) (hi : xs i ≤ 0) :
    brownianFirstHitFinitePDF a n ds c xs t = 0 := by
  classical
  induction n generalizing c t with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro h0
        simp only [brownianFirstHitFinitePDF,brownianKilledTransitionPDF,not_lt.mpr h0,and_false,ite_false,
          ENNReal.ofReal_zero,zero_mul]
      · intro hj
        rw [brownianFirstHitFinitePDF,ih (xs 0) (Fin.tail ds) (Fin.tail xs) _ j hj,mul_zero]

/-- All finite density values are finite ENNReal values, directly from their scalar formulas. -/
theorem brownianFirstHitFinitePDF_ne_top (a c : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0)
    (xs : Fin n → ℝ) (t : ℝ) : brownianFirstHitFinitePDF a n ds c xs t ≠ ⊤ := by
  induction n generalizing c t with
  | zero => exact ENNReal.ofReal_ne_top
  | succ n ih =>
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ih (xs 0) (Fin.tail ds) (Fin.tail xs) _)

/-- The product-density measure has precisely the actual pre-hit survival mass. -/
theorem lintegral_brownianFirstHitFinitePDF (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    (∫⁻ z : (Fin n → ℝ) × ℝ, brownianFirstHitFinitePDF a n ds c z.1 z.2 ∂volume.prod volume) =
      P {p : BrownianPath | brownianFirstHitHorizon n ds < firstPassageTime (driftedBrownianPath a p) c} := by
  have he := brownianFirstHitFiniteIntegral_eq_density a c n ds (fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← he]
  exact brownianFirstHitFiniteIntegral_one P hB a c ha hc n ds hds


/-- The exact scalar killed kernel is jointly measurable in elapsed time and both states. -/
theorem measurable_brownianKilledTransitionPDF_time (a : ℝ) :
    Measurable (fun z : ℝ≥0 × (ℝ × ℝ) => brownianKilledTransitionPDF a z.1 z.2.1 z.2.2) := by
  classical
  have hx : Measurable (fun z : ℝ≥0 × (ℝ × ℝ) => z.2.1) := measurable_fst.comp measurable_snd
  have hy : Measurable (fun z : ℝ≥0 × (ℝ × ℝ) => z.2.2) := measurable_snd.comp measurable_snd
  have h1 : Measurable (fun z : ℝ≥0 × (ℝ × ℝ) => gaussianPDFReal 0 z.1 (z.2.2-z.2.1)) :=
    measurable_uncurry_gaussianPDFReal.comp (measurable_const.prodMk (measurable_fst.prodMk (hy.sub hx)))
  have h2 : Measurable (fun z : ℝ≥0 × (ℝ × ℝ) => gaussianPDFReal 0 z.1 (z.2.2+z.2.1)) :=
    measurable_uncurry_gaussianPDFReal.comp (measurable_const.prodMk (measurable_fst.prodMk (hy.add hx)))
  have he : Measurable (fun z : ℝ≥0 × (ℝ × ℝ) => Real.exp (a*(z.2.2-z.2.1)-a^2*(z.1 : ℝ)/2)) := by
    fun_prop
  exact Measurable.ite ((measurableSet_lt measurable_const hx).inter (measurableSet_lt measurable_const hy))
    (he.mul (h1.sub h2)) measurable_const

/-- The actual first-hit lifetime measure restricted beyond a deterministic horizon is the same restriction of its full hitting density. -/
theorem brownianPath_firstHit_restricted_lifetime_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (s : ℝ≥0) :
    (P.restrict {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c}).map
      (fun p => (firstPassageTime (driftedBrownianPath a p) c : ℝ)) =
      (volume.withDensity (fun t => ENNReal.ofReal (brownianFirstHitDensity a c t))).restrict (Ioi (s : ℝ)) := by
  have hm : Measurable (fun p : BrownianPath => (firstPassageTime (driftedBrownianPath a p) c : ℝ)) :=
    NNReal.continuous_coe.measurable.comp ((measurable_firstPassageTime c).comp
      (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)))
  rw [← brownianPath_positiveDrift_firstHit_density_map P hB a c ha hc,Measure.restrict_map hm measurableSet_Ioi]
  congr 1

/-- Projecting the explicit complete finite density to its lifetime gives the actual hitting density restricted beyond the observation horizon. -/
theorem brownianFirstHitFinitePDF_lifetime_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    ((volume.prod volume).withDensity (fun z : (Fin n → ℝ) × ℝ =>
      brownianFirstHitFinitePDF a n ds c z.1 z.2)).map Prod.snd =
      (volume.withDensity (fun t => ENNReal.ofReal (brownianFirstHitDensity a c t))).restrict
        (Ioi (brownianFirstHitHorizon n ds : ℝ)) := by
  rw [← brownianPath_firstHit_finite_density_map P hB a c ha hc n ds hds,
    Measure.map_map measurable_snd (measurable_brownianFirstHitObservation_fixed n ds a c)]
  exact brownianPath_firstHit_restricted_lifetime_map P hB a c ha hc _




/-- The Gaussian heat density is jointly continuous in positive elapsed time and state. -/
theorem continuousAt_brownian_heatPDF (T : ℝ≥0) (x : ℝ) (hT : T ≠ 0) :
    ContinuousAt (fun z : ℝ≥0 × ℝ => gaussianPDFReal 0 z.1 z.2) (T,x) := by
  have hpos : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  unfold gaussianPDFReal
  fun_prop (disch := positivity)

/-- The first-hit density is jointly continuous in remaining level and positive remaining time. -/
theorem continuousAt_brownianFirstHitDensity_joint (a c t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun z : ℝ × ℝ => brownianFirstHitDensity a z.1 z.2) (c,t) := by
  have hc : ContinuousAt (fun z : ℝ × ℝ => z.1/z.2*(Real.sqrt (2*Real.pi*z.2))⁻¹*
      Real.exp (-z.1^2/(2*z.2)+a*z.1-a^2*z.2/2)) (c,t) := by
    fun_prop (disch := positivity)
  have he : (fun z : ℝ × ℝ => brownianFirstHitDensity a z.1 z.2) =ᶠ[𝓝 (c,t)]
      (fun z : ℝ × ℝ => z.1/z.2*(Real.sqrt (2*Real.pi*z.2))⁻¹*
        Real.exp (-z.1^2/(2*z.2)+a*z.1-a^2*z.2/2)) := by
    filter_upwards [(continuous_snd.tendsto (c,t)).eventually (Ioi_mem_nhds ht)] with z hz
    change 0 < z.2 at hz
    simp only [brownianFirstHitDensity,ite_eq_left hz]
  exact hc.congr_of_eventuallyEq he

end DOZZ.Proofs
