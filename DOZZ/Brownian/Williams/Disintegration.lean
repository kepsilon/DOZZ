/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.BandAverage
/-!
# The Williams maximum disintegration

The band average proves factorization for bounded continuous prefix tests and
every ordered positive finite future cylinder. Weighting the original Brownian
law by one such prefix test turns this into equality of finite future
observation measures. Ordered positive observations determine the whole
continuous-path measure: a finite set of times is sorted after removing zero,
reconstructed from its positive ordered coordinates, and completed by the
almost-sure value zero at time zero. The evaluation-generated path sigma
algebra and uniqueness of projective limits then give the full weighted future
law on the continuous-path carrier.

For a measurable future event, this weighted law determines its complete
prefix measure by bounded continuous tests. Equality of rectangle masses
therefore identifies the actual marked maximum split law with the product
of the positive-drift first-hit mixture and the given conditioned law.
The product-law identity gives all nonnegative measurable prefix and future
tests directly, including infinite integrals, without extra integrability
or continuity premises in the final statement.

The final declaration has exactly the signature of
`DOZZ.brownian_williams_maximum_disintegration`. Its AE measurability guards
come from the actual maximum geometry and first-hit measurability proofs. The
first-hit mixture itself is jointly measurable in its level and marked prefix,
so the level-kernel measurability guard is retained for every test in the
statement.

This module uses the finite-density characterization of the given entrance
law. It does not use or assume a conditioned last-exit avoidance identity. The
latter is a separate input for first-hit reversal.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

private noncomputable def williamsMark (ν : ℝ) (p : BrownianPath) : ℝ × StoppedBrownianPath :=
  (driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p)

private theorem aemeasurable_mark (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) :
    AEMeasurable (williamsMark ν) P :=
  (aemeasurable_driftedBrownianMaximum P hB ν hν).prodMk
    (aemeasurable_brownianPreMaximumSegment P hB ν hν)

/-- The literal positive-drift first-hit mixture against the maximum reference law
`DOZZ.brownianMaximumReferenceLaw`. -/
noncomputable def brownianWilliamsPrefixLaw (P : Measure BrownianPath) (ν : ℝ) :
    Measure (ℝ × StoppedBrownianPath) :=
  ((brownianMaximumReferenceLaw ν).prod P).map (fun z =>
    (z.1,positiveDriftFirstHitSegment ν z.1 z.2))

private theorem measurable_prefixMap (ν : ℝ) :
    Measurable (fun z : ℝ × BrownianPath => (z.1,positiveDriftFirstHitSegment ν z.1 z.2)) :=
  measurable_fst.prodMk (measurable_positiveDriftFirstHitSegment_joint ν)

/-- Nonnegative tests of the full prefix mixture are the exact level-dependent first-hit integrals. -/
theorem lintegral_brownianWilliamsPrefixLaw (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂brownianWilliamsPrefixLaw P ν) =
      ∫⁻ m, ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P ∂brownianMaximumReferenceLaw ν := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [brownianWilliamsPrefixLaw,lintegral_map hF (measurable_prefixMap ν)]
  exact lintegral_prod _ (hF.comp (measurable_prefixMap ν)).aemeasurable

private theorem prefix_finite (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) :
    IsFiniteMeasure (brownianWilliamsPrefixLaw P ν) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  unfold brownianWilliamsPrefixLaw
  infer_instance

/-- A bounded continuous nonnegative test has a finite common ENNReal bound. -/
private theorem bcf_bound {E : Type*} [TopologicalSpace E] (f : BoundedContinuousFunction E ℝ≥0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x, (f x : ℝ≥0∞) ≤ K := by
  obtain ⟨K,hK⟩ := f.isBounded_range.bddAbove
  exact ⟨K,ENNReal.coe_ne_top,fun x => ENNReal.coe_le_coe.mpr (hK (mem_range_self x))⟩

private noncomputable def weightedFutureLaw (P : Measure BrownianPath) (ν : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) : Measure BrownianPath :=
  (P.withDensity (fun p => F (williamsMark ν p))).map (brownianPostMaximumPath ν)

private theorem weightedFuture_finite (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (KF : ℝ≥0∞) (hKF : KF ≠ ∞)
    (hFb : ∀ z, F z ≤ KF) : IsFiniteMeasure (weightedFutureLaw P ν F) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hh : (∫⁻ p, F (williamsMark ν p) ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top hKF ((lintegral_mono (fun p => hFb _)).trans_eq
      (by rw [lintegral_const,measure_univ,mul_one]))
  let _ := isFiniteMeasure_withDensity hh
  unfold weightedFutureLaw
  infer_instance

private theorem weightedFuture_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ q, G q ∂weightedFutureLaw P ν F) =
      ∫⁻ p, F (williamsMark ν p)*G (brownianPostMaximumPath ν p) ∂P := by
  have hW : AEMeasurable (fun p => F (williamsMark ν p)) P :=
    hF.comp_aemeasurable (aemeasurable_mark P hB ν hν)
  have hpost := aemeasurable_brownianPostMaximumPath P hB ν hν
  have hp := hpost.mono_ac (withDensity_absolutelyContinuous P (fun p => F (williamsMark ν p)))
  have hGP : AEMeasurable (fun p => G (brownianPostMaximumPath ν p)) P := hG.comp_aemeasurable hpost
  rw [weightedFutureLaw,lintegral_map' hG.aemeasurable hp,
    lintegral_withDensity_eq_lintegral_mul₀ hW hGP]
  rfl

private theorem weightedFuture_ordered_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞)
    (hF : Continuous F)
    (KF : ℝ≥0∞) (hKF : KF ≠ ∞)
    (hFb : ∀ z, F z ≤ KF)
    (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (ht0 : ∀ i, 0 < ts i) (hts : StrictMono ts) :
    (weightedFutureLaw P ν F).map (fun q i => q (ts i)) =
      (∫⁻ z, F z ∂brownianWilliamsPrefixLaw P ν) • Q.map (fun q i => q (ts i)) := by
  let _ := weightedFuture_finite P hB ν F KF hKF hFb
  have hEval : Measurable (fun q : BrownianPath => fun i => q (ts i)) :=
    Measurable.of_eval (fun i => ContinuousMap.measurable_eval _)
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  obtain ⟨KG,hKG,hGb⟩ := bcf_bound f
  have hφ : Continuous (fun ys => (f ys : ℝ≥0∞)) := ENNReal.continuous_coe.comp f.continuous
  have hG : Measurable (fun q : BrownianPath => (f (fun i => q (ts i)) : ℝ≥0∞)) := hφ.measurable.comp hEval
  rw [lintegral_map hφ.measurable hEval,lintegral_smul_measure,
    lintegral_map hφ.measurable hEval,weightedFuture_lintegral P hB ν hν F hF.measurable _ hG,
    lintegral_brownianWilliamsPrefixLaw P hB ν F hF.measurable]
  exact brownianPath_williams_continuous_ordered_lintegral P hB ν hν Q hQ F hF n ts ht0 hts
    _ hφ KF KG hKF hKG hFb hGb

/-- Sorting finite positive observation sets and restoring the known zero coordinate
identifies the entire path law. The carrier sigma algebra is generated by evaluations. -/
private theorem positive_ordered_path_law_unique (μ η : Measure BrownianPath)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ0 : ∀ᵐ q ∂μ, q 0 = 0) (hη0 : ∀ᵐ q ∂η, q 0 = 0) (hmass : μ univ = η univ)
    (hordered : ∀ (n : ℕ) (ts : Fin (n+1) → ℝ≥0), (∀ i, 0 < ts i) → StrictMono ts →
      μ.map (fun q i => q (ts i)) = η.map (fun q i => q (ts i))) : μ = η := by
  classical
  have heval : Measurable (fun q : BrownianPath => fun t : ℝ≥0 => q t) :=
    Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)
  have hfinite (I : Finset ℝ≥0) : μ.map (fun q (i : I) => q i) = η.map (fun q (i : I) => q i) := by
    let J := I.erase 0
    let ts : Fin J.card → ℝ≥0 := J.orderEmbOfFin rfl
    have ht0 (i : Fin J.card) : 0 < ts i := by
      have hm := J.orderEmbOfFin_mem rfl i
      exact pos_iff_ne_zero.mpr (Finset.mem_erase.mp hm).1
    have hts : StrictMono ts := (J.orderEmbOfFin rfl).strictMono
    have hmaps : μ.map (fun q i => q (ts i)) = η.map (fun q i => q (ts i)) := by
      by_cases hc : J.card = 0
      ·
        have : IsEmpty (Fin J.card) := by rw [hc]; infer_instance
        apply Measure.ext_of_lintegral
        intro f hf
        have he (ys : Fin J.card → ℝ) : ys = (fun i => isEmptyElim i) := Subsingleton.elim _ _
        have hm : Measurable (fun q : BrownianPath => fun i => q (ts i)) :=
          Measurable.of_eval (fun i => ContinuousMap.measurable_eval _)
        rw [lintegral_map hf hm,lintegral_map hf hm]
        simp only [he,lintegral_const,hmass]
      · obtain ⟨n,hc⟩ := Nat.exists_eq_succ_of_ne_zero hc
        have he := hordered n (fun i => ts (Fin.cast hc.symm i))
          (fun i => ht0 _) (hts.comp (Fin.castOrderIso hc.symm).strictMono)
        have hm : Measurable (fun q : BrownianPath => fun i => q (ts i)) :=
          Measurable.of_eval (fun i => ContinuousMap.measurable_eval _)
        apply (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => ℝ) (finCongr hc)).map_measurableEquiv_injective
        rw [Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable hm,
          Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable hm]
        exact he
    let R : (Fin J.card → ℝ) → (I → ℝ) := fun ys i =>
      if hi : 0 < i.1 then ys ((J.orderIsoOfFin rfl).symm ⟨i.1,Finset.mem_erase.mpr ⟨hi.ne',i.2⟩⟩) else 0
    have hR : Measurable R := by
      apply Measurable.of_eval
      intro i
      by_cases hi : 0 < i.1
      · simp only [R,hi,dite_true]
        exact measurable_pi_apply _
      · simp only [R,hi,dite_false]
        exact measurable_const
    have hEvalJ : Measurable (fun q : BrownianPath => fun i => q (ts i)) :=
      Measurable.of_eval (fun i => ContinuousMap.measurable_eval _)
    have hr (q : BrownianPath) (hq : q 0 = 0) :
        (fun i : I => q i) = R (fun i => q (ts i)) := by
      funext i
      by_cases hi : 0 < i.1
      · simp only [R,hi,dite_true]
        apply congrArg q
        exact (congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply
          ⟨i.1,Finset.mem_erase.mpr ⟨hi.ne',i.2⟩⟩)).symm
      · have hz : i.1 = 0 := le_antisymm (le_of_not_gt hi) bot_le
        dsimp only [R]
        rw [dite_eq_right hi,hz,hq]
    calc
      _ = (μ.map (fun q i => q (ts i))).map R := by
        rw [Measure.map_map hR hEvalJ]
        exact Measure.map_congr (hμ0.mono (fun q hq => hr q hq))
      _ = (η.map (fun q i => q (ts i))).map R := by rw [hmaps]
      _ = _ := by
        rw [Measure.map_map hR hEvalJ]
        exact (Measure.map_congr (hη0.mono (fun q hq => hr q hq))).symm
  apply brownianPath_measure_eq_of_process_map_eq
  let K (I : Finset ℝ≥0) := η.map (fun q (i : I) => q i)
  have hK (I : Finset ℝ≥0) : IsFiniteMeasure (K I) := by dsimp [K]; infer_instance
  let _ := hK
  apply IsProjectiveLimit.unique (P := K)
  · intro I
    rw [Measure.map_map (Finset.measurable_restrict I) heval]
    exact hfinite I
  · intro I
    rw [Measure.map_map (Finset.measurable_restrict I) heval]
    rfl

private theorem post_start_zero (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) :
    ∀ᵐ p ∂P, brownianPostMaximumPath ν p 0 = 0 := by
  filter_upwards [brownianPath_globalMaximumTime_attains_ae P hB ν hν] with p hp
  change p (driftedBrownianMaximumTime ν p+0)-ν*((driftedBrownianMaximumTime ν p+0 : ℝ≥0) : ℝ)-
      driftedBrownianMaximum ν p = 0
  rw [add_zero]
  linarith only [hp]

/-- Ordered finite-cylinder factorization identifies the full prefix-weighted future law.
The mass and time-zero boundary are transported from the actual maximum split. -/
private theorem weightedFuture_law (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞)
    (hF : Continuous F)
    (KF : ℝ≥0∞) (hKF : KF ≠ ∞)
    (hFb : ∀ z, F z ≤ KF) :
    weightedFutureLaw P ν F = (∫⁻ z, F z ∂brownianWilliamsPrefixLaw P ν) • Q := by
  let _ := hQ.2.1
  let _ := prefix_finite P hB ν hν
  let _ := weightedFuture_finite P hB ν F KF hKF hFb
  let c := ∫⁻ z, F z ∂brownianWilliamsPrefixLaw P ν
  have hc : c ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hKF (measure_ne_top (brownianWilliamsPrefixLaw P ν) univ)) ((lintegral_mono hFb).trans_eq (lintegral_const KF))
  let _ := Measure.smul_finite Q hc
  have hpost := aemeasurable_brownianPostMaximumPath P hB ν hν
  have hac := withDensity_absolutelyContinuous P (fun p => F (williamsMark ν p))
  have hp0 : ∀ᵐ q ∂weightedFutureLaw P ν F, q 0 = 0 := by
    apply (ae_map_iff (hpost.mono_ac hac)
      (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)).mpr
    exact hac.ae_le (post_start_zero P hB ν hν)
  have hqc : c • Q ≪ Q := by
    refine Measure.AbsolutelyContinuous.mk (fun s hs hz => ?_)
    rw [Measure.smul_apply,hz,smul_zero]
  have hq0 : ∀ᵐ q ∂c • Q, q 0 = 0 := hqc.ae_le hQ.2.2.1
  have hmass : (weightedFutureLaw P ν F) univ = (c • Q) univ := by
    have he := weightedFuture_ordered_map P hB ν hν Q hQ F hF KF hKF hFb 0
      (fun _ => 1) (fun _ => zero_lt_one) (by intro i j hij; omega)
    have hm : Measurable (fun q : BrownianPath => fun _ : Fin 1 => q 1) :=
      Measurable.of_eval (fun _ => ContinuousMap.measurable_eval _)
    have hh := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ univ) he
    simpa only [Measure.map_apply hm MeasurableSet.univ,preimage_univ,Measure.smul_apply] using hh
  apply positive_ordered_path_law_unique _ _ hp0 hq0 hmass
  intro n ts ht0 hts
  rw [Measure.map_smul _ (Measurable.of_eval (fun i => ContinuousMap.measurable_eval (ts i))).aemeasurable]
  exact weightedFuture_ordered_map P hB ν hν Q hQ F hF KF hKF hFb n ts ht0 hts

/-- The actual maximum split has the complete product law, including its lifetime-marked prefix. -/
theorem brownianPath_williams_joint_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q) :
    P.map (fun p => ((driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p),
      brownianPostMaximumPath ν p)) = (brownianWilliamsPrefixLaw P ν).prod Q := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := hQ.2.1
  let _ := prefix_finite P hB ν hν
  have hm := aemeasurable_mark P hB ν hν
  have hp := aemeasurable_brownianPostMaximumPath P hB ν hν
  apply Measure.ext_prod
  intro A B hA hBset
  let S : Set BrownianPath := (brownianPostMaximumPath ν) ⁻¹' B
  have hS : NullMeasurableSet S P := hp.nullMeasurableSet_preimage hBset
  let μB := (P.restrict S).map (williamsMark ν)
  have hμB : μB = (Q B) • brownianWilliamsPrefixLaw P ν := by
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro f
    obtain ⟨KF,hKF,hFb⟩ := bcf_bound f
    have hf : Continuous (fun z => (f z : ℝ≥0∞)) := ENNReal.continuous_coe.comp f.continuous
    have he := weightedFuture_law P hB ν hν Q hQ _ hf KF hKF hFb
    have hpf := hp.mono_ac (withDensity_absolutelyContinuous P (fun p => (f (williamsMark ν p) : ℝ≥0∞)))
    have heB := congrArg (fun μ : Measure BrownianPath => μ B) he
    rw [weightedFutureLaw,Measure.map_apply_of_aemeasurable hpf hBset,
      withDensity_apply₀ _ hS,Measure.smul_apply,smul_eq_mul] at heB
    change (∫⁻ z, (f z : ℝ≥0∞) ∂(P.restrict S).map (williamsMark ν)) = _
    rw [lintegral_map' hf.measurable.aemeasurable hm.restrict,lintegral_smul_measure]
    exact heB.trans (mul_comm _ _)
  change (P.map (fun p => (williamsMark ν p,brownianPostMaximumPath ν p))) (A ×ˢ B) = _
  rw [Measure.map_apply_of_aemeasurable (hm.prodMk hp) (hA.prod hBset),Measure.prod_prod]
  have heA := congrArg (fun μ : Measure (ℝ × StoppedBrownianPath) => μ A) hμB
  rw [Measure.map_apply_of_aemeasurable hm.restrict hA,Measure.restrict_apply₀ (hm.restrict.nullMeasurableSet_preimage hA),
    Measure.smul_apply,smul_eq_mul] at heA
  change P (((williamsMark ν) ⁻¹' A) ∩ S) = (brownianWilliamsPrefixLaw P ν) A*Q B
  exact heA.trans (mul_comm _ _)

/-- The full measurable source identity follows from the actual product split law. -/
theorem brownianPath_williams_measurable_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p, F (driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p)*
        G (brownianPostMaximumPath ν p) ∂P) =
      ∫⁻ m, (∫⁻ u, F (m,u) ∂P.map (positiveDriftFirstHitSegment ν m)) *
        (∫⁻ q, G q ∂Q) ∂brownianMaximumReferenceLaw ν := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := hQ.2.1
  have hmap := (aemeasurable_mark P hB ν hν).prodMk (aemeasurable_brownianPostMaximumPath P hB ν hν)
  have htest : Measurable (fun z : (ℝ × StoppedBrownianPath) × BrownianPath => F z.1*G z.2) :=
    (hF.comp measurable_fst).mul (hG.comp measurable_snd)
  calc
    _ = ∫⁻ z, F z.1*G z.2 ∂P.map (fun p => ((driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p),
        brownianPostMaximumPath ν p)) := (lintegral_map' htest.aemeasurable hmap).symm
    _ = ∫⁻ z, F z.1*G z.2 ∂(brownianWilliamsPrefixLaw P ν).prod Q := by
      rw [brownianPath_williams_joint_map P hB ν hν Q hQ]
    _ = (∫⁻ z, F z ∂brownianWilliamsPrefixLaw P ν)*(∫⁻ q, G q ∂Q) :=
      lintegral_prod_mul hF.aemeasurable hG.aemeasurable
    _ = _ := by
      rw [lintegral_brownianWilliamsPrefixLaw P hB ν F hF]
      have hK := measurable_positiveFirstHit_kernel P ν F hF
      have he (m : ℝ) : (∫⁻ u, F (m,u) ∂P.map (positiveDriftFirstHitSegment ν m)) =
          ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P :=
        lintegral_map (hF.comp (measurable_const.prodMk measurable_id))
          (measurable_positiveDriftFirstHitSegment ν m)
      simp_rw [← he]
      rw [lintegral_mul_const _ hK]

/-- The positive-drift first-hit prefix kernel is a probability law on the exact carrier
`ℝ × StoppedBrownianPath`. -/
theorem isProbabilityMeasure_brownianWilliamsPrefixLaw (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) :
    IsProbabilityMeasure (brownianWilliamsPrefixLaw P ν) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  constructor
  rw [brownianWilliamsPrefixLaw,Measure.map_apply (measurable_prefixMap ν) MeasurableSet.univ,
    preimage_univ,measure_univ]



/-- Proof of `DOZZ.brownian_williams_maximum_disintegration`, including all original
AE-measurability guards. -/
theorem brownian_williams_maximum_disintegration
    (P : Measure BrownianPath)
    (hB : ProbabilityTheory.IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) :
    (AEMeasurable (driftedBrownianMaximum ν) P) ∧
    (AEMeasurable (brownianPreMaximumSegment ν) P) ∧
    (AEMeasurable (brownianPostMaximumPath ν) P) ∧
    (∀ m : ℝ, 0 < m → AEMeasurable (positiveDriftFirstHitSegment ν m) P) ∧
    ∀ (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞),
      Measurable F → Measurable G →
        (AEMeasurable (fun m : ℝ =>
          ∫⁻ u, F (m, u) ∂P.map (positiveDriftFirstHitSegment ν m))
            (brownianMaximumReferenceLaw ν) ∧
        ∫⁻ p, F (driftedBrownianMaximum ν p, brownianPreMaximumSegment ν p) *
          G (brownianPostMaximumPath ν p) ∂P =
        ∫⁻ m,
          (∫⁻ u, F (m, u) ∂P.map (positiveDriftFirstHitSegment ν m)) *
            (∫⁻ q, G q ∂Qν) ∂brownianMaximumReferenceLaw ν) := by
  refine ⟨aemeasurable_driftedBrownianMaximum P hB ν hν,
    aemeasurable_brownianPreMaximumSegment P hB ν hν,
    aemeasurable_brownianPostMaximumPath P hB ν hν,
    fun m _ => (measurable_positiveDriftFirstHitSegment ν m).aemeasurable,?_⟩
  intro F G hF hG
  exact ⟨aemeasurable_positiveFirstHit_kernel P hB ν F hF,
    brownianPath_williams_measurable_lintegral P hB ν hν Qν hQν F hF G hG⟩

end DOZZ.Proofs
