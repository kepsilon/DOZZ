/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.EntranceLimit
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
/-!
# Williams disintegration on bounded continuous finite cylinders

Integrating the exact source thin-band identity over its lower edge gives an
average over a unit interval below the actual maximum. This is the integral
version of the source maximum mesh: on each original path every averaged lower
edge tends to its maximum, its first-hit prefix tends to the pre-maximum
segment, and its full future tends to the post path. The maximum is positive
almost surely, so the lower-edge positivity cutoff eventually disappears. A
common bounded test dominates on the probability product with the unit
interval, making this convergence literal dominated convergence without
additional level-regularity hypotheses.

The exact band formula factors the average into its harmonic band ratio, the
positive-drift first-hit level integral, and the actual conditioned future
test. Their limits are the rate factor 2ν, the same level integral, and the
entrance-cylinder test. The exponential maximum reference law absorbs the rate
factor. This proves the full source factorization on bounded continuous prefix
tests and finite future cylinders.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

private theorem affine_lintegral (M ε : ℝ) (hε : 0 < ε) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ m, H m) = ENNReal.ofReal ε*(∫⁻ u, H (M-ε*u)) := by
  have hS : Measurable (fun m : ℝ => H (M+m)) := hH.comp (measurable_const.add measurable_id)
  calc
    _ = ∫⁻ m, H (M+m) := (lintegral_add_left_eq_self H M).symm
    _ = ENNReal.ofReal |(-ε)| *(∫⁻ u, H (M+(-ε)*u)) := by
      conv_lhs => rw [← Real.smul_map_volume_mul_left (a := -ε) (neg_ne_zero.mpr hε.ne')]
      have hm : Measurable (fun x : ℝ => -ε*x) := measurable_const.mul measurable_id
      rw [lintegral_smul_measure,lintegral_map hS hm]
      rfl
    _ = _ := by simp only [abs_neg,abs_of_pos hε,neg_mul,← sub_eq_add_neg]

private theorem affine_band_iff (M ε u : ℝ) (hε : 0 < ε) :
    (0 < M-ε*u ∧ M-ε*u ≤ M ∧ M < (M-ε*u)+ε) ↔
      (u ∈ Ico 0 1 ∧ 0 < M-ε*u) := by
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    refine ⟨⟨?_,?_⟩,hp⟩ <;> nlinarith only [hε,hlo,hhi]
  · rintro ⟨⟨hu0,hu1⟩,hp⟩
    refine ⟨hp,?_,?_⟩ <;> nlinarith only [hε,hu0,hu1]

private theorem harmonic_band_ratio_limit (ν : ℝ) (hν : 0 < ν) :
    Tendsto (fun ε => conditionedH ν ε/ε) (𝓝[>] (0 : ℝ)) (𝓝 (2*ν)) := by
  have hd : HasDerivAt (conditionedH ν) (2*ν) 0 := by
    have harg : HasDerivAt (fun x : ℝ => Real.exp (-2*ν*x)) (-2*ν) 0 := by
      simpa only [id_eq,mul_zero,Real.exp_zero,mul_one,one_mul] using
        ((hasDerivAt_id (0 : ℝ)).const_mul (-2*ν)).exp
    convert (hasDerivAt_const (0 : ℝ) 1).sub harg using 1
    · funext x
      simp only [conditionedH,ite_eq_right hν.ne',Pi.sub_apply]
    · ring
  have hh := hd.tendsto_slope_zero_right
  simp only [zero_add,smul_eq_mul] at hh
  change Tendsto (fun t : ℝ => t⁻¹*(conditionedH ν t-conditionedH ν 0)) (𝓝[>] 0) (𝓝 (2*ν)) at hh
  simp only [conditionedH,ite_eq_right hν.ne',mul_zero,Real.exp_zero,sub_self,sub_zero] at hh
  convert hh using 1
  funext t
  simp only [conditionedH,ite_eq_right hν.ne',div_eq_mul_inv]
  ring

noncomputable def brownianFirstHitFuture (ν m : ℝ) (p : BrownianPath) : BrownianPath :=
  driftedBrownianPath (-ν) (brownianShiftPath (firstPassageTime (driftedBrownianPath (-ν) p) m) p)

private theorem measurable_future (ν : ℝ) :
    Measurable (fun z : ℝ × BrownianPath => brownianFirstHitFuture ν z.1 z.2) := by
  have hd : Measurable (fun z : ℝ × BrownianPath => driftedBrownianPath (-ν) z.2) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_snd)
  have ht := measurable_firstPassageTime_joint.comp (measurable_fst.prodMk hd)
  exact continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk
    (continuous_brownianShiftPath.measurable.comp (ht.prodMk measurable_snd)))

noncomputable def brownianWilliamsLevelTest (ν : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞)
    (z : ℝ × BrownianPath) : ℝ≥0∞ :=
  F (z.1,positiveDriftFirstHitSegment (-ν) z.1 z.2)*G (brownianFirstHitFuture ν z.1 z.2)

private theorem measurable_levelTest (ν : ℝ) (F : ℝ × StoppedBrownianPath → ℝ≥0∞)
    (G : BrownianPath → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) :
    Measurable (brownianWilliamsLevelTest ν F G) :=
  (hF.comp (measurable_fst.prodMk (measurable_positiveDriftFirstHitSegment_joint (-ν)))).mul
    (hG.comp (measurable_future ν))

noncomputable def brownianWilliamsBandTest (ν ε : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞) :
    ℝ × BrownianPath → ℝ≥0∞ :=
  {z | 0 < z.1 ∧ z.1 ≤ driftedBrownianMaximum ν z.2 ∧
    driftedBrownianMaximum ν z.2 < z.1+ε}.indicator (brownianWilliamsLevelTest ν F G)

private theorem aemeasurable_bandTest (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν) (ε : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    AEMeasurable (brownianWilliamsBandTest ν ε F G) ((volume : Measure ℝ).prod P) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hm := (aemeasurable_driftedBrownianMaximum P hB ν hν).comp_snd (μ := (volume : Measure ℝ))
  exact (measurable_levelTest ν F G hF hG).aemeasurable.indicator₀
    ((nullMeasurableSet_lt aemeasurable_const measurable_fst.aemeasurable).inter
      ((nullMeasurableSet_le measurable_fst.aemeasurable hm).inter
        (nullMeasurableSet_lt hm (measurable_fst.add measurable_const).aemeasurable)))

/-- The positive lower-edge test averaged immediately below the actual maximum. -/
noncomputable def brownianWilliamsAverageTest (ν ε : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞) :
    ℝ × BrownianPath → ℝ≥0∞ :=
  {z | 0 < driftedBrownianMaximum ν z.2-ε*z.1}.indicator
    (fun z => brownianWilliamsLevelTest ν F G (driftedBrownianMaximum ν z.2-ε*z.1,z.2))

private theorem aemeasurable_averageTest (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν) (ε : ℝ)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (μ : Measure ℝ) :
    AEMeasurable (brownianWilliamsAverageTest ν ε F G) (μ.prod P) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hm := (aemeasurable_driftedBrownianMaximum P hB ν hν).comp_snd (μ := μ)
  have hl : AEMeasurable (fun z : ℝ × BrownianPath => driftedBrownianMaximum ν z.2-ε*z.1) (μ.prod P) :=
    hm.sub (measurable_const.mul measurable_fst).aemeasurable
  exact ((measurable_levelTest ν F G hF hG).comp_aemeasurable
    (hl.prodMk measurable_snd.aemeasurable)).indicator₀
      (nullMeasurableSet_lt aemeasurable_const hl)

private theorem band_affine_path (ν ε : ℝ) (hε : 0 < ε)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (p : BrownianPath) :
    (∫⁻ m, brownianWilliamsBandTest ν ε F G (m,p)) =
      ENNReal.ofReal ε*(∫⁻ u in Ico (0 : ℝ) 1, brownianWilliamsAverageTest ν ε F G (u,p)) := by
  have ht : Measurable (fun m => brownianWilliamsLevelTest ν F G (m,p)) :=
    (measurable_levelTest ν F G hF hG).comp (measurable_id.prodMk measurable_const)
  have hplus : Measurable (fun m : ℝ => m+ε) := measurable_id.add measurable_const
  have hs : MeasurableSet {m : ℝ | 0 < m ∧ m ≤ driftedBrownianMaximum ν p ∧
      driftedBrownianMaximum ν p < m+ε} :=
    (measurableSet_lt measurable_const measurable_id).inter
      ((measurableSet_le measurable_id measurable_const).inter
        (measurableSet_lt measurable_const hplus))
  have hh : Measurable (fun m => brownianWilliamsBandTest ν ε F G (m,p)) := ht.indicator hs
  rw [affine_lintegral (driftedBrownianMaximum ν p) ε hε _ hh]
  congr 1
  rw [← lintegral_indicator measurableSet_Ico]
  apply lintegral_congr
  intro u
  simp only [brownianWilliamsBandTest,brownianWilliamsAverageTest,Set.indicator_apply,
    Set.mem_ofPred_eq,affine_band_iff _ _ _ hε]
  by_cases hu : u ∈ Ico (0 : ℝ) 1 <;>
    by_cases hp : 0 < driftedBrownianMaximum ν p-ε*u <;> simp only [hu,hp,and_self,and_false,
      false_and,ite_true,ite_false]

private theorem band_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ m, ∫⁻ p, brownianWilliamsBandTest ν ε F G (m,p) ∂P) =
      ENNReal.ofReal (conditionedH ν ε)*(∫⁻ q, G q ∂brownianBelowConditionedLaw P ν ε)*
        (∫⁻ m in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-2*ν*m))*
          ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P) := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let K : ℝ → ℝ≥0∞ := fun m => ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P
  have hK : Measurable K :=
    (hF.comp (measurable_fst.prodMk (measurable_positiveDriftFirstHitSegment_joint ν))).lintegral_prod_right'
  have hExp : Measurable (fun m : ℝ => ENNReal.ofReal (Real.exp (-2*ν*m))) := by fun_prop
  have hv : Measurable (fun m : ℝ => ENNReal.ofReal (Real.exp (-2*ν*m))*K m) := hExp.mul hK
  have he (m : ℝ) : (∫⁻ p, brownianWilliamsBandTest ν ε F G (m,p) ∂P) =
      (Ioi (0 : ℝ)).indicator (fun m => ENNReal.ofReal (conditionedH ν ε)*
        (∫⁻ q, G q ∂brownianBelowConditionedLaw P ν ε)*
          (ENNReal.ofReal (Real.exp (-2*ν*m))*K m)) m := by
    by_cases hm : 0 < m
    · have hM := aemeasurable_driftedBrownianMaximum P hB ν hν
      have hs : NullMeasurableSet {p | m ≤ driftedBrownianMaximum ν p ∧
          driftedBrownianMaximum ν p < m+ε} P :=
        (nullMeasurableSet_le aemeasurable_const hM).inter (nullMeasurableSet_lt hM aemeasurable_const)
      have hb : (fun p => brownianWilliamsBandTest ν ε F G (m,p)) =
          {p | m ≤ driftedBrownianMaximum ν p ∧ driftedBrownianMaximum ν p < m+ε}.indicator
            (fun p => F (m,positiveDriftFirstHitSegment (-ν) m p)*G (brownianFirstHitFuture ν m p)) := by
        funext p
        simp only [brownianWilliamsBandTest,brownianWilliamsLevelTest,Set.indicator_apply,
          Set.mem_ofPred_eq,hm,true_and]
      rw [hb,lintegral_indicator₀ hs]
      dsimp only [brownianFirstHitFuture]
      rw [brownianPath_williams_thinBand_lintegral P hB ν m ε hν hm hε
        (fun z => F (m,z)) (hF.comp (measurable_const.prodMk measurable_id)) G hG,
          Set.indicator_of_mem (show m ∈ Ioi (0 : ℝ) from hm)]
      ring
    · simp only [brownianWilliamsBandTest,Set.indicator_apply,Set.mem_ofPred_eq,hm,false_and,
        ite_false,lintegral_zero,Set.mem_Ioi]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioi,lintegral_const_mul _ hv]

private theorem average_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ u in Ico (0 : ℝ) 1, ∫⁻ p, brownianWilliamsAverageTest ν ε F G (u,p) ∂P) =
      (ENNReal.ofReal ε)⁻¹*ENNReal.ofReal (conditionedH ν ε)*
        (∫⁻ q, G q ∂brownianBelowConditionedLaw P ν ε)*
          (∫⁻ m in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-2*ν*m))*
            ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hband := aemeasurable_bandTest P hB ν hν ε F G hF hG
  have havg := aemeasurable_averageTest P hB ν hν ε F G hF hG (volume.restrict (Ico (0 : ℝ) 1))
  have he : (∫⁻ m, ∫⁻ p, brownianWilliamsBandTest ν ε F G (m,p) ∂P) =
      ENNReal.ofReal ε*(∫⁻ u in Ico (0 : ℝ) 1, ∫⁻ p, brownianWilliamsAverageTest ν ε F G (u,p) ∂P) := by
    rw [lintegral_lintegral_swap (f := fun m p => brownianWilliamsBandTest ν ε F G (m,p)) hband]
    simp_rw [band_affine_path ν ε hε F G hF hG]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← lintegral_lintegral_swap (f := fun u p => brownianWilliamsAverageTest ν ε F G (u,p)) havg]
  rw [band_integral P hB ν ε hν hε F G hF hG] at he
  calc
    _ = (ENNReal.ofReal ε)⁻¹*(ENNReal.ofReal ε*
        (∫⁻ u in Ico (0 : ℝ) 1, ∫⁻ p, brownianWilliamsAverageTest ν ε F G (u,p) ∂P)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top,one_mul]
    _ = _ := by rw [← he]; ring

private theorem maximum_positive_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν) :
    ∀ᵐ p ∂P, 0 < driftedBrownianMaximum ν p := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hm := aemeasurable_driftedBrownianMaximum P hB ν hν
  apply (ae_iff_measure_eq (nullMeasurableSet_lt aemeasurable_const hm)).mpr
  rw [measure_univ]
  change P ((driftedBrownianMaximum ν) ⁻¹' Ioi (0 : ℝ)) = 1
  rw [← Measure.map_apply_of_aemeasurable hm measurableSet_Ioi,
    brownianPath_globalMaximum_Ioi P hB ν 0 hν le_rfl]
  simp only [mul_zero,Real.exp_zero,ENNReal.ofReal_one]

/-- The complete actual thin-band average converges to the maximum split. -/
theorem brownianPath_williams_bandAverage_limit (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Continuous F)
    (G : BrownianPath → ℝ≥0∞) (hG : Continuous G)
    (KF KG : ℝ≥0∞) (hKF : KF ≠ ∞) (hKG : KG ≠ ∞)
    (hFb : ∀ z, F z ≤ KF) (hGb : ∀ q, G q ≤ KG) :
    Tendsto (fun k => ∫⁻ u in Ico (0 : ℝ) 1, ∫⁻ p,
      brownianWilliamsAverageTest ν (xs k) F G (u,p) ∂P) atTop
        (𝓝 (∫⁻ p, F (driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p)*
          G (brownianPostMaximumPath ν p) ∂P)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let μ : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)
  have hμ : μ univ = 1 := by
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    norm_num
  have hprod : (μ.prod P) univ = 1 := by
    rw [← Set.univ_prod_univ,Measure.prod_prod,hμ,measure_univ,one_mul]
  let T : BrownianPath → ℝ≥0∞ := fun p =>
    F (driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p)*G (brownianPostMaximumPath ν p)
  have hT : AEMeasurable T P :=
    (hF.measurable.comp_aemeasurable ((aemeasurable_driftedBrownianMaximum P hB ν hν).prodMk
      (aemeasurable_brownianPreMaximumSegment P hB ν hν))).mul
        (hG.measurable.comp_aemeasurable (aemeasurable_brownianPostMaximumPath P hB ν hν))
  have hbound (k : ℕ) : ∀ z : ℝ × BrownianPath, brownianWilliamsAverageTest ν (xs k) F G z ≤ KF*KG := by
    intro z
    by_cases hz : 0 < driftedBrownianMaximum ν z.2-xs k*z.1
    · simpa only [brownianWilliamsAverageTest,Set.indicator_apply,Set.mem_ofPred_eq,hz,ite_true,
        brownianWilliamsLevelTest] using mul_le_mul' (hFb _) (hGb _)
    · simp only [brownianWilliamsAverageTest,Set.indicator_apply,Set.mem_ofPred_eq,hz,ite_false]
      exact bot_le
  have hfin : (∫⁻ z : ℝ × BrownianPath, KF*KG ∂μ.prod P) ≠ ∞ := by
    rw [lintegral_const,hprod,mul_one]
    exact ENNReal.mul_ne_top hKF hKG
  have hconv : ∀ᵐ z ∂μ.prod P, Tendsto
      (fun k => brownianWilliamsAverageTest ν (xs k) F G z) atTop (𝓝 (T z.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico),
      Measure.quasiMeasurePreserving_snd.ae (maximum_positive_ae P hB ν hν),
      Measure.quasiMeasurePreserving_snd.ae (brownianPath_firstHitSegment_tendsto_preMaximum_ae P hB ν hν),
      Measure.quasiMeasurePreserving_snd.ae (brownianPath_firstHitFuture_tendsto_postMaximum_ae P hB ν hν)]
        with z hu hM hpre hpost
    let cs : ℕ → ℝ := fun k => driftedBrownianMaximum ν z.2-xs k*z.1
    have hcs (k : ℕ) : cs k ≤ driftedBrownianMaximum ν z.2 :=
      sub_le_self _ (mul_nonneg (hxs k).le hu.1)
    have hclim : Tendsto cs atTop (𝓝 (driftedBrownianMaximum ν z.2)) := by
      simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (hxlim.mul_const z.1)
    have hA := hF.continuousAt.tendsto.comp (hclim.prodMk_nhds (hpre cs hcs hclim))
    have hB' := hG.continuousAt.tendsto.comp (hpost cs hcs hclim)
    have hh := ENNReal.Tendsto.mul hA (Or.inr (ne_top_of_le_ne_top hKG (hGb _)))
      hB' (Or.inr (ne_top_of_le_ne_top hKF (hFb _)))
    apply hh.congr'
    filter_upwards [hclim.eventually (Ioi_mem_nhds hM)] with k hk
    simp only [brownianWilliamsAverageTest,Set.indicator_apply,Set.mem_ofPred_eq,cs] at hk ⊢
    rw [ite_eq_left hk]
    rfl
  have hd := tendsto_lintegral_of_dominated_convergence' (fun _ => KF*KG)
    (fun k => aemeasurable_averageTest P hB ν hν (xs k) F G hF.measurable hG.measurable μ)
    (fun k => ae_of_all _ (hbound k)) hfin hconv
  have hout (k : ℕ) : (∫⁻ z, brownianWilliamsAverageTest ν (xs k) F G z ∂μ.prod P) =
      ∫⁻ u in Ico (0 : ℝ) 1, ∫⁻ p, brownianWilliamsAverageTest ν (xs k) F G (u,p) ∂P :=
    lintegral_prod _ (aemeasurable_averageTest P hB ν hν (xs k) F G hF.measurable hG.measurable μ)
  have htout : (∫⁻ z, T z.2 ∂μ.prod P) = ∫⁻ p, T p ∂P := by
    rw [lintegral_prod_symm _ hT.comp_snd]
    simp only [lintegral_const,hμ,mul_one]
  simpa only [hout,htout] using hd

private theorem maximum_reference_lintegral (ν : ℝ) (hν : 0 < ν)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ m, H m ∂brownianMaximumReferenceLaw ν) =
      ENNReal.ofReal (2*ν)*(∫⁻ m in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-2*ν*m))*H m) := by
  have hd : Measurable (fun m : ℝ => ENNReal.ofReal
      (if 0 < m then 2*ν*Real.exp (-2*ν*m) else 0)) := by
    have hm : Measurable (fun m : ℝ => 2*ν*Real.exp (-2*ν*m)) := by fun_prop
    exact (hm.ite (measurableSet_lt measurable_const measurable_id) measurable_const).ennreal_ofReal
  rw [brownianMaximumReferenceLaw,lintegral_withDensity_eq_lintegral_mul _ hd hH]
  have he : (fun m : ℝ => ENNReal.ofReal (if 0 < m then 2*ν*Real.exp (-2*ν*m) else 0)*H m) =
      (Ioi (0 : ℝ)).indicator (fun m => ENNReal.ofReal (2*ν)*(ENNReal.ofReal (Real.exp (-2*ν*m))*H m)) := by
    funext m
    by_cases hm : 0 < m
    · rw [ite_eq_left hm,ENNReal.ofReal_mul (by positivity : 0 ≤ 2*ν),
        Set.indicator_of_mem (show m ∈ Ioi (0 : ℝ) from hm)]
      ring
    · simp only [hm,ite_false,ENNReal.ofReal_zero,zero_mul,
        Set.indicator_of_notMem (show m ∉ Ioi (0 : ℝ) from hm)]
  change (∫⁻ m, ENNReal.ofReal (if 0 < m then 2*ν*Real.exp (-2*ν*m) else 0)*H m) = _
  rw [he,lintegral_indicator measurableSet_Ioi]
  have hprod : Measurable (fun m : ℝ => ENNReal.ofReal (Real.exp (-2*ν*m))*H m) := by fun_prop
  rw [lintegral_const_mul _ hprod]

/-- The source factorization holds for bounded continuous prefix and finite future tests. -/
theorem brownianPath_williams_continuous_cylinder_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Continuous F)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (φ : (Fin n → ℝ) → ℝ≥0∞) (hφ : Continuous φ)
    (KF KG : ℝ≥0∞) (hKF : KF ≠ ∞) (hKG : KG ≠ ∞)
    (hFb : ∀ z, F z ≤ KF) (hGb : ∀ ys, φ ys ≤ KG) :
    (∫⁻ p, F (driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p)*
        φ (fun i => brownianPostMaximumPath ν p (brownianFirstHitTimes n ds i)) ∂P) =
      (∫⁻ m, ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P ∂brownianMaximumReferenceLaw ν)*
        (∫⁻ q, φ (fun i => q (brownianFirstHitTimes n ds i)) ∂Q) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := hQ.2.1
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  let K : ℝ → ℝ≥0∞ := fun m => ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P
  have hK : Measurable K :=
    (hF.measurable.comp (measurable_fst.prodMk (measurable_positiveDriftFirstHitSegment_joint ν))).lintegral_prod_right'
  have hKbound (m : ℝ) : K m ≤ KF := by
    calc
      _ ≤ ∫⁻ p : BrownianPath, KF ∂P := lintegral_mono (fun p => hFb _)
      _ = KF := by rw [lintegral_const,measure_univ,mul_one]
  let L : ℝ≥0∞ := ∫⁻ m in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-2*ν*m))*K m
  have href : (∫⁻ m, K m ∂brownianMaximumReferenceLaw ν) = ENNReal.ofReal (2*ν)*L :=
    maximum_reference_lintegral ν hν K hK
  have htwo : ENNReal.ofReal (2*ν) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hL : L ≠ ∞ := by
    have hrf : (∫⁻ m, K m ∂brownianMaximumReferenceLaw ν) ≠ ∞ :=
      ne_top_of_le_ne_top hKF ((lintegral_mono hKbound).trans_eq (by rw [lintegral_const,measure_univ,mul_one]))
    have he : L = (ENNReal.ofReal (2*ν))⁻¹*(∫⁻ m, K m ∂brownianMaximumReferenceLaw ν) := by
      rw [href,← mul_assoc,ENNReal.inv_mul_cancel htwo ENNReal.ofReal_ne_top,one_mul]
    rw [he]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr htwo) hrf
  let G : BrownianPath → ℝ≥0∞ := fun q => φ (fun i => q (brownianFirstHitTimes n ds i))
  have hG : Continuous G := hφ.comp (continuous_pi (fun i => continuous_eval_const _))
  let xs : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hxs (k : ℕ) : 0 < xs k := one_div_pos.mpr (by positivity)
  have hxlim : Tendsto xs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft := brownianPath_williams_bandAverage_limit P hB ν hν xs hxs hxlim F hF G hG
    KF KG hKF hKG hFb (fun q => hGb _)
  have hJ := brownianBelowConditionedLaw_tendsto_entrance_cylinder P hB ν hν Q hQ xs hxs hxlim
    n ds hds φ hφ KG hKG hGb
  have hJfin : (∫⁻ q, G q ∂Q) ≠ ∞ := ne_top_of_le_ne_top hKG
    ((lintegral_mono (fun q => hGb _)).trans_eq (by rw [lintegral_const,measure_univ,mul_one]))
  have hwithin : Tendsto xs atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hxlim,Filter.Eventually.of_forall hxs⟩
  have hr : Tendsto (fun k => (ENNReal.ofReal (xs k))⁻¹*ENNReal.ofReal (conditionedH ν (xs k)))
      atTop (𝓝 (ENNReal.ofReal (2*ν))) := by
    have hh := ENNReal.tendsto_ofReal ((harmonic_band_ratio_limit ν hν).comp hwithin)
    convert hh using 1
    funext k
    dsimp only [Function.comp_def]
    rw [ENNReal.ofReal_div_of_pos (hxs k),div_eq_mul_inv,mul_comm]
  have hright := ENNReal.Tendsto.mul_const
    (ENNReal.Tendsto.mul hr (Or.inr hJfin) hJ (Or.inr ENNReal.ofReal_ne_top)) (Or.inr hL)
  have he (k : ℕ) := average_integral P hB ν (xs k) hν (hxs k) F G hF.measurable hG.measurable
  have hright' : Tendsto (fun k => ∫⁻ u in Ico (0 : ℝ) 1, ∫⁻ p,
      brownianWilliamsAverageTest ν (xs k) F G (u,p) ∂P) atTop
        (𝓝 (ENNReal.ofReal (2*ν)*(∫⁻ q, G q ∂Q)*L)) := by
    simpa only [he] using hright
  have hh := tendsto_nhds_unique hleft hright'
  calc
    _ = ENNReal.ofReal (2*ν)*(∫⁻ q, G q ∂Q)*L := hh
    _ = _ := by rw [href]; ring

/-- Factorization also holds on every strictly ordered positive absolute schedule. -/
theorem brownianPath_williams_continuous_ordered_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (hF : Continuous F)
    (n : ℕ) (ts : Fin (n+1) → ℝ≥0) (ht0 : ∀ i, 0 < ts i) (hts : StrictMono ts)
    (φ : (Fin (n+1) → ℝ) → ℝ≥0∞) (hφ : Continuous φ)
    (KF KG : ℝ≥0∞) (hKF : KF ≠ ∞) (hKG : KG ≠ ∞)
    (hFb : ∀ z, F z ≤ KF) (hGb : ∀ ys, φ ys ≤ KG) :
    (∫⁻ p, F (driftedBrownianMaximum ν p,brownianPreMaximumSegment ν p)*
        φ (fun i => brownianPostMaximumPath ν p (ts i)) ∂P) =
      (∫⁻ m, ∫⁻ p, F (m,positiveDriftFirstHitSegment ν m p) ∂P ∂brownianMaximumReferenceLaw ν)*
        (∫⁻ q, φ (fun i => q (ts i)) ∂Q) := by
  have hh := brownianPath_williams_continuous_cylinder_lintegral P hB ν hν Q hQ F hF
    (n+1) (brownianFirstHitElapsed (n+1) ts)
    (brownianFirstHitElapsed_pos (n+1) ts ht0 hts) φ hφ KF KG hKF hKG hFb hGb
  simpa only [brownianFirstHitTimes_elapsed n ts hts.monotone] using hh

end DOZZ.Proofs
