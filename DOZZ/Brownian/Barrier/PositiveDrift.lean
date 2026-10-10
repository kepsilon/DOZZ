/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.GaussianTilting
public import DOZZ.Brownian.BarrierKernelBounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Weighted first-hit reflection and positive-drift barriers

Reflection after the capped first hit preserves every measurable endpoint test
on the preterminal-hit event. Applying this symmetry to an endpoint below the
barrier identifies its killed mass with the reflected Gaussian upper tail.

The running maximum has no positive atom, and the terminal Gaussian has no
atoms at a positive horizon. Consequently, survival agrees almost everywhere
with the lower endpoint event minus the preterminal first-hit event.
This yields the signed endpoint integral before any estimate is applied.

The scalar Gaussian density and Lebesgue reflection turn the signed integral
into a single killed-density difference. Finite-horizon Gaussian tilting then
supplies the exact weighted density of a drifted barrier event.

The analytic kernel bound keeps the cancellation in that difference. Its
one-sided exponential first moment gives the inverse square drift factor;
the Gaussian normalization gives the horizon to the power three halves.

The final proof of `DOZZ.brownian_positiveDrift_barrier_bound` transports the
canonical estimate to an arbitrary Brownian sample space using one common
almost-everywhere continuous-path event. No additional measurability premise
is imposed on the statement.

The endpoint expectation identity is exported separately for the later
infinite-horizon maximum calculation. All equalities here concern the actual
path events and measures, rather than a separately specified kernel model.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- First-hit reflection preserves every measurable endpoint test on the event of a preterminal hit. -/
theorem brownianPath_firstHit_endpoint_setIntegral_symmetry (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β) (T : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ p in {p | cappedBrownianFirstPassage β T p < T}, F (p T) ∂P) =
      ∫ p in {p | cappedBrownianFirstPassage β T p < T}, F (2*β-p T) ∂P := by
  let τ := cappedBrownianFirstPassage β T
  have hτ := cappedBrownianFirstPassage_isStoppingTime β T
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  let H : Set BrownianPath := {p | τ p < T}
  have hH : MeasurableSet H := measurableSet_lt hmτ measurable_const
  let S : Set (ℝ≥0 × BrownianPath) := {z | z.1 < T}
  have hS : MeasurableSet S := measurableSet_lt measurable_fst measurable_const
  let G : ℝ≥0 × BrownianPath → ℝ := S.indicator (fun z => F (β+z.2 (T-z.1)))
  have hmG : Measurable G :=
    (hF.comp (measurable_const.add (measurable_brownianPath_evaluation.comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)))).indicator hS
  have hlaw := brownianPath_bounded_restart_joint_neg P hB τ hτ T
    (cappedBrownianFirstPassage_le β T) τ (measurable_finite_stoppingTime_stopped _ τ hτ)
  have hi : (∫ p, G (τ p,brownianShiftPath (τ p) p) ∂P) =
      ∫ p, G (τ p,-brownianShiftPath (τ p) p) ∂P := by
    calc
      _ = ∫ z, G z ∂P.map (fun p => (τ p,brownianShiftPath (τ p) p)) :=
        (integral_map (hmτ.prodMk hmV).aemeasurable hmG.aestronglyMeasurable).symm
      _ = ∫ z, G z ∂P.map (fun p => (τ p,-brownianShiftPath (τ p) p)) := by rw [hlaw]
      _ = _ := integral_map
        (show Measurable (fun p => (τ p,-brownianShiftPath (τ p) p)) from hmτ.prodMk hmV.neg).aemeasurable
        hmG.aestronglyMeasurable
  rw [← integral_indicator hH,← integral_indicator hH]
  have hup : (fun p => G (τ p,brownianShiftPath (τ p) p)) =ᵐ[P] H.indicator (fun p => F (p T)) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    by_cases hτT : τ p < T
    · have hp0 : p 0 < β := hp ▸ hβ
      have hv := cappedBrownianFirstPassage_value β T p hp0 hτT
      simp only [G,S,H,Set.indicator_apply,mem_ofPred_eq,ite_eq_left hτT]
      change F (β+(p (τ p+(T-τ p))-p (τ p))) = F (p T)
      rw [add_tsub_cancel_of_le (cappedBrownianFirstPassage_le β T p),hv]
      congr 1
      ring_nf
    · simp only [G,S,H,Set.indicator_apply,mem_ofPred_eq,ite_eq_right hτT]
  have hlo : (fun p => G (τ p,-brownianShiftPath (τ p) p)) =ᵐ[P]
      H.indicator (fun p => F (2*β-p T)) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    by_cases hτT : τ p < T
    · have hp0 : p 0 < β := hp ▸ hβ
      have hv := cappedBrownianFirstPassage_value β T p hp0 hτT
      simp only [G,S,H,Set.indicator_apply,mem_ofPred_eq,ite_eq_left hτT]
      change F (β+-(p (τ p+(T-τ p))-p (τ p))) = F (2*β-p T)
      rw [add_tsub_cancel_of_le (cappedBrownianFirstPassage_le β T p),hv]
      congr 1
      ring_nf
    · simp only [G,S,H,Set.indicator_apply,mem_ofPred_eq,ite_eq_right hτT]
  exact (integral_congr_ae hup).symm.trans (hi.trans (integral_congr_ae hlo))
/-- Reflect the endpoint below the barrier onto the terminal Gaussian upper tail. -/
theorem brownianPath_firstHit_endpoint_below_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β) (T : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ p in {p | cappedBrownianFirstPassage β T p < T} ∩ {p | p T < β}, F (p T) ∂P) =
      ∫ p in {p | β < p T}, F (2*β-p T) ∂P := by
  let H : Set BrownianPath := {p | cappedBrownianFirstPassage β T p < T}
  let L : Set BrownianPath := {p | p T < β}
  let U : Set BrownianPath := {p | β < p T}
  have hL : MeasurableSet L := measurableSet_lt (ContinuousMap.measurable_eval T) measurable_const
  have hU : MeasurableSet U := measurableSet_lt measurable_const (ContinuousMap.measurable_eval T)
  have hI : MeasurableSet (Iio β) := measurableSet_Iio
  have hs := brownianPath_firstHit_endpoint_setIntegral_symmetry P hB β hβ T
    ((Iio β).indicator F) (hF.indicator hI)
  have hl : (fun p : BrownianPath => (Iio β).indicator F (p T)) = L.indicator (fun p => F (p T)) := by
    funext p
    simp only [L, Set.indicator_apply, mem_Iio, mem_ofPred_eq]
  have hu : (fun p : BrownianPath => (Iio β).indicator F (2*β-p T)) =
      U.indicator (fun p => F (2*β-p T)) := by
    funext p
    have he : 2*β-p T < β ↔ β < p T := by constructor <;> intro h <;> linarith
    simp only [U, Set.indicator_apply, mem_Iio, mem_ofPred_eq, he]
  rw [hl, hu, setIntegral_indicator hL, setIntegral_indicator hU] at hs
  have he : H ∩ U =ᵐ[P] U := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    apply propext
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨cappedBrownianFirstPassage_lt_of_terminal β T p (hp ▸ hβ) h, h⟩
  exact hs.trans (setIntegral_congr_set he)
/-- Up to Brownian null sets, survival is the lower endpoint event minus a first hit. -/
theorem brownianPath_barrier_ae_endpoint_sdiff_firstHit (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} =ᵐ[P]
      {p | p T < β} \ {p | cappedBrownianFirstPassage β T p < T} := by
  have hn : ∀ᵐ p ∂P, (⨆ u : Iic T, p u) ≠ β := by
    rw [ae_iff]
    simpa only [not_not] using brownianPath_runningMaximum_atom_zero P hB β hβ T hT
  filter_upwards [hn,brownianPath_crossing_ae_firstHit P hB β hβ T hT] with p hp hc
  have hce : (∃ u ≤ T, β ≤ p u) ↔ cappedBrownianFirstPassage β T p < T :=
    Iff.of_eq hc
  apply propext
  change (∀ u : ℝ≥0, u ≤ T → p u ≤ β) ↔ p T < β ∧ ¬cappedBrownianFirstPassage β T p < T
  constructor
  · intro h
    have hmax : (⨆ u : Iic T, p u) < β :=
      lt_of_le_of_ne ((brownianPath_barrier_iff_runningMaximum p T β).mp h) hp
    refine ⟨(le_ciSup (brownianPath_Iic_bddAbove p T) ⟨T,le_rfl⟩).trans_lt hmax,?_⟩
    intro hh
    obtain ⟨u,hu,hβu⟩ := hce.mpr hh
    exact (hβu.trans (le_ciSup (brownianPath_Iic_bddAbove p T) ⟨u,hu⟩)).not_gt hmax
  · rintro ⟨_,hh⟩ u hu
    by_contra hb
    exact hh (hce.mp ⟨u,hu,(lt_of_not_ge hb).le⟩)

/-- Weighted survival is the lower Gaussian endpoint integral minus its reflected upper tail. -/
theorem brownianPath_barrier_endpoint_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) (F : ℝ → ℝ) (hF : Measurable F)
    (hInt : Integrable (fun p => F (p T)) P) :
    (∫ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}, F (p T) ∂P) =
      (∫ p in {p | p T < β}, F (p T) ∂P) - ∫ p in {p | β < p T}, F (2*β-p T) ∂P := by
  have hmτ := measurable_finite_brownian_stoppingTime _ _ (cappedBrownianFirstPassage_isStoppingTime β T)
  have hH := measurableSet_lt hmτ (measurable_const (a := T))
  rw [setIntegral_congr_set (brownianPath_barrier_ae_endpoint_sdiff_firstHit P hB β hβ T hT)]
  have he : {p : BrownianPath | p T < β} \ {p | cappedBrownianFirstPassage β T p < T} =
      {p | p T < β} \ ({p | cappedBrownianFirstPassage β T p < T} ∩ {p | p T < β}) := by
    ext p
    simp only [Set.mem_sdiff,mem_inter_iff,mem_ofPred_eq]
    tauto
  rw [he,setIntegral_sdiff (hH.inter (measurableSet_lt (ContinuousMap.measurable_eval T) measurable_const))
    hInt.integrableOn inter_subset_right,
    brownianPath_firstHit_endpoint_below_integral P hB β hβ T F hF]
/-- A continuous Brownian terminal test over an endpoint set is its Gaussian set integral. -/
theorem brownianPath_endpoint_setIntegral (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (T : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S) (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ p in {p | p T ∈ S}, F (p T) ∂P) = ∫ x in S, F x ∂gaussianReal 0 T := by
  rw [← (hB.hasLaw_eval T).map_eq]
  exact (setIntegral_map hS hF.aestronglyMeasurable (ContinuousMap.measurable_eval T).aemeasurable).symm

/-- Real Gaussian set integrals use the literal scalar density. -/
theorem gaussianReal_setIntegral_pdf (T : ℝ≥0) (hT : T ≠ 0)
    (S : Set ℝ) (hS : MeasurableSet S) (F : ℝ → ℝ) :
    (∫ x in S, F x ∂gaussianReal 0 T) = ∫ x in S, gaussianPDFReal 0 T x * F x := by
  rw [gaussianReal_of_var_ne_zero 0 hT,
    setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF 0 T)
      (ae_of_all _ (fun x => gaussianPDF_lt_top (μ := 0) (v := T) (x := x))) F hS]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul]

/-- Gaussian integrability is precisely integrability against its scalar density. -/
theorem gaussianReal_integrable_pdf (T : ℝ≥0) (hT : T ≠ 0) (F : ℝ → ℝ)
    (hF : Integrable F (gaussianReal 0 T)) : Integrable (fun x => gaussianPDFReal 0 T x*F x) := by
  rw [gaussianReal_of_var_ne_zero 0 hT] at hF
  have hi := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 T)
    (ae_of_all _ (fun x => gaussianPDF_lt_top (μ := 0) (v := T) (x := x)))).mp hF
  simpa only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] using hi

/-- Reflection around a real level exchanges the two open endpoint half lines. -/
theorem integral_reflection_Ioi (β : ℝ) (F : ℝ → ℝ) :
    (∫ x in Ioi β, F (2*β-x)) = ∫ x in Iio β, F x := by
  have hp : (fun x : ℝ => 2*β-x) ⁻¹' Iio β = Ioi β := by
    ext x
    simp only [mem_preimage,mem_Iio,mem_Ioi]
    constructor <;> intro h <;> linarith
  simpa only [hp] using (volume.measurePreserving_sub_left (2*β)).setIntegral_preimage_emb
    (Homeomorph.subLeft (2*β)).measurableEmbedding F (Iio β)

/-- Reflection also transports integrability on either endpoint half line. -/
theorem integrableOn_reflection_Ioi_iff (β : ℝ) (F : ℝ → ℝ) :
    IntegrableOn (fun x => F (2*β-x)) (Ioi β) ↔ IntegrableOn F (Iio β) := by
  have hp : (fun x : ℝ => 2*β-x) ⁻¹' Iio β = Ioi β := by
    ext x
    simp only [mem_preimage,mem_Iio,mem_Ioi]
    constructor <;> intro h <;> linarith
  simpa only [hp,Function.comp_def] using
    (volume.measurePreserving_sub_left (2*β)).integrableOn_comp_preimage
      (Homeomorph.subLeft (2*β)).measurableEmbedding (f := F) (s := Iio β)

/-- The killed Brownian endpoint integral retains the full reflected density difference. -/
theorem brownianPath_barrier_killedDensity_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) (F : ℝ → ℝ) (hF : Measurable F)
    (hInt : Integrable F (gaussianReal 0 T))
    (hIntR : Integrable (fun x => F (2*β-x)) (gaussianReal 0 T)) :
    (∫ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}, F (p T) ∂P) =
      ∫ x in Iio β, (gaussianPDFReal 0 T x-gaussianPDFReal 0 T (2*β-x))*F x := by
  have hIntP : Integrable (fun p => F (p T)) P := by
    simpa only [Function.comp_def] using (hB.hasLaw_eval T).integrable_comp hInt
  rw [brownianPath_barrier_endpoint_integral P hB β hβ T hT F hF hIntP]
  change (∫ p in {p | p T ∈ Iio β}, F (p T) ∂P) -
    (∫ p in {p | p T ∈ Ioi β}, F (2*β-p T) ∂P) = _
  rw [brownianPath_endpoint_setIntegral P hB.toIsPreBrownianReal T (Iio β) measurableSet_Iio F hF,
    brownianPath_endpoint_setIntegral P hB.toIsPreBrownianReal T (Ioi β) measurableSet_Ioi
      (fun x => F (2*β-x)) (hF.comp (measurable_const.sub measurable_id)),
    gaussianReal_setIntegral_pdf T hT (Iio β) measurableSet_Iio F,
    gaussianReal_setIntegral_pdf T hT (Ioi β) measurableSet_Ioi (fun x => F (2*β-x))]
  have hr : (fun x => gaussianPDFReal 0 T x*F (2*β-x)) =
      (fun x => (gaussianPDFReal 0 T (2*β-x)*F x)) ∘ (fun x => 2*β-x) := by
    funext x
    have he : 2*β-(2*β-x) = x := by ring_nf
    simp only [Function.comp_def,he]
  have hiR := (integrableOn_reflection_Ioi_iff β (fun x => gaussianPDFReal 0 T (2*β-x)*F x)).mp
    (by simpa only [Function.comp_def] using
      (show IntegrableOn ((fun x => gaussianPDFReal 0 T (2*β-x)*F x) ∘ (fun x => 2*β-x)) (Ioi β) from
        hr ▸ (gaussianReal_integrable_pdf T hT _ hIntR).integrableOn))
  rw [hr,show (∫ x in Ioi β, ((fun x => gaussianPDFReal 0 T (2*β-x)*F x) ∘ (fun x => 2*β-x)) x) =
      ∫ x in Iio β, gaussianPDFReal 0 T (2*β-x)*F x by simpa only [Function.comp_def] using integral_reflection_Ioi β (fun x => gaussianPDFReal 0 T (2*β-x)*F x),
    ← integral_sub (gaussianReal_integrable_pdf T hT F hInt).integrableOn hiR]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp; ring)
/-- The endpoint distance from the barrier parametrizes the positive half line. -/
theorem integral_barrier_distance (β : ℝ) (F : ℝ → ℝ) :
    (∫ y in Ioi (0 : ℝ), F (β-y)) = ∫ x in Iio β, F x := by
  have hp : (fun y : ℝ => β-y) ⁻¹' Iio β = Ioi (0 : ℝ) := by
    ext y
    simp only [mem_preimage,mem_Iio,mem_Ioi]
    constructor <;> intro h <;> linarith
  simpa only [hp] using (volume.measurePreserving_sub_left β).setIntegral_preimage_emb
    (Homeomorph.subLeft β).measurableEmbedding F (Iio β)

/-- The terminal likelihood is integrable under any scalar Gaussian law. -/
theorem integrable_real_brownianGaussianLikelihood (a : ℝ) (T : ℝ≥0) :
    Integrable (fun x => Real.exp (a*x-a^2*(T : ℝ)/2)) (gaussianReal 0 T) := by
  have he : (fun x : ℝ => Real.exp (a*x-a^2*(T : ℝ)/2)) =
      fun x => Real.exp (a*x)*Real.exp (-(a^2*(T : ℝ)/2)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
  rw [he]
  exact (integrable_exp_mul_gaussianReal a).mul_const _

/-- The reflected terminal likelihood is also genuinely Gaussian-integrable. -/
theorem integrable_real_brownianGaussianLikelihood_reflected (a β : ℝ) (T : ℝ≥0) :
    Integrable (fun x => Real.exp (a*(2*β-x)-a^2*(T : ℝ)/2)) (gaussianReal 0 T) := by
  have he : (fun x : ℝ => Real.exp (a*(2*β-x)-a^2*(T : ℝ)/2)) =
      fun x => Real.exp ((-a)*x)*Real.exp (2*a*β-a^2*(T : ℝ)/2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  exact (integrable_exp_mul_gaussianReal (-a)).mul_const _

/-- A drifted Brownian barrier has the exact exponentially weighted killed Gaussian integral. -/
theorem brownianPath_drift_barrier_killedDensity (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹*Real.exp (a*β-a^2*(T : ℝ)/2)*
        ∫ y in Ioi (0 : ℝ), Real.exp (-a*y)*
          (Real.exp (-((y-β)^2/(2*(T : ℝ))))-Real.exp (-((y+β)^2/(2*(T : ℝ)))))) := by
  let F : ℝ → ℝ := fun x => Real.exp (a*x-a^2*(T : ℝ)/2)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hInt := integrable_real_brownianGaussianLikelihood a T
  have hIntP : Integrable (fun p => F (p T)) P := by
    simpa only [Function.comp_def] using (hB.hasLaw_eval T).integrable_comp hInt
  rw [brownian_drift_barrier_probability_likelihood P hB.toIsPreBrownianReal a β T hT]
  change (∫⁻ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}, ENNReal.ofReal (F (p T)) ∂P) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hIntP.integrableOn (ae_of_all _ (fun p => (Real.exp_pos _).le)),
    brownianPath_barrier_killedDensity_integral P hB β hβ T hT F hF hInt
      (integrable_real_brownianGaussianLikelihood_reflected a β T),
    ← integral_barrier_distance β]
  congr 1
  have he : (fun y : ℝ => (gaussianPDFReal 0 T (β-y)-gaussianPDFReal 0 T (2*β-(β-y)))*F (β-y)) =
      fun y => ((Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹*Real.exp (a*β-a^2*(T : ℝ)/2))*
        (Real.exp (-a*y)*(Real.exp (-((y-β)^2/(2*(T : ℝ))))-Real.exp (-((y+β)^2/(2*(T : ℝ)))))) := by
    funext y
    have hsq : (β-y)^2 = (y-β)^2 := by ring_nf
    have hr : 2*β-(β-y) = y+β := by ring_nf
    have hExp : Real.exp (a*(β-y)-a^2*(T : ℝ)/2) =
        Real.exp (a*β-a^2*(T : ℝ)/2)*Real.exp (-a*y) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    simp only [gaussianPDFReal,sub_zero,F,hsq,hr,hExp]
    ring_nf
  rw [he,integral_const_mul]
/-- The two reflected endpoint integrals are the real expectation of drifted survival. -/
theorem brownianPath_drift_barrier_endpoint_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} =
      ENNReal.ofReal ((∫ x in Iio β, Real.exp (a*x-a^2*(T : ℝ)/2) ∂gaussianReal 0 T) -
        ∫ x in Ioi β, Real.exp (a*(2*β-x)-a^2*(T : ℝ)/2) ∂gaussianReal 0 T) := by
  let F : ℝ → ℝ := fun x => Real.exp (a*x-a^2*(T : ℝ)/2)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hiP : Integrable (fun p => F (p T)) P := by
    simpa only [Function.comp_def] using (hB.hasLaw_eval T).integrable_comp
      (integrable_real_brownianGaussianLikelihood a T)
  rw [brownian_drift_barrier_probability_likelihood P hB.toIsPreBrownianReal a β T hT]
  change (∫⁻ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}, ENNReal.ofReal (F (p T)) ∂P) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hiP.integrableOn (ae_of_all _ (fun p => (Real.exp_pos _).le)),
    brownianPath_barrier_endpoint_integral P hB β hβ T hT F hF hiP]
  congr 1
  change (∫ p in {p | p T ∈ Iio β}, F (p T) ∂P) -
    (∫ p in {p | p T ∈ Ioi β}, F (2*β-p T) ∂P) = _
  rw [brownianPath_endpoint_setIntegral P hB.toIsPreBrownianReal T (Iio β) measurableSet_Iio F hF,
    brownianPath_endpoint_setIntegral P hB.toIsPreBrownianReal T (Ioi β) measurableSet_Ioi
      (fun x => F (2*β-x)) (hF.comp (measurable_const.sub measurable_id))]

/-- Normalize the analytic reflected-kernel estimate to the finite-horizon coefficient of
`DOZZ.brownian_positiveDrift_barrier_bound`. -/
theorem brownian_positiveDrift_normalization (a β t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    (Real.sqrt (2*Real.pi*t))⁻¹*Real.exp (a*β-a^2*t/2)*(2*β/t*a⁻¹^(2 : ℝ)) =
      Real.sqrt (2/Real.pi)*β*Real.exp (a*β-a^2*t/2)/(a^2*t^(3/2 : ℝ)) := by
  have hp : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hs : Real.sqrt t ≠ 0 := by positivity
  have hpow : t^(3/2 : ℝ) = t*Real.sqrt t := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add ht,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [Real.rpow_two,Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),hpow,← brownian_gaussian_normalization]
  field_simp [ha.ne',ht.ne',hp,hs]

/-- The exact positive-drift estimate on the canonical continuous-path carrier. -/
theorem brownianPath_positiveDrift_barrier_bound (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} ≤
      ENNReal.ofReal (Real.sqrt (2/Real.pi)*β*Real.exp (a*β-a^2*(T : ℝ)/2)/
        (a^2*(T : ℝ)^(3/2 : ℝ))) := by
  have ht : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  rw [brownianPath_drift_barrier_killedDensity P hB a β hβ T hT]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹*Real.exp (a*β-a^2*(T : ℝ)/2)*
        (2*β/(T : ℝ)*a⁻¹^(2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (integral_weightedGaussianKernelDifference_le _ β a ht hβ.le ha) (by positivity)
    _ = _ := brownian_positiveDrift_normalization a β _ ha ht

/-- Proof of `DOZZ.brownian_positiveDrift_barrier_bound`, without extra sample-space measurability
premises. -/
theorem brownian_positiveDrift_barrier_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (α β t : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω + α * u ≤ β} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * β *
        Real.exp (α * β - α ^ 2 * t / 2) / (α ^ 2 * t ^ (3 / 2 : ℝ))) := by
  let T : ℝ≥0 := NNReal.mk t ht.le
  have hT : T ≠ 0 := by
    intro he
    have ht0 : t = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    exact ht.ne' ht0
  let X := brownianContinuousPath B
  have hm : AEMeasurable X P := aemeasurable_brownianContinuousPath hB
  have hS : MeasurableSet {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+α*(u : ℝ) ≤ β} := by
    have hmDrift : Measurable (brownianDriftPath α) :=
      continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_id)
    exact ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
      (measurableSet_brownianPath_barrier T β)).preimage hmDrift
  have he : P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω+α*(u : ℝ) ≤ β} =
      (P.map X) {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+α*(u : ℝ) ≤ β} := by
    rw [Measure.map_apply_of_aemeasurable hm hS]
    apply measure_congr
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    apply propext
    simp only [mem_ofPred_eq,mem_preimage,X,hω]
    rfl
  rw [he]
  exact brownianPath_positiveDrift_barrier_bound _ (brownianContinuousPath_isBrownian hB) α β hα hβ T hT

end DOZZ.Proofs
