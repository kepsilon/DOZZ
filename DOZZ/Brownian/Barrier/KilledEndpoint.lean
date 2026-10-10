/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.Maximum

/-!
# Actual killed endpoint measures

The reflected endpoint expectation identifies the pushforward of the actual
surviving Brownian paths with a Lebesgue density. Its nonnegativity and
integrability are proved before the measure identity is used.

Gaussian tilting gives the same identification with arbitrary real drift.
Reflection and translation give the killed transition kernel on the positive
half line, for either sign of drift and every positive initial state.

The resulting kernel is measurable, nonnegative and has at most unit mass.
Every measurable nonnegative endpoint test inherits the exact integral formula.
The argument also identifies strict and closed barriers almost everywhere by
excluding the positive-level finite-maximum atom.

Exchanging the two states and reversing the drift transposes the kernel. This
is the scalar cancellation used by the ceiling-grid first-hit reversal proof.
The actual multi-time killed Markov factorization and lifetime-marked reversal
are later steps; neither is inferred merely from the scalar kernel identity.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- The reflected scalar endpoint density for survival below a positive barrier. -/
noncomputable def brownianUpperKilledPDFReal (β : ℝ) (T : ℝ≥0) : ℝ → ℝ :=
  (Iio β).indicator (fun x => gaussianPDFReal 0 T x-gaussianPDFReal 0 T (2*β-x))

/-- The literal reflected density is measurable. -/
theorem measurable_brownianUpperKilledPDFReal (β : ℝ) (T : ℝ≥0) :
    Measurable (brownianUpperKilledPDFReal β T) := by
  unfold brownianUpperKilledPDFReal
  apply Measurable.indicator _ measurableSet_Iio
  fun_prop

/-- The reflected upper-barrier density is nonnegative. -/
theorem brownianUpperKilledPDFReal_nonneg (β : ℝ) (hβ : 0 < β) (T : ℝ≥0) (hT : T ≠ 0) (x : ℝ) :
    0 ≤ brownianUpperKilledPDFReal β T x := by
  classical
  by_cases hx : x < β
  · have ht : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
    have hd := gaussianKernelDifference_nonneg (T : ℝ) (β-x) β ht (sub_nonneg.mpr hx.le) hβ.le
    have hsq : (β-x-β)^2 = x^2 := by ring_nf
    have hr : β-x+β = 2*β-x := by ring_nf
    simp only [hsq,hr] at hd
    simp only [brownianUpperKilledPDFReal,Set.indicator_apply,mem_Iio,ite_eq_left hx,gaussianPDFReal,sub_zero]
    have hm := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (2*Real.pi*(T : ℝ)))) hd
    simpa only [mul_sub,neg_div] using hm
  · simp only [brownianUpperKilledPDFReal,Set.indicator_apply,mem_Iio,ite_eq_right hx,le_refl]

/-- The killed density is pointwise dominated by the original Gaussian endpoint density. -/
theorem brownianUpperKilledPDFReal_le (β : ℝ) (T : ℝ≥0) (x : ℝ) :
    brownianUpperKilledPDFReal β T x ≤ gaussianPDFReal 0 T x := by
  classical
  by_cases hx : x < β
  · simp only [brownianUpperKilledPDFReal,Set.indicator_apply,mem_Iio,ite_eq_left hx]
    exact sub_le_self _ (gaussianPDFReal_nonneg _ _ _)
  · simp only [brownianUpperKilledPDFReal,Set.indicator_apply,mem_Iio,ite_eq_right hx]
    exact gaussianPDFReal_nonneg _ _ _

/-- The reflected endpoint difference is genuinely Lebesgue-integrable. -/
theorem integrable_brownianUpperKilledPDFReal (β : ℝ) (hβ : 0 < β) (T : ℝ≥0) (hT : T ≠ 0) :
    Integrable (brownianUpperKilledPDFReal β T) := by
  apply (integrable_gaussianPDFReal 0 T).mono' (measurable_brownianUpperKilledPDFReal β T).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (brownianUpperKilledPDFReal_nonneg β hβ T hT x)]
    exact brownianUpperKilledPDFReal_le β T x)

/-- The actual surviving Brownian endpoint measure is the reflected Gaussian density. -/
theorem brownianPath_barrier_endpoint_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}).map (fun p => p T) =
      volume.withDensity (fun x => ENNReal.ofReal (brownianUpperKilledPDFReal β T x)) := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}
  apply Measure.ext
  intro S hS
  let F : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hF : Measurable F := measurable_const.indicator hS
  have hiF : Integrable F (gaussianReal 0 T) := (integrable_const (1 : ℝ)).indicator hS
  have hiR : Integrable (fun x => F (2*β-x)) (gaussianReal 0 T) := by
    have he : (fun x => F (2*β-x)) = ((fun x : ℝ => 2*β-x) ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
      funext x
      simp only [F,Set.indicator_apply,mem_preimage]
    rw [he]
    exact (integrable_const (1 : ℝ)).indicator (hS.preimage (measurable_const.sub measurable_id))
  have hk := brownianPath_barrier_killedDensity_integral P hB β hβ T hT F hF hiF hiR
  have hleft : ENNReal.ofReal (∫ p in A, F (p T) ∂P) = (P.restrict A).map (fun p => p T) S := by
    have he : (fun p : BrownianPath => F (p T)) = ((fun p : BrownianPath => p T) ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
      funext p
      simp only [F,Set.indicator_apply,mem_preimage]
    rw [he,setIntegral_indicator (hS.preimage (ContinuousMap.measurable_eval T)),integral_const]
    simp only [smul_eq_mul,mul_one]
    rw [Measure.map_apply (ContinuousMap.measurable_eval T) hS,
      Measure.restrict_apply (hS.preimage (ContinuousMap.measurable_eval T)),inter_comm]
    rw [Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hright : (∫ x in Iio β, (gaussianPDFReal 0 T x-gaussianPDFReal 0 T (2*β-x))*F x) =
      ∫ x in S, brownianUpperKilledPDFReal β T x := by
    rw [← integral_indicator measurableSet_Iio,← integral_indicator hS]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases h1 : x < β <;> by_cases h2 : x ∈ S <;>
      simp only [F,brownianUpperKilledPDFReal,Set.indicator_apply,mem_Iio,
        h1,h2,ite_true,ite_false,mul_one,mul_zero]
  rw [← hleft, hk,hright,withDensity_apply _ hS,← ofReal_integral_eq_lintegral_ofReal
    (integrable_brownianUpperKilledPDFReal β hβ T hT).integrableOn
    (ae_of_all _ (brownianUpperKilledPDFReal_nonneg β hβ T hT))]
/-- Drifted barrier events are measurable on the actual continuous-path carrier. -/
theorem measurableSet_brownianPath_drift_barrier (a β : ℝ) (T : ℝ≥0) :
    MeasurableSet {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} := by
  have hm : Measurable (brownianDriftPath a) :=
    continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_id)
  exact ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
    (measurableSet_brownianPath_barrier T β)).preimage hm

/-- Gaussian tilting identifies the surviving drifted endpoint measure with the original surviving tilted measure. -/
theorem brownianPath_drift_barrier_endpoint_map_eq_tilt (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a β : ℝ)
    (T : ℝ≥0) (hT : T ≠ 0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β}).map
      (fun p => p T+a*(T : ℝ)) =
      ((brownianFiniteTilt P a T).restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}).map (fun p => p T) := by
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}
  have hA : MeasurableSet A := ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
    (measurableSet_brownianPath_barrier T β))
  have hmStop := measurable_stopBrownianPath_fixed T
  have hmDrift : Measurable (driftedBrownianPath a) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  apply Measure.ext
  intro S hS
  let E : Set BrownianPath := (fun p : BrownianPath => p T) ⁻¹' S ∩ A
  have hE : MeasurableSet E := (hS.preimage (ContinuousMap.measurable_eval T)).inter hA
  have hmap := congrArg (fun μ : Measure BrownianPath => μ E)
    (brownianFiniteTilt_stoppedPath_map P hB a T hT)
  rw [Measure.map_apply hmStop hE,
    Measure.map_apply (show Measurable (fun p => stopBrownianPath (driftedBrownianPath a p) T) from hmStop.comp hmDrift) hE] at hmap
  have hzero : (fun p : BrownianPath => stopBrownianPath p T) ⁻¹' E = (fun p => p T) ⁻¹' S ∩ A := by
    ext p
    change stopBrownianPath p T T ∈ S ∧ (∀ u : ℝ≥0, u ≤ T → stopBrownianPath p T u ≤ β) ↔ _
    rw [stopBrownianPath_barrier_iff]
    change p (min T T) ∈ S ∧ (∀ u : ℝ≥0, u ≤ T → p u ≤ β) ↔ _
    rw [min_self]
    rfl
  have hdrift : (fun p : BrownianPath => stopBrownianPath (driftedBrownianPath a p) T) ⁻¹' E =
      (fun p => p T+a*(T : ℝ)) ⁻¹' S ∩ {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} := by
    ext p
    change stopBrownianPath (driftedBrownianPath a p) T T ∈ S ∧
      (∀ u : ℝ≥0, u ≤ T → stopBrownianPath (driftedBrownianPath a p) T u ≤ β) ↔ _
    rw [stopBrownianPath_barrier_iff]
    change p (min T T)+a*((min T T : ℝ≥0) : ℝ) ∈ S ∧ _ ↔ _
    rw [min_self]
    rfl
  rw [hzero,hdrift] at hmap
  rw [Measure.map_apply
      (show Measurable (fun p : BrownianPath => p T+a*(T : ℝ)) from (ContinuousMap.measurable_eval T).add measurable_const) hS,
    Measure.map_apply (ContinuousMap.measurable_eval T) hS,
    Measure.restrict_apply (hS.preimage (show Measurable (fun p : BrownianPath => p T+a*(T : ℝ)) from
      (ContinuousMap.measurable_eval T).add measurable_const)),
    Measure.restrict_apply (hS.preimage (ContinuousMap.measurable_eval T))]
  exact hmap.symm

/-- The actual endpoint of a surviving drifted path has the likelihood-weighted reflected density. -/
theorem brownianPath_drift_barrier_endpoint_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β}).map
      (fun p => p T+a*(T : ℝ)) =
      volume.withDensity (fun x => ENNReal.ofReal (brownianUpperKilledPDFReal β T x)*brownianGaussianLikelihood a T x) := by
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}
  have hA : MeasurableSet A := ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
    (measurableSet_brownianPath_barrier T β))
  rw [brownianPath_drift_barrier_endpoint_map_eq_tilt P hB.toIsPreBrownianReal a β T hT,
    brownianFiniteTilt,restrict_withDensity hA,
    brownian_map_withDensity_comp (P.restrict A) _ (ContinuousMap.measurable_eval T)
      (brownianGaussianLikelihood a T) (measurable_brownianGaussianLikelihood a T),
    brownianPath_barrier_endpoint_map P hB β hβ T hT,
    ← withDensity_mul volume (measurable_brownianUpperKilledPDFReal β T).ennreal_ofReal
      (measurable_brownianGaussianLikelihood a T)]
  simp only [Pi.mul_def]
/-- Reflecting a scalar Lebesgue density around a level composes the density with that reflection. -/
theorem brownian_scalar_reflection_withDensity (c : ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (volume.withDensity w).map (fun x => c-x) = volume.withDensity (fun y => w (c-y)) := by
  let f : ℝ → ℝ := fun x => c-x
  have hf : Measurable f := measurable_const.sub measurable_id
  have he : (fun x => w (f (f x))) = w := by
    funext x
    have hx : f (f x) = x := by dsimp [f]; ring_nf
    rw [hx]
  have hmap := brownian_map_withDensity_comp volume f hf (fun y => w (f y)) (hw.comp hf)
  rw [he,(volume.measurePreserving_sub_left c).map_eq] at hmap
  exact hmap

/-- Reflecting the surviving upper endpoint measure gives the actual lower-killed drifted endpoint. -/
theorem brownianPath_lowerKilled_endpoint_map_eq_upper (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (T : ℝ≥0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → 0 ≤ x+p u+a*(u : ℝ)}).map
      (fun p => x+p T+a*(T : ℝ)) =
      ((P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+(-a)*(u : ℝ) ≤ x}).map
        (fun p => p T+(-a)*(T : ℝ))).map (fun y => x-y) := by
  have hUp : MeasurableSet {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+(-a)*(u : ℝ) ≤ x} :=
    measurableSet_brownianPath_drift_barrier (-a) x T
  have hmUp : Measurable (fun p : BrownianPath => p T+(-a)*(T : ℝ)) :=
    (ContinuousMap.measurable_eval T).add measurable_const
  have hmLow : Measurable (fun p : BrownianPath => x+p T+a*(T : ℝ)) :=
    (measurable_const.add (ContinuousMap.measurable_eval T)).add measurable_const
  have hf : Measurable (fun y : ℝ => x-y) := measurable_const.sub measurable_id
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hmLow hS,Measure.restrict_apply (hS.preimage hmLow),
    Measure.map_map hf hmUp,Measure.map_apply (hf.comp hmUp) hS,
    Measure.restrict_apply (hS.preimage (hf.comp hmUp))]
  have hE : MeasurableSet (((fun y : ℝ => x-y) ∘ (fun p : BrownianPath => p T+(-a)*(T : ℝ))) ⁻¹' S ∩
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+(-a)*(u : ℝ) ≤ x}) :=
    (hS.preimage (hf.comp hmUp)).inter hUp
  conv_rhs => rw [← brownianPath_neg_map P hB]
  rw [Measure.map_apply measurable_neg hE]
  congr 1
  ext p
  simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq,Function.comp_def]
  have hv : x-((-p) T+(-a)*(T : ℝ)) = x+p T+a*(T : ℝ) := by
    change x-(-p T+(-a)*(T : ℝ)) = _
    ring_nf
  rw [hv]
  apply and_congr_right
  intro hSx
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro hu
  change (0 ≤ x+p u+a*(u : ℝ)) ↔ (-p u+(-a)*(u : ℝ) ≤ x)
  constructor <;> intro h <;> linarith

/-- The lower-killed drifted Brownian endpoint measure is an actual reflected tilted Gaussian density. -/
theorem brownianPath_lowerKilled_endpoint_map_reflected (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) (hT : T ≠ 0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → 0 ≤ x+p u+a*(u : ℝ)}).map
      (fun p => x+p T+a*(T : ℝ)) =
      volume.withDensity (fun y => ENNReal.ofReal (brownianUpperKilledPDFReal x T (x-y))*brownianGaussianLikelihood (-a) T (x-y)) := by
  rw [brownianPath_lowerKilled_endpoint_map_eq_upper P hB a x T,
    brownianPath_drift_barrier_endpoint_map P hB (-a) x hx T hT]
  exact brownian_scalar_reflection_withDensity x _
    (show Measurable (fun y => ENNReal.ofReal (brownianUpperKilledPDFReal x T y)*brownianGaussianLikelihood (-a) T y) from
      (measurable_brownianUpperKilledPDFReal x T).ennreal_ofReal.mul (measurable_brownianGaussianLikelihood (-a) T))

/-- The killed transition density on the positive half line, for either sign of the Brownian drift. -/
noncomputable def brownianKilledTransitionPDF (a : ℝ) (T : ℝ≥0) (x y : ℝ) : ℝ :=
  if 0 < x ∧ 0 < y then Real.exp (a*(y-x)-a^2*(T : ℝ)/2)*
    (gaussianPDFReal 0 T (y-x)-gaussianPDFReal 0 T (y+x)) else 0

/-- The scalar killed kernel is jointly measurable in its two states. -/
theorem measurable_brownianKilledTransitionPDF (a : ℝ) (T : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => brownianKilledTransitionPDF a T z.1 z.2) := by
  classical
  unfold brownianKilledTransitionPDF
  apply Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter (measurableSet_lt measurable_const measurable_snd))
    _ measurable_const
  fun_prop

/-- The centered Gaussian density is symmetric in its argument. -/
theorem brownian_gaussianPDFReal_neg (T : ℝ≥0) (z : ℝ) :
    gaussianPDFReal 0 T (-z) = gaussianPDFReal 0 T z := by
  simp only [gaussianPDFReal,sub_zero,neg_sq]

/-- The scalar reflected tilted density is exactly the killed positive-half-line transition kernel. -/
theorem brownianKilledTransitionPDF_eq_reflected (a x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) (y : ℝ) :
    ENNReal.ofReal (brownianKilledTransitionPDF a T x y) =
      ENNReal.ofReal (brownianUpperKilledPDFReal x T (x-y))*brownianGaussianLikelihood (-a) T (x-y) := by
  classical
  by_cases hy : 0 < y
  · have hxy : x-y < x := by linarith
    have hneg : x-y = -(y-x) := by ring_nf
    have hsum : 2*x-(x-y) = y+x := by ring_nf
    have he : (-a)*(x-y)-(-a)^2*(T : ℝ)/2 = a*(y-x)-a^2*(T : ℝ)/2 := by ring_nf
    simp only [brownianKilledTransitionPDF,ite_eq_left (show 0 < x ∧ 0 < y from ⟨hx,hy⟩),brownianUpperKilledPDFReal,
      Set.indicator_apply,mem_Iio]
    rw [ite_eq_left hxy]
    change ENNReal.ofReal (Real.exp (a*(y-x)-a^2*(T : ℝ)/2)*
      (gaussianPDFReal 0 T (y-x)-gaussianPDFReal 0 T (y+x))) =
      ENNReal.ofReal (gaussianPDFReal 0 T (x-y)-gaussianPDFReal 0 T (2*x-(x-y)))*
        ENNReal.ofReal (Real.exp ((-a)*(x-y)-(-a)^2*(T : ℝ)/2))
    rw [hsum,he,hneg,brownian_gaussianPDFReal_neg,ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_comm _ _
  · have hxy : ¬x-y < x := by linarith
    simp only [brownianKilledTransitionPDF,hy,and_false,ite_false,brownianUpperKilledPDFReal,
      Set.indicator_apply,mem_Iio,ite_eq_right hxy,ENNReal.ofReal_zero,zero_mul]

/-- The actual killed Brownian endpoint law has the source's positive-half-line kernel. -/
theorem brownianPath_lowerKilled_endpoint_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) (hT : T ≠ 0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → 0 ≤ x+p u+a*(u : ℝ)}).map
      (fun p => x+p T+a*(T : ℝ)) =
      volume.withDensity (fun y => ENNReal.ofReal (brownianKilledTransitionPDF a T x y)) := by
  rw [brownianPath_lowerKilled_endpoint_map_reflected P hB a x hx T hT]
  congr 1
  funext y
  exact (brownianKilledTransitionPDF_eq_reflected a x hx T y).symm
/-- Reversing the drift and exchanging the states transposes the killed Gaussian kernel. -/
theorem brownianKilledTransitionPDF_transpose (a : ℝ) (T : ℝ≥0) (x y : ℝ) :
    brownianKilledTransitionPDF (-a) T y x = brownianKilledTransitionPDF a T x y := by
  classical
  have hc : (0 < y ∧ 0 < x) ↔ (0 < x ∧ 0 < y) := and_comm
  have he : (-a)*(x-y)-(-a)^2*(T : ℝ)/2 = a*(y-x)-a^2*(T : ℝ)/2 := by ring_nf
  have hx : x-y = -(y-x) := by ring_nf
  simp only [brownianKilledTransitionPDF,hc]
  rw [he]
  simp only [hx,brownian_gaussianPDFReal_neg,add_comm x y]

/-- The killed Gaussian transition kernel is nonnegative for positive times. -/
theorem brownianKilledTransitionPDF_nonneg (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (x y : ℝ) :
    0 ≤ brownianKilledTransitionPDF a T x y := by
  classical
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · have hxy : x-y < x := by linarith
      have hsum : 2*x-(x-y) = y+x := by ring_nf
      have hneg : x-y = -(y-x) := by ring_nf
      have hd := brownianUpperKilledPDFReal_nonneg x hx T hT (x-y)
      simp only [brownianUpperKilledPDFReal,Set.indicator_apply,mem_Iio] at hd
      rw [ite_eq_left hxy,hsum,hneg,brownian_gaussianPDFReal_neg] at hd
      simp only [brownianKilledTransitionPDF,hx,hy,and_self,ite_true]
      exact mul_nonneg (Real.exp_pos _).le hd
    · simp only [brownianKilledTransitionPDF,hy,and_false,ite_false,le_refl]
  · simp only [brownianKilledTransitionPDF,hx,false_and,ite_false,le_refl]


/-- Every nonnegative endpoint test of an actually surviving path integrates against the killed transition density. -/
theorem brownianPath_lowerKilled_endpoint_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) (hT : T ≠ 0) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → 0 ≤ x+p u+a*(u : ℝ)},
      F (x+p T+a*(T : ℝ)) ∂P) =
      ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF a T x y)*F y := by
  have hm : Measurable (fun p : BrownianPath => x+p T+a*(T : ℝ)) :=
    (measurable_const.add (ContinuousMap.measurable_eval T)).add measurable_const
  have hk : Measurable (fun y => ENNReal.ofReal (brownianKilledTransitionPDF a T x y)) :=
    ((measurable_brownianKilledTransitionPDF a T).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  calc
    _ = ∫⁻ y, F y ∂(P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → 0 ≤ x+p u+a*(u : ℝ)}).map
        (fun p => x+p T+a*(T : ℝ)) := (lintegral_map hF hm).symm
    _ = ∫⁻ y, F y ∂volume.withDensity (fun y => ENNReal.ofReal (brownianKilledTransitionPDF a T x y)) := by
      rw [brownianPath_lowerKilled_endpoint_map P hB a x hx T hT]
    _ = _ := lintegral_withDensity_eq_lintegral_mul volume hk hF
/-- Strict and closed finite-horizon drifted barriers differ only on a null maximum atom. -/
theorem brownianPath_drift_barrier_ae_strict (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} =ᵐ[P]
      {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) < β} := by
  have hn : ∀ᵐ p ∂P, (⨆ u : Iic T, driftedBrownianPath a p u) ≠ β := by
    rw [ae_iff]
    simpa only [not_not] using brownianPath_drift_runningMaximum_atom_zero P hB a β hβ T hT
  filter_upwards [hn] with p hp
  apply propext
  constructor
  · intro h u hu
    have hm : (⨆ u : Iic T, driftedBrownianPath a p u) < β :=
      lt_of_le_of_ne ((brownianPath_barrier_iff_runningMaximum _ T β).mp h) hp
    exact (le_ciSup (brownianPath_Iic_bddAbove (driftedBrownianPath a p) T) ⟨u,hu⟩).trans_lt hm
  · intro h u hu
    exact (h u hu).le


end DOZZ.Proofs
