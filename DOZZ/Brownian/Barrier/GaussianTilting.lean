/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.StoppedPaths
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Finite-horizon Gaussian change of drift

Completing the square proves the scalar Gaussian likelihood identity. The capped
Brownian bridge and terminal value are jointly Gaussian and uncorrelated, hence
independent as actual continuous-path and scalar random variables.

The likelihood changes only the terminal Gaussian. Reconstructing from the bridge
and terminal value proves the change of drift on the entire stopped continuous
path carrier, including the terminal horizon zero. This gives the finite-time
path-law assertion of the change of drift from Gaussian inputs.

Nonnegative stopped-path tests inherit the exact likelihood identity. In
particular, a drifted barrier probability is the likelihood-weighted integral
over the original zero-drift barrier. Both directions of absolute continuity
preserve the original null sets. The later killed-density calculation must retain
its reflection cancellation before estimating the weighted integral.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs
/-- The scalar Gaussian likelihood used in the finite-horizon Brownian tilt. -/
noncomputable def brownianGaussianLikelihood (a : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a*x-a^2*(v : ℝ)/2))

/-- The scalar likelihood is measurable. -/
theorem measurable_brownianGaussianLikelihood (a : ℝ) (v : ℝ≥0) :
    Measurable (brownianGaussianLikelihood a v) := by
  unfold brownianGaussianLikelihood
  fun_prop

/-- Completing the square identifies the scalar Gaussian tilted density pointwise. -/
theorem brownianGaussianLikelihood_mul_pdf (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    gaussianPDF 0 v x*brownianGaussianLikelihood a v x = gaussianPDF (a*(v : ℝ)) v x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [gaussianPDF,gaussianPDF,brownianGaussianLikelihood,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal,sub_zero]
  have hs : -(x^2)/(2*(v : ℝ))+(a*x-a^2*(v : ℝ)/2) =
      -(x-a*(v : ℝ))^2/(2*(v : ℝ)) := by
    field_simp
    ring
  rw [mul_assoc,← Real.exp_add,hs]

/-- The actual scalar Gaussian measure tilted by its likelihood has the shifted Gaussian law. -/
theorem gaussianReal_withDensity_brownianGaussianLikelihood (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (gaussianReal 0 v).withDensity (brownianGaussianLikelihood a v) = gaussianReal (a*(v : ℝ)) v := by
  rw [gaussianReal_of_var_ne_zero 0 hv,gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (measurable_brownianGaussianLikelihood a v)]
  congr 1
  funext x
  exact brownianGaussianLikelihood_mul_pdf a v hv x
/-- Pushing forward a likelihood depending on the pushed variable gives its actual tilted marginal. -/
theorem brownian_map_withDensity_comp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (w : E → ℝ≥0∞) (hw : Measurable w) :
    (P.withDensity (fun ω => w (X ω))).map X = (P.map X).withDensity w := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hX hS,withDensity_apply _ (hS.preimage hX),withDensity_apply _ hS]
  exact (setLIntegral_map hS hw hX).symm

/-- Brownian bridge centered at the chosen terminal time, held constant beyond that time. -/
noncomputable def brownianBridgePath (T : ℝ≥0) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p (min t T)-((min t T : ℝ≥0) : ℝ)/(T : ℝ)*p T,by fun_prop⟩

/-- At a fixed terminal time the literal bridge is continuous as a function of the input path. -/
theorem continuous_brownianBridgePath (T : ℝ≥0) : Continuous (brownianBridgePath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : BrownianPath × ℝ≥0 => z.1 (min z.2 T)-
    ((min z.2 T : ℝ≥0) : ℝ)/(T : ℝ)*z.1 T)
  exact (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.min continuous_const))).sub
    (((NNReal.continuous_coe.comp (continuous_snd.min continuous_const)).div_const _).mul
      ((continuous_eval_const T).comp continuous_fst))

/-- The capped bridge and terminal value form one Gaussian process. -/
theorem brownianBridge_joint_isGaussian (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (T : ℝ≥0) :
    IsGaussianProcess (Sum.elim (fun t (p : BrownianPath) => brownianBridgePath T p t)
      (fun (_ : Unit) (p : BrownianPath) => p T)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  rintro (t | ⟨⟩)
  · exact ⟨{min t T,T},
      { toFun x := x ⟨min t T,by simp⟩-((min t T : ℝ≥0) : ℝ)/(T : ℝ)*x ⟨T,by simp⟩
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring },by simp [brownianBridgePath]⟩
  · exact ⟨{T},
      { toFun x := x ⟨T,by simp⟩
        map_add' x y := by simp
        map_smul' c x := by simp },by simp⟩

/-- The Brownian bridge is uncorrelated with its chosen terminal value at every time. -/
theorem brownianBridge_covariance_terminal_zero (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (T t : ℝ≥0) :
    cov[fun p => brownianBridgePath T p t,fun p => p T; P] = 0 := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  change cov[fun p => p (min t T)-((min t T : ℝ≥0) : ℝ)/(T : ℝ)*p T,fun p => p T; P] = 0
  rw [covariance_fun_sub_left
    (hB.isGaussianProcess.hasGaussianLaw_eval (min t T)).memLp_two
    ((hB.isGaussianProcess.hasGaussianLaw_eval T).memLp_two.const_mul _)
    (hB.isGaussianProcess.hasGaussianLaw_eval T).memLp_two,
    covariance_const_mul_left,hB.covariance_eval,hB.covariance_eval,min_self,
    min_eq_left (by exact_mod_cast min_le_right t T)]
  by_cases hT : T = 0
  · simp only [hT,min_zero,NNReal.coe_zero,zero_div,zero_mul,sub_zero]
  · have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    field_simp
    ring

/-- Gaussian orthogonality makes the entire capped bridge process independent of its terminal value. -/
theorem brownianBridge_process_indep_terminal (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (T : ℝ≥0) :
    IndepFun (fun p t => brownianBridgePath T p t) (fun p => p T) P := by
  have hi := IsGaussianProcess.indepFun_of_covariance_eq_zero (brownianBridge_joint_isGaussian P hB T)
    (fun t => ((ContinuousMap.measurable_eval t).comp (continuous_brownianBridgePath T).measurable).aemeasurable)
    (fun (_ : Unit) => (ContinuousMap.measurable_eval T).aemeasurable)
    (fun t (_ : Unit) => brownianBridge_covariance_terminal_zero P hB T t)
  simpa only [Function.comp_def,id_eq] using hi.comp measurable_id (measurable_pi_apply ())

/-- Independence holds for the actual continuous bridge path, rather than only its finite projections. -/
theorem brownianBridgePath_indep_terminal (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (T : ℝ≥0) :
    IndepFun (brownianBridgePath T) (fun p => p T) P := by
  change Indep (MeasurableSpace.comap (brownianBridgePath T) (inferInstance : MeasurableSpace BrownianPath))
    (MeasurableSpace.comap (fun p : BrownianPath => p T) inferInstance) P
  rw [brownianPath_measurableSpace_eq_comap,MeasurableSpace.comap_comp]
  exact brownianBridge_process_indep_terminal P hB T
/-- The actual finite-horizon Brownian exponential tilt on continuous paths. -/
noncomputable def brownianFiniteTilt (P : Measure BrownianPath)
    (a : ℝ) (T : ℝ≥0) : Measure BrownianPath :=
  P.withDensity (fun p => brownianGaussianLikelihood a T (p T))


/-- Tilting only the terminal normal preserves the independent continuous bridge law. -/
theorem brownianFiniteTilt_bridge_terminal_map (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    (brownianFiniteTilt P a T).map (fun p => (brownianBridgePath T p,p T)) =
      (P.map (brownianBridgePath T)).prod (gaussianReal (a*(T : ℝ)) T) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let J : BrownianPath → BrownianPath × ℝ := fun p => (brownianBridgePath T p,p T)
  have hmJ : Measurable J :=
    (continuous_brownianBridgePath T).measurable.prodMk (ContinuousMap.measurable_eval T)
  have he := brownian_map_withDensity_comp P J hmJ
    (fun z => brownianGaussianLikelihood a T z.2)
    ((measurable_brownianGaussianLikelihood a T).comp measurable_snd)
  have hJlaw := (brownianBridgePath_indep_terminal P hB T).map_prod_eq_prod_map_map
    (continuous_brownianBridgePath T).measurable.aemeasurable
    (ContinuousMap.measurable_eval T).aemeasurable
  change P.map J = _ at hJlaw
  rw [hJlaw,← prod_withDensity_right (measurable_brownianGaussianLikelihood a T),
    (hB.hasLaw_eval T).map_eq,gaussianReal_withDensity_brownianGaussianLikelihood a T hT] at he
  exact he

/-- Reconstruct a stopped path from its bridge and terminal value. -/
noncomputable def brownianBridgeReconstruct (T : ℝ≥0) (z : BrownianPath × ℝ) : BrownianPath :=
  ⟨fun t => z.1 t+((min t T : ℝ≥0) : ℝ)/(T : ℝ)*z.2,by fun_prop⟩

/-- Reconstruction is continuous on the literal continuous-path and endpoint carriers. -/
theorem continuous_brownianBridgeReconstruct (T : ℝ≥0) : Continuous (brownianBridgeReconstruct T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (BrownianPath × ℝ) × ℝ≥0 => z.1.1 z.2+
    ((min z.2 T : ℝ≥0) : ℝ)/(T : ℝ)*z.1.2)
  exact (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)).add
    (((NNReal.continuous_coe.comp (continuous_snd.min continuous_const)).div_const _).mul continuous_fst.snd)

/-- The bridge plus its original terminal value reconstructs the literal stopped path. -/
theorem brownianBridgeReconstruct_original (T : ℝ≥0) (p : BrownianPath) :
    brownianBridgeReconstruct T (brownianBridgePath T p,p T) = stopBrownianPath p T := by
  apply ContinuousMap.ext
  intro t
  change (p (min t T)-((min t T : ℝ≥0) : ℝ)/(T : ℝ)*p T)+
    ((min t T : ℝ≥0) : ℝ)/(T : ℝ)*p T = p (min t T)
  ring

/-- Translating only the terminal normal produces exactly the stopped Brownian drift translation. -/
theorem brownianBridgeReconstruct_shift (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (p : BrownianPath) :
    brownianBridgeReconstruct T (brownianBridgePath T p,p T+a*(T : ℝ)) =
      stopBrownianPath (driftedBrownianPath a p) T := by
  apply ContinuousMap.ext
  intro t
  change (p (min t T)-((min t T : ℝ≥0) : ℝ)/(T : ℝ)*p T)+
    ((min t T : ℝ≥0) : ℝ)/(T : ℝ)*(p T+a*(T : ℝ)) = p (min t T)+a*((min t T : ℝ≥0) : ℝ)
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  field_simp
  ring

/-- The finite-horizon Gaussian change of drift on the actual stopped continuous-path carrier. -/
theorem brownianFiniteTilt_stoppedPath_map (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    (brownianFiniteTilt P a T).map (fun p => stopBrownianPath p T) =
      P.map (fun p => stopBrownianPath (driftedBrownianPath a p) T) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmH := (continuous_brownianBridgePath T).measurable
  have hmY : Measurable (fun p : BrownianPath => p T) := ContinuousMap.measurable_eval T
  have hmJ := hmH.prodMk hmY
  have hmJ' : Measurable (fun p : BrownianPath => (brownianBridgePath T p,p T+a*(T : ℝ))) :=
    hmH.prodMk (hmY.add_const _)
  have hi : IndepFun (brownianBridgePath T) (fun p => p T+a*(T : ℝ)) P := by
    simpa only [Function.comp_def,id_eq] using
      (brownianBridgePath_indep_terminal P hB T).comp measurable_id (measurable_id.add_const (a*(T : ℝ)))
  have hshift := hi.map_prod_eq_prod_map_map hmH.aemeasurable (hmY.add_const _).aemeasurable
  rw [(gaussianReal_add_const (hB.hasLaw_eval T) (a*(T : ℝ))).map_eq,zero_add] at hshift
  have he := (brownianFiniteTilt_bridge_terminal_map P hB a T hT).trans hshift.symm
  have hout := congrArg (fun μ : Measure (BrownianPath × ℝ) => μ.map (brownianBridgeReconstruct T)) he
  rw [Measure.map_map (continuous_brownianBridgeReconstruct T).measurable hmJ,
    Measure.map_map (continuous_brownianBridgeReconstruct T).measurable hmJ'] at hout
  simpa only [Function.comp_def,brownianBridgeReconstruct_original,
    brownianBridgeReconstruct_shift a T hT] using hout
/-- Nonnegative stopped-path tests satisfy the finite-horizon Gaussian likelihood identity. -/
theorem brownianFiniteTilt_stoppedPath_lintegral (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (F : BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (stopBrownianPath (driftedBrownianPath a p) T) ∂P) =
      ∫⁻ p, brownianGaussianLikelihood a T (p T)*F (stopBrownianPath p T) ∂P := by
  have hmStop : Measurable (fun p : BrownianPath => stopBrownianPath p T) :=
    continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hmDrift : Measurable (fun p : BrownianPath => stopBrownianPath (driftedBrownianPath a p) T) :=
    hmStop.comp (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  calc
    _ = ∫⁻ q, F q ∂P.map (fun p => stopBrownianPath (driftedBrownianPath a p) T) :=
      (lintegral_map hF hmDrift).symm
    _ = ∫⁻ q, F q ∂(brownianFiniteTilt P a T).map (fun p => stopBrownianPath p T) := by
      rw [brownianFiniteTilt_stoppedPath_map P hB a T hT]
    _ = ∫⁻ p, F (stopBrownianPath p T) ∂brownianFiniteTilt P a T := lintegral_map hF hmStop
    _ = _ := lintegral_withDensity_eq_lintegral_mul P
      ((measurable_brownianGaussianLikelihood a T).comp (ContinuousMap.measurable_eval T))
      (hF.comp hmStop)

/-- Stopping at the terminal horizon leaves the barrier event unchanged. -/
theorem stopBrownianPath_barrier_iff (p : BrownianPath) (T : ℝ≥0) (β : ℝ) :
    (∀ u : ℝ≥0, u ≤ T → stopBrownianPath p T u ≤ β) ↔
      ∀ u : ℝ≥0, u ≤ T → p u ≤ β := by
  constructor <;> intro h u hu
  · have he := h u hu
    simpa only [stopBrownianPath,ContinuousMap.coe_mk,min_eq_left hu] using he
  · change p (min u T) ≤ β
    rw [min_eq_left hu]
    exact h u hu

/-- The tilted probability of a barrier equals the original probability for the drifted path. -/
theorem brownianFiniteTilt_barrier_probability (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a β : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    (brownianFiniteTilt P a T) {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} =
      P {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} := by
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}
  have hA : MeasurableSet A :=
    (brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
      (measurableSet_brownianPath_barrier T β)
  have hmStop : Measurable (fun p : BrownianPath => stopBrownianPath p T) :=
    continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hmDrift : Measurable (fun p : BrownianPath => stopBrownianPath (driftedBrownianPath a p) T) :=
    hmStop.comp (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  have he := congrArg (fun μ : Measure BrownianPath => μ A) (brownianFiniteTilt_stoppedPath_map P hB a T hT)
  rw [Measure.map_apply hmStop hA,Measure.map_apply hmDrift hA] at he
  have hleft : (fun p : BrownianPath => stopBrownianPath p T) ⁻¹' A = A := by
    ext p
    exact stopBrownianPath_barrier_iff p T β
  have hright : (fun p : BrownianPath => stopBrownianPath (driftedBrownianPath a p) T) ⁻¹' A =
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} := by
    ext p
    change (∀ u : ℝ≥0, u ≤ T → stopBrownianPath (driftedBrownianPath a p) T u ≤ β) ↔ _
    rw [stopBrownianPath_barrier_iff]
    rfl
  rw [hleft,hright] at he
  exact he

/-- The source's drifted barrier probability is the actual terminal-likelihood weighted integral over the zero-drift barrier. -/
theorem brownian_drift_barrier_probability_likelihood (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a β : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β} =
      ∫⁻ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β},
        brownianGaussianLikelihood a T (p T) ∂P := by
  rw [← brownianFiniteTilt_barrier_probability P hB a β T hT,brownianFiniteTilt,
    withDensity_apply _
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
        (measurableSet_brownianPath_barrier T β))]


/-- Every finite tilt is absolutely continuous with respect to the original Brownian law. -/
theorem brownianFiniteTilt_absolutelyContinuous (P : Measure BrownianPath) (a : ℝ) (T : ℝ≥0) :
    brownianFiniteTilt P a T ≪ P := withDensity_absolutelyContinuous _ _
/-- Gaussian likelihoods are finite and strictly positive at every actual sample. -/
theorem brownianGaussianLikelihood_ne_zero (a : ℝ) (v : ℝ≥0) (x : ℝ) :
    brownianGaussianLikelihood a v x ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'


/-- At time zero the Brownian likelihood equals one on the one common initial-value event. -/
theorem brownianFiniteTilt_zero_time (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) : brownianFiniteTilt P a 0 = P := by
  have he : (fun p : BrownianPath => brownianGaussianLikelihood a 0 (p 0)) =ᵐ[P] 1 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    simp only [brownianGaussianLikelihood,hp,NNReal.coe_zero,mul_zero,zero_div,sub_zero,
      Real.exp_zero,ENNReal.ofReal_one,Pi.one_apply]
  rw [brownianFiniteTilt,withDensity_congr_ae he,withDensity_one]

/-- The finite-horizon path-law tilt also includes the degenerate terminal horizon. -/
theorem brownianFiniteTilt_stoppedPath_map_all (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) (T : ℝ≥0) :
    (brownianFiniteTilt P a T).map (fun p => stopBrownianPath p T) =
      P.map (fun p => stopBrownianPath (driftedBrownianPath a p) T) := by
  by_cases hT : T = 0
  · rw [hT,brownianFiniteTilt_zero_time P hB a]
    congr 1
    funext p
    apply ContinuousMap.ext
    intro t
    change p (min t 0) = p (min t 0)+a*((min t 0 : ℝ≥0) : ℝ)
    simp only [min_zero,NNReal.coe_zero,mul_zero,add_zero]
  · exact brownianFiniteTilt_stoppedPath_map P hB a T hT


/-- A stopped-path test is measurable as a function of its original continuous path. -/
theorem measurable_stopBrownianPath_fixed (T : ℝ≥0) : Measurable (fun p : BrownianPath => stopBrownianPath p T) :=
  continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)

/-- The finite-horizon likelihood identity for arbitrary nonnegative stopped-path tests, including time zero. -/
theorem brownianFiniteTilt_stoppedPath_lintegral_all (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) (T : ℝ≥0)
    (F : BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (stopBrownianPath (driftedBrownianPath a p) T) ∂P) =
      ∫⁻ p, brownianGaussianLikelihood a T (p T)*F (stopBrownianPath p T) ∂P := by
  have hmStop := measurable_stopBrownianPath_fixed T
  have hmDrift : Measurable (fun p : BrownianPath => stopBrownianPath (driftedBrownianPath a p) T) :=
    hmStop.comp (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  calc
    _ = ∫⁻ q, F q ∂P.map (fun p => stopBrownianPath (driftedBrownianPath a p) T) :=
      (lintegral_map hF hmDrift).symm
    _ = ∫⁻ q, F q ∂(brownianFiniteTilt P a T).map (fun p => stopBrownianPath p T) := by
      rw [brownianFiniteTilt_stoppedPath_map_all P hB a T]
    _ = ∫⁻ p, F (stopBrownianPath p T) ∂brownianFiniteTilt P a T := lintegral_map hF hmStop
    _ = _ := lintegral_withDensity_eq_lintegral_mul P
      ((measurable_brownianGaussianLikelihood a T).comp (ContinuousMap.measurable_eval T))
      (hF.comp hmStop)
end DOZZ.Proofs
