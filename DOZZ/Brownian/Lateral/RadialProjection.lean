/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CircleVersion
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.Brownian.LateralLocalFiniteness
public import DOZZ.Brownian.LateralPolarFormula
public import DOZZ.Brownian.MeasureTranslationFinite
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The actual two-sided radial path and its polar projection

The continuous modification of the circle averages yields a continuous path on the full real
line. Its two halves are Brownian and independent. This construction uses the same probability
space and the actual circle-average witness of the field.

The GMC has a measurable finite version. Joint integration against a finite measure then makes
its radial Wick projection almost everywhere measurable. Its bounded-interval masses are finite
without any moment assumption. These results supply the radial and measurability clauses of the
lateral decomposition; independence of the projection requires identification with the chaos of
the lateral field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Pack the circle averages at the origin into a full continuous radial path. -/
noncomputable def originRadialPath {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ)
    (ω : Ω) : TwoSidedPath :=
  ContinuousMap.mkD (fun s => Xc ω 0 s) 0

/-- One common continuity event identifies the packed path at every real radius. -/
theorem originRadialPath_eval_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Xc : Ω → ℂ → ℝ → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, originRadialPath Xc ω s = Xc ω 0 s := by
  filter_upwards [hcont] with ω hω s
  apply ContinuousMap.mkD_apply_of_continuous
  exact hω.comp (continuous_const.prodMk continuous_id)

/-- Dense real evaluations detect almost-everywhere measurability of full radial paths. -/
theorem aemeasurable_twoSidedPath_of_eval {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → TwoSidedPath}
    (hA : ∀ s, AEMeasurable (fun ω => A ω s) P) : AEMeasurable A P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ
  let _ := hDc.to_subtype
  let E : TwoSidedPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval (fun t => ContinuousMap.measurable_eval t.1)
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    have he := hDd.denseRange_val.equalizer p.continuous q.continuous hpq
    exact congrFun he
  apply (hmE.measurableEmbedding hinj).aemeasurable_comp_iff.mp
  exact AEMeasurable.of_eval (fun t => hA t.1)

/-- The packed origin path is measurable up to a null set under the circle-average witness. -/
theorem originRadialPath_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    AEMeasurable (originRadialPath Xc) P := by
  apply aemeasurable_twoSidedPath_of_eval
  intro s
  exact (hc.2.1 0 s).aemeasurable.congr
    ((originRadialPath_eval_ae hcont).mono (fun ω hω => (hω s).symm))

/-- The radial path starts at the equator pin on the same probability space. -/
theorem originRadialPath_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    ∀ᵐ ω ∂P, originRadialPath Xc ω 0 = 0 := by
  filter_upwards [originRadialPath_eval_ae hcont,
    circleAverage_equator_ae_eq_zero X Xc hc] with ω hω hzero
  exact (hω 0).trans hzero

/-- Both halves of the packed path have the Brownian path law. -/
theorem originRadialPath_isBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IsBrownianReal (fun t ω => originRadialPath Xc ω (t : ℝ)) P ∧
      IsBrownianReal (fun t ω => originRadialPath Xc ω (-(t : ℝ))) P := by
  have hpre := circleAverage_origin_preBrownian P X Xc hX hc
  have heq := originRadialPath_eval_ae hcont
  constructor
  · refine ⟨hpre.1.congr (fun t => heq.mono (fun ω hω => (hω t).symm)), ?_⟩
    exact ae_of_all P (fun ω => (originRadialPath Xc ω).continuous.comp NNReal.continuous_coe)
  · refine ⟨hpre.2.1.congr (fun t => heq.mono (fun ω hω => (hω (-(t : ℝ))).symm)), ?_⟩
    exact ae_of_all P (fun ω =>
      (originRadialPath Xc ω).continuous.comp NNReal.continuous_coe.neg)

/-- The two full half-path coordinate families are independent. -/
theorem originRadialPath_halves_indep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IndepFun (fun ω => fun t : ℝ≥0 => originRadialPath Xc ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => originRadialPath Xc ω (-(t : ℝ))) P := by
  apply (circleAverage_origin_preBrownian P X Xc hX hc).2.2.1.congr
  · filter_upwards [originRadialPath_eval_ae hcont] with ω hω
    exact funext (fun t => (hω t).symm)
  · filter_upwards [originRadialPath_eval_ae hcont] with ω hω
    exact funext (fun t => (hω (-(t : ℝ))).symm)



/-- The origin covariance at arbitrary real times, before splitting into its two halves. -/
theorem originRadialPath_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) (s t : ℝ) :
    covariance (fun ω => originRadialPath Xc ω s)
      (fun ω => originRadialPath Xc ω t) P =
        min s t + max 0 (-s) + max 0 (-t) := by
  rw [covariance_congr_ae
    ((originRadialPath_eval_ae hcont).mono (fun ω hω => hω s))
    ((originRadialPath_eval_ae hcont).mono (fun ω hω => hω t)),
    circleAverage_covariance_integral P X Xc hX hc,
    integral_integral_gffKernel_origin]




/-- The radial Wick weight, including its zero value at the origin. -/
noncomputable def lateralRadialWeight (γ : ℝ) (A : TwoSidedPath) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (if ‖x‖ = 0 then 0 else
    Real.exp (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|))

/-- Joint measurability includes the radial path, charge, and spatial parameter. -/
theorem measurable_lateralRadialWeight :
    Measurable (fun p : (ℝ × TwoSidedPath) × ℂ =>
      lateralRadialWeight p.1.1 p.1.2 p.2) := by
  unfold lateralRadialWeight
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_norm.comp measurable_snd) measurable_const
  · exact measurable_const
  · have hev : Measurable (fun p : (ℝ × TwoSidedPath) × ℂ =>
        p.1.2 (-Real.log ‖p.2‖)) := by
      exact continuous_eval.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk
          (measurable_neg.comp (Real.measurable_log.comp
            (measurable_norm.comp measurable_snd))))
    have hQ : Measurable (fun γ : ℝ => Q γ) := by
      unfold Q
      fun_prop
    have hγ : Measurable (fun p : (ℝ × TwoSidedPath) × ℂ => p.1.1) :=
      measurable_fst.comp measurable_fst
    have hlog : Measurable (fun p : (ℝ × TwoSidedPath) × ℂ => |Real.log ‖p.2‖|) :=
      continuous_abs.measurable.comp (Real.measurable_log.comp (measurable_norm.comp measurable_snd))
    exact Real.measurable_exp.comp ((hγ.neg.mul hev).add
      ((hγ.mul (hQ.comp hγ)).mul hlog))

/-- Polar projection is jointly measurable on finite plane measures. -/
theorem measurable_lateralProjectedGMC_finite :
    Measurable (fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
      lateralProjectedGMC p.1.1 p.1.2 (p.2 : Measure ℂ)) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  let ρ : ℂ → ℝ := fun x => -Real.log ‖x‖
  have hρ : Measurable ρ := measurable_neg.comp (Real.measurable_log.comp measurable_norm)
  have hpre : MeasurableSet (ρ ⁻¹' S) := hS.preimage hρ
  have hi : Measurable (fun p : (ℝ × TwoSidedPath) × ℂ =>
      (ρ ⁻¹' S).indicator (fun x => lateralRadialWeight p.1.1 p.1.2 x) p.2) := by
    exact measurable_lateralRadialWeight.indicator
      (hpre.preimage measurable_snd)
  have hm := measurable_lintegral_finiteMeasure_parameter hi
  convert hm using 1
  funext p
  unfold lateralProjectedGMC
  rw [Measure.map_apply hρ hS, withDensity_apply _ hpre]
  rw [← lintegral_indicator hpre]
  rfl

/-- An arbitrary GMC version is almost-everywhere measurable as a measure. -/
theorem equatorGFF_GMC_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) : AEMeasurable M P := by
  obtain ⟨N, hNm, _, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  exact hNm.aemeasurable.congr (hMN.mono (fun _ hω => hω.symm))

/-- Removing the radial Wick factor preserves measure-valued AE measurability. -/
theorem lateralProjectedGMC_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (M : Ω → Measure ℂ) (hMm : AEMeasurable M P)
    (hMf : ∀ ω, IsFiniteMeasure (M ω)) :
    AEMeasurable (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P := by
  let N : Ω → FiniteMeasure ℂ := fun ω => ⟨M ω, hMf ω⟩
  have hN : AEMeasurable N P := by
    exact @AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hMm
      {μ | IsFiniteMeasure μ} hMf
  have hγa : AEMeasurable (fun _ : Ω => γ) P := aemeasurable_const
  have hpair : AEMeasurable (fun ω => (γ, A ω)) P := hγa.prodMk hA
  have hp : AEMeasurable (fun ω => ((γ, A ω), N ω)) P := hpair.prodMk hN
  have hr := measurable_lateralProjectedGMC_finite.comp_aemeasurable hp
  change AEMeasurable (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P at hr
  exact hr


/-- The polar projection assigns no mass to the plane origin, before taking its pushforward. -/
theorem lateralRadialWeight_zero (γ : ℝ) (A : TwoSidedPath) :
    lateralRadialWeight γ A (0 : ℂ) = 0 := by
  simp [lateralRadialWeight]

/-- Away from the plane origin, the radial Wick factor is strictly positive and finite. -/
theorem lateralRadialWeight_pos {γ : ℝ} {A : TwoSidedPath} {x : ℂ} (hx : x ≠ 0) :
    0 < lateralRadialWeight γ A x ∧ lateralRadialWeight γ A x < ⊤ := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [lateralRadialWeight, hnorm, reduceIte]
  exact ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top⟩

/-- Reinserting the radial factor cancels the removal weight exactly. -/
theorem lateralRadialWeight_cancel (γ : ℝ) (A : TwoSidedPath) (x : ℂ) :
    lateralRadialWeight γ A x *
      ENNReal.ofReal (Real.exp (γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖|)) =
        if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · simp [hx, lateralRadialWeight]
  · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp only [lateralRadialWeight, hnorm, hx, reduceIte]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have he : -γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖| +
        (γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖|) = 0 := by ring
    rw [he, Real.exp_zero, ENNReal.ofReal_one]

/-- The forward radial Wick factor on the full cylinder. -/
noncomputable def lateralForwardWeight (γ : ℝ) (A : TwoSidedPath) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * A s - γ * Q γ * |s|))

/-- The forward factor is measurable for every continuous radial path. -/
theorem measurable_lateralForwardWeight (γ : ℝ) (A : TwoSidedPath) :
    Measurable (lateralForwardWeight γ A) := by
  unfold lateralForwardWeight
  fun_prop

/-- The projected chaos recovers every nonnegative radial test of the original plane chaos,
with its possible atom at the origin removed. No lateral-law assertion is used in this identity. -/
theorem lateralProjectedGMC_reinsert_lintegral (γ : ℝ) (A : TwoSidedPath)
    (M : Measure ℂ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, lateralForwardWeight γ A s * f s ∂lateralProjectedGMC γ A M) =
      ∫⁻ x, if x = 0 then 0 else f (-Real.log ‖x‖) ∂M := by
  have hg : Measurable (fun s => lateralForwardWeight γ A s * f s) :=
    (measurable_lateralForwardWeight γ A).mul hf
  rw [lateralProjectedGMC_lintegral_eq γ A M _ hg]
  apply lintegral_congr
  intro x
  change lateralRadialWeight γ A x *
    (lateralForwardWeight γ A (-Real.log ‖x‖) * f (-Real.log ‖x‖)) = _
  rw [← mul_assoc]
  have hforward : lateralForwardWeight γ A (-Real.log ‖x‖) =
      ENNReal.ofReal (Real.exp (γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖|)) := by
    simp only [lateralForwardWeight, abs_neg]
  rw [hforward, lateralRadialWeight_cancel]
  split_ifs <;> simp


/-- The charge coefficient is exactly the polar Jacobian plus the radial Wick variance. -/
theorem gamma_mul_Q_eq (γ : ℝ) (hγ : γ ≠ 0) : γ * Q γ = 2 + γ ^ 2 / 2 := by
  unfold Q
  field_simp



end DOZZ.Proofs
