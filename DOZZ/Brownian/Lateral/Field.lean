/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.GFFStructure.GaussianIntegration
public import DOZZ.GFFStructure.OffCenterDecomposition

/-!
# The origin lateral field on the whole punctured plane

Subtract the radial Bochner average from every smooth test supported away from the origin.
The resulting test family and all origin circles belong to the same closed Gaussian space.
The concentric covariance identifies the radial average as the orthogonal radial projection.
Consequently the entire real radial process is independent of the whole lateral test family.

No pointwise lateral noise is defined: lateral coordinates are evaluations of the distribution
against smooth compact tests. The covariance calculation applies to tests on either side of the
equator and to tests crossing it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Compact smooth tests for the lateral distribution on the punctured plane. -/
abbrev OriginLateralTest := {ψ : TestFn // (0 : ℂ) ∉ tsupport ψ}

/-- The lateral evaluation removes the samplewise radial integral from the actual field. -/
noncomputable def originLateralEvaluation {Ω : Type*} (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (ψ : TestFn) (ω : Ω) : ℝ :=
  X ω ψ - ∫ w : ℂ, ψ w * Xc ω 0 (-Real.log ‖w‖)

/-- Scalar concentric covariance written in plane coordinates. -/
noncomputable def originRadialCovariance (s : ℝ) (w : ℂ) : ℝ :=
  min s (-Real.log ‖w‖) + max 0 (-s) + max 0 (Real.log ‖w‖)

/-- The plane potential of one origin circle is precisely the radial covariance. -/
theorem origin_circleKernelPotential_eq (s : ℝ) (w : ℂ) (hw : w ≠ 0) :
    (∫ v, gffKernel w v ∂circleMeasure 0 s) = originRadialCovariance s w := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [integral_gffKernel_circleMeasure, integral_log_normPlus_circleMeasure_origin_eq_max,
    zero_sub, norm_neg, neg_log_max_exp_eq_min hnorm]
  unfold originRadialCovariance
  have hpin : Real.log (normPlus w) = max 0 (Real.log ‖w‖) := by
    unfold normPlus
    rcases le_total 1 ‖w‖ with hn | hn
    · rw [max_eq_right hn, max_eq_right (Real.log_nonneg hn)]
    · rw [max_eq_left hn, Real.log_one,
        max_eq_left (Real.log_nonpos hnorm.le hn)]
  rw [hpin]
  ring

/-- Compact tests pair with the origin circles by the radial covariance kernel. -/
theorem circleCross_origin_eq_radial_integral (s : ℝ) (ψ : TestFn)
    (hψ : (0 : ℂ) ∉ tsupport ψ) :
    circleCross 0 s ψ = ∫ w : ℂ, ψ w * originRadialCovariance s w := by
  unfold circleCross
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    dsimp only
    by_cases hw : ψ w = 0
    · simp only [hw, zero_mul]
    · have hw0 : w ≠ 0 := by
        intro hzero
        exact hψ (hzero ▸ subset_tsupport ψ hw)
      rw [origin_circleKernelPotential_eq s w hw0]

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The actual radial/circle covariance has the same scalar plane kernel. -/
theorem origin_circle_radial_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (s : ℝ) (w : ℂ) :
    covariance (fun ω => Xc ω 0 s)
      (fun ω => Xc ω 0 (-Real.log ‖w‖)) P = originRadialCovariance s w := by
  rw [circleAverage_covariance_integral P X Xc hX hc,
    integral_integral_gffKernel_origin]
  simp only [originRadialCovariance, neg_neg]

/-- The radial Bochner integral has exactly the field's pairing with each origin circle. -/
theorem origin_radialIntegral_circle_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (s : ℝ) (ψ : TestFn) (hψ : (0 : ℂ) ∉ tsupport ψ) :
    covariance (fun ω => Xc ω 0 s) (radialIntegralL2 X Xc hc 0 ψ) P =
      circleCross 0 s ψ := by
  let _ := hX.1
  rw [covariance_comm]
  rw [← covariance_congr_ae (EventuallyEq.rfl :
    (⇑(radialIntegralL2 X Xc hc 0 ψ)) =ᵐ[P] _) (circleAverageL2_ae_eq hc (0, s)),
    radialIntegralL2_circle_covariance X Xc hX hc 0 ψ hψ,
    circleCross_origin_eq_radial_integral s ψ hψ]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    simp only [sub_zero]
    rw [covariance_comm, origin_circle_radial_covariance X Xc hX hc]

/-- The lateral L² representative agrees with the literal whole-plane lateral test. -/
theorem originLateralEvaluation_ae_eq_L2 (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ψ : TestFn) (hψ : (0 : ℂ) ∉ tsupport ψ) :
    (⇑(lateralEvaluationL2 X Xc hX hc 0 ψ)) =ᵐ[P]
      originLateralEvaluation X Xc ψ := by
  let _ := hX.1
  filter_upwards [lateralEvaluationL2_ae_eq X Xc hX hc hm 0 ψ hψ] with ω hω
  change (lateralEvaluationL2 X Xc hX hc 0 ψ) ω =
    X ω ψ - ∫ w : ℂ, ψ w * Xc ω 0 (-Real.log ‖w‖)
  simpa only [sub_zero] using hω

/-- Lateral evaluations retain actual square integrability and measurability. -/
theorem originLateralEvaluation_memLp (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ψ : TestFn) (hψ : (0 : ℂ) ∉ tsupport ψ) :
    MemLp (originLateralEvaluation X Xc ψ) 2 P :=
  MemLp.ae_eq (originLateralEvaluation_ae_eq_L2 X Xc hX hc hm ψ hψ) (Lp.memLp _)



/-- Every radial circle is orthogonal to every whole-plane lateral test. -/
theorem originLateralEvaluation_circle_covariance_zero
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (s : ℝ) (ψ : TestFn) (hψ : (0 : ℂ) ∉ tsupport ψ) :
    covariance (fun ω => Xc ω 0 s) (originLateralEvaluation X Xc ψ) P = 0 := by
  let _ := hX.1
  have hae := originLateralEvaluation_ae_eq_L2 X Xc hX hc hm ψ hψ
  rw [← covariance_congr_ae (EventuallyEq.rfl : (fun ω => Xc ω 0 s) =ᵐ[P] _) hae]
  rw [lateralEvaluationL2, covariance_congr_ae (EventuallyEq.rfl :
    (fun ω => Xc ω 0 s) =ᵐ[P] _) (Lp.coeFn_sub _ _),
    covariance_sub_right (hc.2.1 0 s) (Lp.memLp _) (Lp.memLp _),
    covariance_congr_ae (EventuallyEq.rfl : (fun ω => Xc ω 0 s) =ᵐ[P] _)
      (MemLp.coeFn_toLp (equatorGFF_test_memLp X hX ψ)),
    circleAverage_test_covariance P X Xc hX hc,
    origin_radialIntegral_circle_covariance X Xc hX hc s ψ hψ, sub_self]

/-- Joint Gaussianity of the whole radial and lateral test families. -/
theorem origin_radial_lateral_isGaussianProcess (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) :
    IsGaussianProcess (Sum.elim (fun s : ℝ => fun ω => Xc ω 0 s)
      (fun ψ : OriginLateralTest => originLateralEvaluation X Xc ψ.val)) P := by
  let _ := hX.1
  let U : ℝ ⊕ OriginLateralTest → Lp ℝ 2 P :=
    Sum.elim (fun s => circleAverageL2 hc (0, s))
      (fun ψ => lateralEvaluationL2 X Xc hX hc 0 ψ.val)
  have hmem : ∀ j, U j ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
    intro j
    cases j with
    | inl s => exact mem_gaussianHilbertSpan _ (Sum.inl (0, s))
    | inr ψ => exact lateralEvaluationL2_mem_gaussianHilbertSpan X Xc hX hc 0 ψ.val ψ.property
  apply (isGaussianProcess_of_mem_gaussianHilbertSpan
    (gffStructureL2Family_isGaussianProcess X Xc hX hc) U hmem).congr
  intro j
  cases j with
  | inl s => exact circleAverageL2_ae_eq hc (0, s)
  | inr ψ => exact originLateralEvaluation_ae_eq_L2 X Xc hX hc hm ψ.val ψ.property


/-- The entire real radial coordinate family is independent of the lateral distribution. -/
theorem origin_radial_lateral_indepFun (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) :
    IndepFun (fun ω => fun s : ℝ => Xc ω 0 s)
      (fun ω => fun ψ : OriginLateralTest => originLateralEvaluation X Xc ψ.val ω) P := by
  apply (origin_radial_lateral_isGaussianProcess X Xc hX hc hm).indepFun_of_covariance_eq_zero
  · intro s
    exact (hc.2.1 0 s).aemeasurable
  · intro ψ
    exact (originLateralEvaluation_memLp X Xc hX hc hm ψ.val ψ.property).aemeasurable
  · intro s ψ
    exact originLateralEvaluation_circle_covariance_zero X Xc hX hc hm s ψ.val ψ.property

/-- Packing the actual radial path preserves its independence from all lateral test coordinates. -/
theorem originRadialPath_lateral_coordinates_indepFun
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IndepFun (fun ω => fun s : ℝ => originRadialPath Xc ω s)
      (fun ω => fun ψ : OriginLateralTest => originLateralEvaluation X Xc ψ.val ω) P := by
  apply (origin_radial_lateral_indepFun X Xc hX hc hm).congr
    _ EventuallyEq.rfl
  filter_upwards [originRadialPath_eval_ae hcont] with ω hω
  exact funext (fun s => (hω s).symm)

/-- Independence holds for the continuous-path carrier, with its evaluation-generated Borel
structure, rather than just for individual radial coordinates. -/
theorem originRadialPath_lateral_indepFun
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IndepFun (originRadialPath Xc)
      (fun ω => fun ψ : OriginLateralTest => originLateralEvaluation X Xc ψ.val ω) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ
  let _ := hDc.to_subtype
  let E : TwoSidedPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval (fun t => ContinuousMap.measurable_eval t.1)
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    exact congrFun (hDd.denseRange_val.equalizer p.continuous q.continuous hpq)
  have hEmb := hmE.measurableEmbedding hinj
  let restrict : (ℝ → ℝ) → (D → ℝ) := fun p t => p t.1
  have hrestrict : Measurable restrict := Measurable.of_eval (fun t => measurable_pi_apply t.1)
  have hi := (originRadialPath_lateral_coordinates_indepFun X Xc hX hc hm hcont).comp
    hrestrict measurable_id
  change IndepFun (E ∘ originRadialPath Xc)
    (fun ω => fun ψ : OriginLateralTest => originLateralEvaluation X Xc ψ.val ω) P at hi
  rw [IndepFun_iff_Indep, ← MeasurableSpace.comap_comp, hEmb.comap_eq] at hi
  exact (IndepFun_iff_Indep _ _ P).2 hi

/-- Orthogonality to all circle coordinates extends to the integrated radial projection. -/
theorem origin_lateral_radialIntegral_covariance_zero
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ψ χ : TestFn) (hψ : (0 : ℂ) ∉ tsupport ψ) (hχ : (0 : ℂ) ∉ tsupport χ) :
    covariance (lateralEvaluationL2 X Xc hX hc 0 ψ)
      (radialIntegralL2 X Xc hc 0 χ) P = 0 := by
  let _ := hX.1
  rw [covariance_comm, radialIntegralL2_covariance X Xc hX hc 0 χ hχ]
  have heq : (fun w : ℂ => χ w * covariance
      (circleAverageL2 hc (0, -Real.log ‖w - 0‖))
      (lateralEvaluationL2 X Xc hX hc 0 ψ) P) = fun _ => (0 : ℝ) := by
    funext w
    rw [covariance_congr_ae (circleAverageL2_ae_eq hc _)
      (originLateralEvaluation_ae_eq_L2 X Xc hX hc hm ψ hψ),
      originLateralEvaluation_circle_covariance_zero X Xc hX hc hm _ ψ hψ, mul_zero]
  rw [heq, integral_zero]




end

/-- The equator pin terms are the positive parts of the logarithmic radius. -/
theorem log_normPlus_eq_max_log {w : ℂ} (hw : w ≠ 0) :
    Real.log (normPlus w) = max 0 (Real.log ‖w‖) := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold normPlus
  rcases le_total 1 ‖w‖ with hn | hn
  · rw [max_eq_right hn, max_eq_right (Real.log_nonneg hn)]
  · rw [max_eq_left hn, Real.log_one, max_eq_left (Real.log_nonpos hnorm.le hn)]

/-- The radial covariance at two geometric radii, including radii outside the unit circle. -/
theorem originRadialCovariance_log_radius {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) :
    originRadialCovariance (-Real.log ‖w‖) v =
      -Real.log (max ‖w‖ ‖v‖) + Real.log (normPlus w) + Real.log (normPlus v) := by
  rw [originRadialCovariance, neg_neg,
    min_neg_log_eq_neg_log_max (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv),
    log_normPlus_eq_max_log hw, log_normPlus_eq_max_log hv]

/-- Subtracting the radial covariance cancels the two equator pin terms pointwise. -/
theorem origin_lateralKernel_cancellation {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) :
    gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v =
      -Real.log ‖w - v‖ + Real.log (max ‖w‖ ‖v‖) := by
  rw [originRadialCovariance_log_radius hw hv, gffKernel]
  ring

/-- The lateral kernel is a logarithm of the scale-free separation. -/
theorem origin_lateralKernel_normalized {w v : ℂ}
    (hw : w ≠ 0) (hv : v ≠ 0) (hsep : w ≠ v) :
    gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v =
      Real.log (max ‖w‖ ‖v‖ / ‖w - v‖) := by
  rw [origin_lateralKernel_cancellation hw hv,
    Real.log_div (ne_of_gt ((norm_pos_iff.mpr hw).trans_le (le_max_left _ _)))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep))]
  ring

/-- The scale-free separation is unchanged by any nonzero common complex dilation. -/
theorem origin_lateral_normalized_separation_dilation
    (c w v : ℂ) (hc : c ≠ 0) :
    max ‖c * w‖ ‖c * v‖ / ‖c * w - c * v‖ = max ‖w‖ ‖v‖ / ‖w - v‖ := by
  rw [← mul_sub, norm_mul, norm_mul, norm_mul,
    ← mul_max_of_nonneg _ _ (norm_nonneg c)]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc)

/-- Common plane dilation corresponds to real cylinder translation and rotation. The exact
lateral covariance is invariant, including across the equator. -/
theorem origin_lateralKernel_dilation
    (c w v : ℂ) (hc : c ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0) (hsep : w ≠ v) :
    gffKernel (c * w) (c * v) -
      originRadialCovariance (-Real.log ‖c * w‖) (c * v) =
        gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v := by
  have hsep' : c * w ≠ c * v := by
    intro h
    exact hsep (mul_left_cancel₀ hc h)
  rw [origin_lateralKernel_normalized (mul_ne_zero hc hw) (mul_ne_zero hc hv) hsep',
    origin_lateralKernel_normalized hw hv hsep,
    origin_lateral_normalized_separation_dilation c w v hc]



end DOZZ.Proofs
