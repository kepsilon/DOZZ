/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceCopiedPolarFinite
public import DOZZ.FourPoint.Dual.SourceCopiedKernelSqueeze
public import DOZZ.FourPoint.Dual.KernelInverseExpectation
public import DOZZ.FourPoint.Dual.CopiedInverseTriple
public import DOZZ.FourPoint.Dual.OuterInverseTransport
public import DOZZ.FourPoint.Dual.SourceRadialMoments
import Mathlib.Tactic
/-! The actual copied kernel inverse expectation is controlled by the same-source polar loss. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- All measurability, positivity, inverse integrability and polar finiteness inputs to the
copied-kernel relative error are discharged on the supplied source and common plane carrier. -/
theorem dual_source_copied_kernel_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (heN : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (heZ : Z =ᵐ[P] (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (α₁ α₂ α₃ ξ h p : ℝ) (hp : 0 < p) (hh : 0 < h)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hznorm : ‖z‖ ≤ 1)
    (hz : ‖z‖ < ‖z‖^(1-ξ)) (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h)
    (hη : Real.exp (-(T : ℝ)) < 1)
    (hr : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ))
    (hiZ : IndepFun (originRadialPath Xc) Z P)
    (B : Ω → BrownianPath × BrownianPath) (Z₀ : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z₀)
    (hlaw : P.map (fun ω => (originRadialPath Xc ω,dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)) =
      (P.prod P).map (fun ω : Ω × Ω => (originRadialPath Xc ω.1,
        ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))) :
    let A := originRadialPath Xc
    let η := Real.exp (-(T : ℝ))
    let R := Real.exp (-h)
    let θlo := (1-R)^(2 : ℝ)*(1-η)⁻¹^(-|γ*α₂|)
    let θhi := (1+R)^(2 : ℝ)*(1-η)⁻¹^|γ*α₂|
    let O := fun v : Ω × Ω => ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ (A v.1) x) ∂N v.2
    let D := ∫ v : (Ω × Ω) × Ω,
      ((O v.1).toReal+dualPathRadialScale γ (Q γ-α₁) h z (A v.1.1)*
        (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
          (brownianShiftPath T (radialPositiveHalf (A v.1.1)) (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
            ∂(Z v.2).map (fun s => s-(T : ℝ))).toReal)^(-p)-(O v.1).toReal^(-p)
        ∂(P.prod P).prod P
    |(dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ p z η (‖z‖^(1-ξ))).toReal-
      (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal-D| ≤
      max |θlo-1| |θhi-1| * (-D) := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let η := Real.exp (-(T : ℝ))
  let R := Real.exp (-h)
  let θlo := (1-R)^(2 : ℝ)*(1-η)⁻¹^(-|γ*α₂|)
  let θhi := (1+R)^(2 : ℝ)*(1-η)⁻¹^|γ*α₂|
  let J := fun U (a : TwoSidedPath) ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
  let O₀ := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let O := fun v : Ω × Ω => J (reflected_outerRegion (‖z‖^(1-ξ))) (A v.1) v.2
  let I := fun v : (Ω × Ω) × Ω => J (reflected_innerRegion η) (A v.1.1) v.2
  let β := fun v : (Ω × Ω) × Ω => dualPathRadialScale γ (Q γ-α₁) h z (A v.1.1)
  let V := fun v : (Ω × Ω) × Ω => ∫⁻ t,
    (if 0 < t then ENNReal.ofReal (Real.exp (γ*
      (brownianShiftPath T (radialPositiveHalf (A v.1.1)) (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
        ∂(Z v.2).map (fun s => s-(T : ℝ))
  let QP := (P.prod P).prod P
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hmRegion (U : Set ℂ) (hU : IsOpen U) (hU0 : U ⊆ ({0} : Set ℂ)ᶜ) :
      Measurable (fun v : TwoSidedPath × Ω => J U v.1 v.2) :=
    reflected_chart_parameter_mass_measurable U hU N hNm
      (fun ω K hK hKU => hfin ω K hK (hKU.trans hU0))
      (fun v : TwoSidedPath × ℂ => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z v.2)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ v.1 v.2))
      (((dual_kernel_measurable γ α₁ α₂ α₃ z).comp measurable_snd).ennreal_ofReal.mul
        (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal)
  have hi : Measurable (fun v : TwoSidedPath × Ω => J (reflected_innerRegion η) v.1 v.2) := by
    apply hmRegion _ ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
    intro x hx hx0
    have he : x = 0 := mem_singleton_iff.mp hx0
    have hxpos : 0 < ‖x‖ := hx.1
    simp only [he, norm_zero, lt_self_iff_false] at hxpos
  have ho : Measurable (fun v : TwoSidedPath × Ω => J (reflected_outerRegion (‖z‖^(1-ξ))) v.1 v.2) := by
    apply hmRegion _ ((isOpen_lt continuous_const continuous_norm).inter
      (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl)
    intro x hx hx0
    have he : x = 0 := mem_singleton_iff.mp hx0
    exact hx.2 (by simp [he])
  have hOm : AEMeasurable O (P.prod P) :=
    ho.comp_aemeasurable (hA.comp_fst.prodMk measurable_snd.aemeasurable)
  have hIm : AEMeasurable I QP := hi.comp_aemeasurable
    (hA.comp_fst.comp_fst.prodMk measurable_snd.aemeasurable)
  have hβm : AEMeasurable β QP :=
    (dual_path_radial_scale_measurable γ (Q γ-α₁) h z).comp_aemeasurable hA.comp_fst.comp_fst
  have hβpos : ∀ᵐ v ∂QP, 0 ≤ β v := ae_of_all _ (fun v => (Real.exp_pos _).le)
  have hO₀m : AEMeasurable O₀ P := (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hrnorm : ‖z‖^(1-ξ) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hznorm
      (sub_nonneg.mpr hξ1.le)
  have hO₀pos : ∀ᵐ ω ∂P, 0 < (O₀ ω).toReal :=
    (dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hznorm hrnorm).mono
      (fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne)
  have hO₀int : Integrable (fun ω => (O₀ ω).toReal^(-p)) P := by
    have ht := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
      (Q γ-α₁) h 0 α₁ α₂ α₃ ξ p hh.le hξ hξ1 hp.le z hz0 hznorm).1
    simpa only [Real.rpow_zero, one_mul] using ht
  have hdata := dual_joint_law_outer_inverse_data P (P.prod P) A (fun v => A v.1) O₀ O
    hA hA.comp_fst hO₀m hOm hlaw p hO₀pos hO₀int
  have hOpos : ∀ᵐ v ∂QP, 0 < (O v.1).toReal :=
    measurePreserving_fst.quasiMeasurePreserving.ae hdata.1
  obtain ⟨C, _, hC⟩ := dual_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ p hp.le
  have hInv₀ : (∫⁻ ω, O₀ ω^(-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hC z ξ hznorm hrnorm)
  have hInvEq := dual_joint_law_outer_inverse_lintegral P (P.prod P) A (fun v => A v.1)
    O₀ O hA hA.comp_fst hO₀m hOm hlaw p
  have hInv : (∫⁻ v : (Ω × Ω) × Ω, O v.1^(-p) ∂QP) ≠ ⊤ := by
    rw [lintegral_prod _ (hOm.comp_fst.pow_const (-p))]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [← hInvEq]
    exact hInv₀
  let ZT := fun ω => (Z ω).map (fun s : ℝ => s-(T : ℝ))
  have hZT : AEMeasurable ZT P := (Measure.measurable_map _ (measurable_id.sub_const _)).comp_aemeasurable hZ.2.2.2.1
  have hZTfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, ZT ω (Icc a b) < ⊤ := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω a b
    have he : (fun s : ℝ => s-(T : ℝ)) ⁻¹' Icc a b = Icc (a+T) (b+T) := by
      ext s
      simp only [mem_preimage, mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add]
    change (Z ω).map (fun s : ℝ => s-(T : ℝ)) (Icc a b) < ⊤
    rw [Measure.map_apply (show Measurable (fun s : ℝ => s-(T : ℝ)) from measurable_id.sub_const _)
      measurableSet_Icc, he]
    exact hω _ _
  have hDm : Measurable (fun a : TwoSidedPath => brownianShiftPath T (radialPositiveHalf a)) :=
    continuous_brownianShiftPath.measurable.comp
      (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hVm : AEMeasurable V QP := by
    have hDp : AEMeasurable (fun v : (Ω × Ω) × Ω =>
        brownianShiftPath T (radialPositiveHalf (A v.1.1))) QP :=
      hDm.comp_aemeasurable hA.comp_fst.comp_fst
    have hZTp : AEMeasurable (fun v : (Ω × Ω) × Ω => ZT v.2) QP := hZT.comp_snd
    have ht := (reflected_measurable_inwardPolarMassCode γ (Q γ-α₁)).comp_aemeasurable
      (hDp.prodMk hZTp)
    apply ht.congr
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hZTfin] with v hv
    exact reflected_inwardPolarMassCode_eq γ (Q γ-α₁)
      (brownianShiftPath T (radialPositiveHalf (A v.1.1))) (ZT v.2) hv
  have hVfin : ∀ᵐ v ∂QP, V v ≠ ⊤ := dual_source_copied_polar_finite_ae
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM N hNm hfin Z hZ α₁ α₂ α₃ ξ h hα₁
    z hz0 hz T hT hr hiZ B Z₀ hData hlaw
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR1 : R < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hh)
  have hηEq : η = R*‖z‖ := by
    dsimp only [η, R]
    rw [hT]
    have he : -(-Real.log ‖z‖+h) = -h+Real.log ‖z‖ := by ring
    rw [he, Real.exp_add, Real.exp_log (norm_pos_iff.mpr hz0)]
  have hθlo : 0 ≤ θlo := mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hR1.le) _)
    (Real.rpow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hη.le)) _)
  have hθhi : 0 ≤ θhi := mul_nonneg (Real.rpow_nonneg (by linarith only [hR0]) _)
    (Real.rpow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hη.le)) _)
  have hs : ∀ᵐ v ∂QP, ENNReal.ofReal (θlo*β v)*V v ≤ I v ∧ I v ≤ ENNReal.ofReal (θhi*β v)*V v := by
    have ht := dual_source_copied_inner_kernel_squeeze P γ α₁ α₂ α₃ h R hγ.ne'
      A M N Z heN heZ z hz0 T hT hR0 hR1 hη hηEq.le
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae ht] with v hv
    exact hv (A v.1.1)
  have hb := dual_ennreal_kernel_inverse_expectation_error QP (fun v => O v.1) I V β p θlo θhi
    hp hθlo hθhi hOm.comp_fst hIm hVm hβm hβpos hOpos hVfin hInv hs
  have hCopy := dual_copied_inverse_moment_triple P Xc hA N hNm hfin γ α₁ α₂ α₃ p η (‖z‖^(1-ξ)) z
  have hCopy' : dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ p z η (‖z‖^(1-ξ)) =
      ∫⁻ v : (Ω × Ω) × Ω, (O v.1+I v)^(-p) ∂QP := by
    rw [hCopy]
    apply lintegral_congr
    intro v
    exact congrArg (fun a : ℝ≥0∞ => a^(-p)) (add_comm _ _)
  have hInvEq' : (∫⁻ v : (Ω × Ω) × Ω, O v.1^(-p) ∂QP) = ∫⁻ ω, O₀ ω^(-p) ∂P := by
    rw [lintegral_prod _ (hOm.comp_fst.pow_const (-p))]
    simp only [lintegral_const, measure_univ, mul_one]
    exact hInvEq.symm
  rw [← hCopy', hInvEq'] at hb
  have hLoss : (∫ v : (Ω × Ω) × Ω, (O v.1).toReal^(-p)-
      ((O v.1).toReal+β v*(V v).toReal)^(-p) ∂QP) =
      -(∫ v : (Ω × Ω) × Ω, ((O v.1).toReal+β v*(V v).toReal)^(-p)-
        (O v.1).toReal^(-p) ∂QP) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by ring)
  rw [hLoss] at hb
  exact hb

end DOZZ.Proofs
