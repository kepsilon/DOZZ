/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterPicardTerms
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Recursive parameter derivatives of Picard summands and their spatial continuity. -/

@[expose] public section

open MeasureTheory Set
open scoped Interval Topology

namespace DOZZ.Proofs

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The recursive candidate for the parameter derivative of a Picard summand. -/
noncomputable def parameterizedPicardTermParamFDeriv (c : ℂ)
    (A : P → ℂ → E →L[ℂ] E)
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (y : P → E) (Dy : P → P →L[ℂ] E) : ℕ → P → ℂ → P →L[ℂ] E
  | 0 => fun p _ => Dy p
  | n + 1 => fun p z =>
      letI : NormedSpace ℝ (P →L[ℂ] E) := NormedSpace.restrictScalars ℝ ℂ _
      ∫ t in (0 : ℝ)..1,
        (z - c) •
          ((A p (AffineMap.lineMap c z t)).comp
              (parameterizedPicardTermParamFDeriv c A DA y Dy n p
                (AffineMap.lineMap c z t)) +
            (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
              (parameterizedPicardTerm c A y n p (AffineMap.lineMap c z t))).comp
                (DA p (AffineMap.lineMap c z t)))

private theorem eval_comp_eq_flip {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : P →L[ℂ] (E →L[ℂ] E)) (v : E) :
    (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E) v).comp K = K.flip v := by
  ext p
  rfl

private def clipUnitInterval (t : ℝ) : ℝ := min 1 (max 0 t)

private theorem clipUnitInterval_mem (t : ℝ) : clipUnitInterval t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min zero_le_one (le_max_left 0 t)
  · exact min_le_left _ _

private theorem clipUnitInterval_eq_of_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    clipUnitInterval t = t := by
  simp [clipUnitInterval, max_eq_right (le_of_lt ht.1), min_eq_right ht.2]

private theorem clipUnitInterval_eq_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    clipUnitInterval t = t := by
  simp [clipUnitInterval, max_eq_right ht.1, min_eq_right ht.2]

/-- Each recursively defined parameter-derivative summand is continuous in the spatial variable
on a Picard disk, provided the coefficient's parameter derivative is spatially continuous there.
The integral is extended continuously off its unit segment by clamping the segment parameter. -/
theorem parameterizedPicardTermParamFDeriv_continuousOn
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ p, DifferentiableOn ℂ (A p) (Metric.ball c r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ p, ContinuousOn (DA p) (Metric.ball c r))
    (y : P → E) (Dy : P → P →L[ℂ] E) :
    ∀ n p, ContinuousOn (parameterizedPicardTermParamFDeriv c A DA y Dy n p)
      (Metric.ball c r) := by
  intro n
  induction n with
  | zero =>
      intro p
      exact continuousOn_const
  | succ n ih =>
      intro p
      let X := {z : ℂ // z ∈ Metric.ball c r}
      let W : X × ℝ → ℂ := fun u =>
        AffineMap.lineMap c (u.1 : ℂ) (clipUnitInterval u.2)
      let G : X × ℝ → P →L[ℂ] E := fun u =>
        ((u.1 : ℂ) - c) •
          ((A p (W u)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n p (W u)) +
            (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
              (parameterizedPicardTerm c A y n p (W u))).comp (DA p (W u)))
      have hclip : ∀ u : X × ℝ, W u ∈ Metric.ball c r := by
        intro u
        have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
        exact (convex_ball c r).mapsTo_lineMap hc u.1.2 (clipUnitInterval_mem u.2)
      have hclipMap : MapsTo W univ (Metric.ball c r) := fun u _ => hclip u
      have hw : Continuous W := by
        have hfst : Continuous (fun u : X × ℝ => (u.1 : ℂ)) :=
          continuous_subtype_val.comp continuous_fst
        have hclipcont : Continuous (fun u : X × ℝ => clipUnitInterval u.2) := by
          fun_prop [clipUnitInterval]
        exact Continuous.lineMap continuous_const hfst hclipcont
      have hAcomp : Continuous (fun u : X × ℝ => A p (W u)) := by
        rw [← continuousOn_univ]
        exact (hA p).continuousOn.comp hw.continuousOn hclipMap
      have hDAcomp : Continuous (fun u : X × ℝ => DA p (W u)) := by
        rw [← continuousOn_univ]
        exact (hDA p).comp hw.continuousOn hclipMap
      have hT : ContinuousOn (parameterizedPicardTerm c A y n p) (Metric.ball c r) := by
        apply (holomorphicPicardTerm_differentiableOn c r (A p) (hA p) (y p) n).continuousOn.congr
        intro z hz
        exact parameterizedPicardTerm_eq_holomorphicPicardTerm c r A hA y n p z hz
      have hTcomp : Continuous (fun u : X × ℝ =>
          parameterizedPicardTerm c A y n p (W u)) := by
        rw [← continuousOn_univ]
        exact hT.comp hw.continuousOn hclipMap
      have hDcomp : Continuous (fun u : X × ℝ =>
          parameterizedPicardTermParamFDeriv c A DA y Dy n p (W u)) := by
        rw [← continuousOn_univ]
        exact (ih p).comp hw.continuousOn hclipMap
      have hComp : Continuous (fun u : X × ℝ =>
          (A p (W u)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n p (W u))) := by
        exact hAcomp.clm_comp hDcomp
      have hEval : Continuous (fun u : X × ℝ =>
          ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
            (parameterizedPicardTerm c A y n p (W u))) := by
        exact (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)).continuous.comp hTcomp
      have hFlip : Continuous (fun u : X × ℝ =>
          (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
            (parameterizedPicardTerm c A y n p (W u))).comp (DA p (W u))) :=
        hEval.clm_comp hDAcomp
      have hScalar : Continuous (fun u : X × ℝ => (u.1 : ℂ) - c) := by
        exact (continuous_subtype_val.comp continuous_fst).sub continuous_const
      have hSum : Continuous (fun u : X × ℝ =>
          (A p (W u)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n p (W u)) +
            (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
              (parameterizedPicardTerm c A y n p (W u))).comp (DA p (W u))) := hComp.add hFlip
      have hG : Continuous G := by
        exact hScalar.smul hSum
      let : LocallyCompactSpace X := Metric.isOpen_ball.locallyCompactSpace
      have hInt : Continuous (fun z : X => ∫ t in Icc (0 : ℝ) 1, G (z, t) ∂volume) :=
        continuous_parametric_integral_of_continuous hG isCompact_Icc
      have hEq : ∀ z : X,
          parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) p (z : ℂ) =
            ∫ t in Icc (0 : ℝ) 1, G (z, t) ∂volume := by
        intro z
        simp only [parameterizedPicardTermParamFDeriv]
        rw [intervalIntegral.integral_of_le zero_le_one]
        rw [← integral_Icc_eq_integral_Ioc]
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        simp [G, W, clipUnitInterval_eq_of_mem_Icc ht]
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (fun z : X =>
        parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) p (z : ℂ))
      rw [show (fun z : X => parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) p (z : ℂ)) =
        (fun z : X => ∫ t in Icc (0 : ℝ) 1, G (z, t) ∂volume) from funext hEq]
      exact hInt

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
private theorem parameterizedPicardTerm_continuousOn
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ p, DifferentiableOn ℂ (A p) (Metric.ball c r))
    (y : P → E) (n : ℕ) (p : P) :
    ContinuousOn (parameterizedPicardTerm c A y n p) (Metric.ball c r) := by
  apply (holomorphicPicardTerm_differentiableOn c r (A p) (hA p) (y p) n).continuousOn.congr
  intro z hz
  exact parameterizedPicardTerm_eq_holomorphicPicardTerm c r A hA y n p z hz

/-- On a Picard disk, spatial continuity of the coefficients and recursive derivative candidates
automatically supplies the measurability and integrability hypotheses for differentiating the next
Picard term. -/
theorem parameterizedPicardTerm_succ_hasFDerivAt_of_continuous
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ q, ContinuousOn (DA q) (Metric.ball c r))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (n : ℕ) (p : P) (s : Set P) (hs : s ∈ 𝓝 p)
    (M L Y D : ℝ)
    (hAderiv : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hTderiv : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => parameterizedPicardTerm c A y n q' w)
        (parameterizedPicardTermParamFDeriv c A DA y Dy n q w) q)
    (hT_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTerm c A y n q w‖ ≤ Y)
    (hDT_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q w‖ ≤ D)
    {z : ℂ} (hz : z ∈ Metric.ball c r) :
    HasFDerivAt (fun q => parameterizedPicardTerm c A y (n + 1) q z)
      (parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) p z) p := by
  let w : ℝ → ℂ := AffineMap.lineMap c z
  have hcenter : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hseg : MapsTo w (Icc (0 : ℝ) 1) (Metric.ball c r) :=
    (convex_ball c r).mapsTo_lineMap hcenter hz
  have hwcont : ContinuousOn w (Icc (0 : ℝ) 1) :=
    AffineMap.lineMap_continuous.continuousOn
  have hAcont (q : P) : ContinuousOn (fun t : ℝ => A q (w t)) (Icc (0 : ℝ) 1) :=
    (hA q).continuousOn.comp hwcont (fun t ht => hseg ht)
  have hTcont (q : P) : ContinuousOn
      (fun t : ℝ => parameterizedPicardTerm c A y n q (w t)) (Icc (0 : ℝ) 1) := by
    exact (parameterizedPicardTerm_continuousOn c r A hA y n q).comp hwcont
      (fun t ht => hseg ht)
  have hFcont (q : P) : ContinuousOn
      (fun t : ℝ => (z - c) • A q (w t)
        (parameterizedPicardTerm c A y n q (w t))) (Icc (0 : ℝ) 1) := by
    exact (hAcont q).clm_apply (hTcont q) |>.const_smul (z - c)
  have hDAcont (q : P) : ContinuousOn (fun t : ℝ => DA q (w t))
      (Icc (0 : ℝ) 1) := (hDA q).comp hwcont (fun t ht => hseg ht)
  have hDTcont (q : P) : ContinuousOn
      (fun t : ℝ => parameterizedPicardTermParamFDeriv c A DA y Dy n q (w t))
      (Icc (0 : ℝ) 1) :=
    (parameterizedPicardTermParamFDeriv_continuousOn c r hr A hA DA hDA y Dy n q).comp
      hwcont (fun t ht => hseg ht)
  have hF'cont_alt (q : P) : ContinuousOn
      (fun t : ℝ => (z - c) •
        ((A q (w t)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n q (w t)) +
          (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
            (parameterizedPicardTerm c A y n q (w t))).comp (DA q (w t))))
      (Icc (0 : ℝ) 1) := by
    have hcomp := (hAcont q).clm_comp (hDTcont q)
    have heval : ContinuousOn (fun t : ℝ =>
        ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
          (parameterizedPicardTerm c A y n q (w t))) (Icc (0 : ℝ) 1) :=
      (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)).continuous.comp_continuousOn
        (hTcont q)
    have hsecond := heval.clm_comp (hDAcont q)
    exact (hcomp.add hsecond).const_smul (z - c)
  have hF'cont (q : P) : ContinuousOn
      (fun t : ℝ => (z - c) •
        ((A q (w t)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n q (w t)) +
          (DA q (w t)).flip (parameterizedPicardTerm c A y n q (w t))))
      (Icc (0 : ℝ) 1) := by
    apply (hF'cont_alt q).congr
    intro t ht
    simp only [eval_comp_eq_flip]
  have hF_meas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable (fun t : ℝ => (z - c) • A q (w t)
        (parameterizedPicardTerm c A y n q (w t)))
        (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [hs] with q hq
    have hmeas := (hFcont q).aestronglyMeasurable_of_subset_isCompact (μ := volume) isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
    simpa [uIoc_of_le zero_le_one] using hmeas
  have hF_int : IntervalIntegrable (fun t : ℝ => (z - c) • A p (w t)
      (parameterizedPicardTerm c A y n p (w t))) volume 0 1 :=
    (hFcont p).intervalIntegrable_of_Icc zero_le_one
  have hFderiv_meas : AEStronglyMeasurable
      (fun t : ℝ => (z - c) •
        ((A p (w t)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n p (w t)) +
          (DA p (w t)).flip (parameterizedPicardTerm c A y n p (w t))))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hmeas := (hF'cont p).aestronglyMeasurable_of_subset_isCompact (μ := volume) isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
    simpa [uIoc_of_le zero_le_one] using hmeas
  have hAderiv' : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun q' => A q' (w t)) (DA q (w t)) q := by
    intro q hq t ht
    exact hAderiv q hq (w t) (hseg ht)
  have hA_bound' : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖A q (w t)‖ ≤ M := by
    intro q hq t ht
    exact hA_bound q hq (w t) (hseg ht)
  have hDA_bound' : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖DA q (w t)‖ ≤ L := by
    intro q hq t ht
    exact hDA_bound q hq (w t) (hseg ht)
  have hTderiv' : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun q' => parameterizedPicardTerm c A y n q' (w t))
        (parameterizedPicardTermParamFDeriv c A DA y Dy n q (w t)) q := by
    intro q hq t ht
    exact hTderiv q hq (w t) (hseg ht)
  have hT_bound' : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parameterizedPicardTerm c A y n q (w t)‖ ≤ Y := by
    intro q hq t ht
    exact hT_bound q hq (w t) (hseg ht)
  have hDT_bound' : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q (w t)‖ ≤ D := by
    intro q hq t ht
    exact hDT_bound q hq (w t) (hseg ht)
  have hresult := parameterizedPicardTerm_succ_hasFDerivAt_of_bounds c z A DA y
    (parameterizedPicardTermParamFDeriv c A DA y Dy n) n p s hs M L Y D
    hAderiv' hA_bound' hDA_bound' hTderiv' hT_bound' hDT_bound'
    hF_meas hF_int hFderiv_meas
  have heq : (∫ t in (0 : ℝ)..1, (z - c) •
      ((A p (w t)).comp (parameterizedPicardTermParamFDeriv c A DA y Dy n p (w t)) +
        (DA p (w t)).flip (parameterizedPicardTerm c A y n p (w t)))) =
      parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) p z := by
    simp [parameterizedPicardTermParamFDeriv, w, eval_comp_eq_flip]
  rw [heq] at hresult
  exact hresult

/-- Uniform bounds on a Picard summand and its derivative candidate give the corresponding bound
for the next recursive derivative candidate. -/
theorem parameterizedPicardTermParamFDeriv_norm_le_succ
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (A : P → ℂ → E →L[ℂ] E)
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (n : ℕ) (s : Set P) (M L Y D : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hT_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTerm c A y n q w‖ ≤ Y)
    (hDT_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q w‖ ≤ D) :
    ∀ q ∈ s, ∀ z ∈ Metric.ball c r,
      ‖parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) q z‖ ≤
        r * (M * D + L * Y) := by
  intro q hq z hz
  have hcenter : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hseg : MapsTo (AffineMap.lineMap c z) (Icc (0 : ℝ) 1) (Metric.ball c r) :=
    (convex_ball c r).mapsTo_lineMap hcenter hz
  change ‖∫ t in (0 : ℝ)..1, (z - c) •
      ((A q (AffineMap.lineMap c z t)).comp
          (parameterizedPicardTermParamFDeriv c A DA y Dy n q
            (AffineMap.lineMap c z t)) +
        (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
          (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t))).comp
          (DA q (AffineMap.lineMap c z t)))‖ ≤ _
  calc
    ‖∫ t in (0 : ℝ)..1, (z - c) •
        ((A q (AffineMap.lineMap c z t)).comp
            (parameterizedPicardTermParamFDeriv c A DA y Dy n q
              (AffineMap.lineMap c z t)) +
          (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
            (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t))).comp
            (DA q (AffineMap.lineMap c z t)))‖ ≤
        (r * (M * D + L * Y)) * |(1 : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
        simpa [uIoc_of_le zero_le_one] using ht
      have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
      have hw : AffineMap.lineMap c z t ∈ Metric.ball c r := hseg htcc
      have hpoint := norm_parameterizedPicardIntegrand_zero_fderiv_le c z
        (AffineMap.lineMap c z t) A
        (fun q' => parameterizedPicardTerm c A y n q'
          (AffineMap.lineMap c z t)) q
        (DA q (AffineMap.lineMap c z t))
        (parameterizedPicardTermParamFDeriv c A DA y Dy n q
          (AffineMap.lineMap c z t))
        M L Y D (hA_bound q hq _ hw) (hDA_bound q hq _ hw)
        (hT_bound q hq _ hw) (hDT_bound q hq _ hw)
      have hpoint' : ‖(z - c) •
          ((A q (AffineMap.lineMap c z t)).comp
              (parameterizedPicardTermParamFDeriv c A DA y Dy n q
                (AffineMap.lineMap c z t)) +
            (ContinuousLinearMap.apply ℂ (E := E) (Fₗ := E)
              (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t))).comp
              (DA q (AffineMap.lineMap c z t)))‖ ≤
          ‖z - c‖ * (M * D + L * Y) := by
        simpa only [eval_comp_eq_flip] using hpoint
      have hdist : ‖z - c‖ ≤ r := by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hz).le
      exact hpoint'.trans (mul_le_mul_of_nonneg_right hdist
        (add_nonneg (mul_nonneg hM hD) (mul_nonneg hL hY)))
    _ = r * (M * D + L * Y) := by norm_num

/-- A strict geometric majorant for the recursive parameter-derivative terms follows from the
one-step norm recurrence whenever the disk radius contracts that majorant. -/
theorem parameterizedPicardTermParamFDeriv_norm_le_of_geometric
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (A : P → ℂ → E →L[ℂ] E)
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (s : Set P) (M L Y D ρ : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D) (hρ : 0 ≤ ρ)
    (hcontract : r * (M * D + L * Y) ≤ D * ρ)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hvalue_bound : ∀ n, ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTerm c A y n q w‖ ≤ Y * ρ ^ n)
    (hDy_bound : ∀ q ∈ s, ‖Dy q‖ ≤ D) :
    ∀ n, ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q w‖ ≤ D * ρ ^ n := by
  intro n
  induction n with
  | zero =>
      intro q hq w hw
      simpa [parameterizedPicardTermParamFDeriv] using hDy_bound q hq
  | succ n ih =>
      intro q hq z hz
      have hnext := parameterizedPicardTermParamFDeriv_norm_le_succ
        c r hr A DA y Dy n s M L (Y * ρ ^ n) (D * ρ ^ n)
        hM hL (mul_nonneg hY (pow_nonneg hρ n))
        (mul_nonneg hD (pow_nonneg hρ n))
        hA_bound hDA_bound
        (fun q' hq' w hw => hvalue_bound n q' hq' w hw)
        (fun q' hq' w hw => ih q' hq' w hw)
      calc
        ‖parameterizedPicardTermParamFDeriv c A DA y Dy (n + 1) q z‖ ≤
            r * (M * (D * ρ ^ n) + L * (Y * ρ ^ n)) := hnext q hq z hz
        _ = (r * (M * D + L * Y)) * ρ ^ n := by ring
        _ ≤ (D * ρ) * ρ ^ n :=
          mul_le_mul_of_nonneg_right hcontract (pow_nonneg hρ n)
        _ = D * ρ ^ (n + 1) := by rw [pow_succ]; ring

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
/-- The factorial Picard bound is dominated by a geometric value bound on any disk whose
coefficient-radius product is below the chosen ratio. -/
lemma parameterizedPicardTerm_norm_le_of_geometric
    [CompleteSpace E]
    (c : ℂ) (r M Y ρ : ℝ) (K : Set P)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r))
    (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hMr : M * r ≤ ρ)
    (hA_bound : ∀ q ∈ K, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (y : P → E) (hy : ∀ q ∈ K, ‖y q‖ ≤ Y) :
    ∀ n, ∀ q ∈ K, ∀ z ∈ Metric.ball c r,
      ‖parameterizedPicardTerm c A y n q z‖ ≤ Y * ρ ^ n := by
  intro n q hq z hz
  have hfacNat : 1 ≤ n.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast hfacNat
  have hquot : (M * r) ^ n / (n.factorial : ℝ) ≤ ρ ^ n := by
    have hMr0 : 0 ≤ M * r := mul_nonneg hM hr
    have hpow : (M * r) ^ n ≤ ρ ^ n := by gcongr
    have hpow0 : 0 ≤ (M * r) ^ n := pow_nonneg hMr0 n
    calc
      (M * r) ^ n / (n.factorial : ℝ) ≤ (M * r) ^ n := by
        apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)).2
        calc
          (M * r) ^ n = (M * r) ^ n * 1 := by ring
          _ ≤ (M * r) ^ n * (n.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left hfac hpow0
      _ ≤ ρ ^ n := hpow
  have hterm := parameterizedPicardTerm_norm_le_of_uniform_bounds
    c r M Y K A hA hM hA_bound y hy n q z hq hz
  have hYq : 0 ≤ Y := le_trans (norm_nonneg (y q)) (hy q hq)
  calc
    ‖parameterizedPicardTerm c A y n q z‖ ≤
        Y * (M * max r 0) ^ n / (n.factorial : ℝ) := hterm
    _ = Y * ((M * r) ^ n / (n.factorial : ℝ)) := by rw [max_eq_left hr]; ring
    _ ≤ Y * ρ ^ n := mul_le_mul_of_nonneg_left hquot hYq

/-- Induction propagates parameter differentiability from the initial vector through every Picard
summand, once the value and candidate-derivative summands have common local majorants. -/
theorem parameterizedPicardTerm_hasFDerivAt_of_local_bounds
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ q, ContinuousOn (DA q) (Metric.ball c r))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (s : Set P) (hs_open : IsOpen s)
    (M L : ℝ) (v d : ℕ → ℝ)
    (hAderiv : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hyderiv : ∀ q ∈ s, HasFDerivAt y (Dy q) q)
    (hvalue_bound : ∀ n, ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTerm c A y n q w‖ ≤ v n)
    (hderiv_bound : ∀ n, ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q w‖ ≤ d n) :
    ∀ n, ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => parameterizedPicardTerm c A y n q' w)
        (parameterizedPicardTermParamFDeriv c A DA y Dy n q w) q := by
  intro n
  induction n with
  | zero =>
      intro q hq w hw
      simpa [parameterizedPicardTerm, parameterizedPicardTermParamFDeriv] using
        hyderiv q hq
  | succ n ih =>
      intro q hq z hz
      exact parameterizedPicardTerm_succ_hasFDerivAt_of_continuous
        c r hr A hA DA hDA y Dy n q s (hs_open.mem_nhds hq) M L (v n) (d n)
        hAderiv hA_bound hDA_bound
        (fun q' hq' w hw => ih q' hq' w hw)
        (fun q' hq' w hw => hvalue_bound n q' hq' w hw)
        (fun q' hq' w hw => hderiv_bound n q' hq' w hw)
        hz

/-- Geometric value and derivative-candidate majorants imply parameter differentiability of every
Picard summand on the common open parameter region. -/
theorem parameterizedPicardTerm_hasFDerivAt_of_geometric_bounds
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (hr : 0 < r) (s : Set P) (hs : IsOpen s)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ q, ContinuousOn (DA q) (Metric.ball c r))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (M L Y D ρ : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D) (hρ : 0 ≤ ρ)
    (hMr : M * r ≤ ρ)
    (hcontract : r * (M * D + L * Y) ≤ D * ρ)
    (hAderiv : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hyderiv : ∀ q ∈ s, HasFDerivAt y (Dy q) q)
    (hy_bound : ∀ q ∈ s, ‖y q‖ ≤ Y)
    (hDy_bound : ∀ q ∈ s, ‖Dy q‖ ≤ D) :
    ∀ n, ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => parameterizedPicardTerm c A y n q' w)
        (parameterizedPicardTermParamFDeriv c A DA y Dy n q w) q := by
  have hvalue := parameterizedPicardTerm_norm_le_of_geometric
    c r M Y ρ s A hA hM (le_of_lt hr) hMr hA_bound y hy_bound
  have hderiv := parameterizedPicardTermParamFDeriv_norm_le_of_geometric
    c r hr A DA y Dy s M L Y D ρ hM hL hY hD hρ hcontract
    hA_bound hDA_bound hvalue hDy_bound
  exact parameterizedPicardTerm_hasFDerivAt_of_local_bounds
    c r hr A hA DA hDA y Dy s hs M L (fun n => Y * ρ ^ n)
      (fun n => D * ρ ^ n) hAderiv hA_bound hDA_bound hyderiv hvalue hderiv

/-- The parameterized Picard series is Fréchet differentiable on an open preconnected parameter
region when its summands and their derivative candidates share a strict geometric majorant. -/
theorem parameterizedPicardSeries_hasFDerivAt_of_geometric_bounds
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (hr : 0 < r) (s : Set P) (hs : IsOpen s) (hsconn : IsPreconnected s)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ q, ContinuousOn (DA q) (Metric.ball c r))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (M L Y D ρ : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D) (hρ : 0 ≤ ρ)
    (hρlt : ρ < 1)
    (hMr : M * r ≤ ρ)
    (hcontract : r * (M * D + L * Y) ≤ D * ρ)
    (hAderiv : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hyderiv : ∀ q ∈ s, HasFDerivAt y (Dy q) q)
    (hy_bound : ∀ q ∈ s, ‖y q‖ ≤ Y)
    (hDy_bound : ∀ q ∈ s, ‖Dy q‖ ≤ D)
    {q₀ q : P} (hq₀ : q₀ ∈ s) (hq : q ∈ s) {z : ℂ}
    (hz : z ∈ Metric.ball c r) :
    HasFDerivAt
      (fun p => ∑' n, parameterizedPicardTerm c A y n p z)
      (∑' n, parameterizedPicardTermParamFDeriv c A DA y Dy n q z) q := by
  have htermDiff := parameterizedPicardTerm_hasFDerivAt_of_geometric_bounds
    c r hr s hs A hA DA hDA y Dy M L Y D ρ hM hL hY hD hρ hMr hcontract
    hAderiv hA_bound hDA_bound hyderiv hy_bound hDy_bound
  have hderivBound := parameterizedPicardTermParamFDeriv_norm_le_of_geometric
    c r hr A DA y Dy s M L Y D ρ hM hL hY hD hρ hcontract
    hA_bound hDA_bound
    (parameterizedPicardTerm_norm_le_of_geometric c r M Y ρ s A hA hM
      (le_of_lt hr) hMr hA_bound y hy_bound)
    hDy_bound
  let u : ℕ → ℝ := fun n => D * ρ ^ n
  let v : ℕ → ℝ := fun n => Y * ρ ^ n
  have hu : Summable u := by
    dsimp [u]
    exact (summable_geometric_of_lt_one hρ hρlt).mul_left D
  have hv : Summable v := by
    dsimp [v]
    exact (summable_geometric_of_lt_one hρ hρlt).mul_left Y
  let F : ℕ → P → E := fun n p => parameterizedPicardTerm c A y n p z
  let F' : ℕ → P → P →L[ℂ] E := fun n p =>
    parameterizedPicardTermParamFDeriv c A DA y Dy n p z
  have hFderiv : ∀ n p, p ∈ s → HasFDerivAt (F n) (F' n p) p := by
    intro n p hp
    exact htermDiff n p hp z hz
  have hFbound : ∀ n p, p ∈ s → ‖F' n p‖ ≤ u n := by
    intro n p hp
    simpa [F', u] using hderivBound n p hp z hz
  have hFsum : Summable (fun n => F n q₀) := by
    apply hv.of_norm_bounded
    intro n
    simpa [F, v] using
      parameterizedPicardTerm_norm_le_of_geometric c r M Y ρ s A hA hM
        (le_of_lt hr) hMr hA_bound y hy_bound n q₀ hq₀ z hz
  exact hasFDerivAt_tsum_of_isPreconnected hu hs hsconn hFderiv hFbound hq₀ hFsum hq

/-- The parameterized Picard value and its derivative candidate are bounded by the sums of their
geometric majorants. These bounds make the endpoint of one Picard disk a valid locally bounded
seed for the next disk in a finite continuation chain. -/
theorem parameterizedPicardSeries_value_and_fderiv_norm_le_of_geometric_bounds
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (hr : 0 < r) (s : Set P)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (M L Y D ρ : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D) (hρ : 0 ≤ ρ)
    (hρlt : ρ < 1)
    (hMr : M * r ≤ ρ)
    (hcontract : r * (M * D + L * Y) ≤ D * ρ)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L)
    (hy_bound : ∀ q ∈ s, ‖y q‖ ≤ Y)
    (hDy_bound : ∀ q ∈ s, ‖Dy q‖ ≤ D) :
    ∀ q ∈ s, ∀ z ∈ Metric.ball c r,
      ‖∑' n : ℕ, parameterizedPicardTerm c A y n q z‖ ≤ Y * (1 - ρ)⁻¹ ∧
      ‖∑' n : ℕ, parameterizedPicardTermParamFDeriv c A DA y Dy n q z‖ ≤
        D * (1 - ρ)⁻¹ := by
  have hvalueTerm := parameterizedPicardTerm_norm_le_of_geometric
    c r M Y ρ s A hA hM (le_of_lt hr) hMr hA_bound y hy_bound
  have hderivTerm := parameterizedPicardTermParamFDeriv_norm_le_of_geometric
    c r hr A DA y Dy s M L Y D ρ hM hL hY hD hρ hcontract
    hA_bound hDA_bound hvalueTerm hDy_bound
  let valueMajorant : ℕ → ℝ := fun n => Y * ρ ^ n
  let derivMajorant : ℕ → ℝ := fun n => D * ρ ^ n
  have hvalueMajorant : Summable valueMajorant := by
    dsimp [valueMajorant]
    exact (summable_geometric_of_lt_one hρ hρlt).mul_left Y
  have hderivMajorant : Summable derivMajorant := by
    dsimp [derivMajorant]
    exact (summable_geometric_of_lt_one hρ hρlt).mul_left D
  have hvalueNormSum : ∀ q ∈ s, ∀ z ∈ Metric.ball c r,
      Summable (fun n : ℕ => ‖parameterizedPicardTerm c A y n q z‖) := by
    intro q hq z hz
    apply hvalueMajorant.of_norm_bounded
    intro n
    simpa [valueMajorant] using hvalueTerm n q hq z hz
  have hderivNormSum : ∀ q ∈ s, ∀ z ∈ Metric.ball c r,
      Summable (fun n : ℕ =>
        ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q z‖) := by
    intro q hq z hz
    apply hderivMajorant.of_norm_bounded
    intro n
    simpa [derivMajorant] using hderivTerm n q hq z hz
  intro q hq z hz
  constructor
  · calc
      ‖∑' n : ℕ, parameterizedPicardTerm c A y n q z‖ ≤
          ∑' n : ℕ, ‖parameterizedPicardTerm c A y n q z‖ :=
        norm_tsum_le_tsum_norm (hvalueNormSum q hq z hz)
      _ ≤ ∑' n : ℕ, valueMajorant n :=
        (hvalueNormSum q hq z hz).tsum_le_tsum
          (fun n => hvalueTerm n q hq z hz) hvalueMajorant
      _ = Y * (1 - ρ)⁻¹ := by
        dsimp [valueMajorant]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ hρlt]
  · calc
      ‖∑' n : ℕ, parameterizedPicardTermParamFDeriv c A DA y Dy n q z‖ ≤
          ∑' n : ℕ, ‖parameterizedPicardTermParamFDeriv c A DA y Dy n q z‖ :=
        norm_tsum_le_tsum_norm (hderivNormSum q hq z hz)
      _ ≤ ∑' n : ℕ, derivMajorant n :=
        (hderivNormSum q hq z hz).tsum_le_tsum
          (fun n => hderivTerm n q hq z hz) hderivMajorant
      _ = D * (1 - ρ)⁻¹ := by
        dsimp [derivMajorant]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ hρlt]

/-- One parameterized Picard disk advances a differentiable seed map to a differentiable endpoint
map, with uniform value and derivative bounds for that endpoint. The output bounds and the fixed
smaller radius let this step iterate over a finite continuation chain. -/
theorem exists_parameterizedPicardSeries_local_step
    [CompleteSpace E]
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (s : Set P) (hs : IsOpen s) (hsconn : IsPreconnected s)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c R))
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (hDA : ∀ q, ContinuousOn (DA q) (Metric.ball c R))
    (y : P → E) (Dy : P → P →L[ℂ] E)
    (M L Y D : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hY : 0 ≤ Y) (hD : 0 ≤ D) (hDpos : 0 < D)
    (hAderiv : ∀ q ∈ s, ∀ w ∈ Metric.ball c R,
      HasFDerivAt (fun q' => A q' w) (DA q w) q)
    (hA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c R, ‖A q w‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ w ∈ Metric.ball c R, ‖DA q w‖ ≤ L)
    (hyderiv : ∀ q ∈ s, HasFDerivAt y (Dy q) q)
    (hy_bound : ∀ q ∈ s, ‖y q‖ ≤ Y)
    (hDy_bound : ∀ q ∈ s, ‖Dy q‖ ≤ D)
    (q₀ : P) (hq₀ : q₀ ∈ s) :
    ∃ r : ℝ, 0 < r ∧
      ∀ q ∈ s, ∀ z ∈ Metric.ball c r,
        HasFDerivAt
            (fun p => ∑' n : ℕ, parameterizedPicardTerm c A y n p z)
            (∑' n : ℕ, parameterizedPicardTermParamFDeriv c A DA y Dy n q z) q ∧
        ‖∑' n : ℕ, parameterizedPicardTerm c A y n q z‖ ≤ 2 * Y ∧
        ‖∑' n : ℕ, parameterizedPicardTermParamFDeriv c A DA y Dy n q z‖ ≤ 2 * D := by
  let ρ : ℝ := 1 / 2
  have hρ : 0 ≤ ρ := by norm_num [ρ]
  have hρpos : 0 < ρ := by norm_num [ρ]
  have hρlt : ρ < 1 := by norm_num [ρ]
  let r : ℝ := min (R / 2)
    (min (ρ / (M + 1)) (D * ρ / (M * D + L * Y + 1)))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (by positivity) (lt_min ?_ ?_)
    · exact div_pos hρpos (by linarith)
    · apply div_pos
      · exact mul_pos hDpos hρpos
      · positivity
  have hrR : r ≤ R := by
    dsimp [r]
    exact (min_le_left _ _).trans (by linarith)
  have hrMr : r ≤ ρ / (M + 1) := by
    dsimp [r]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hMr : M * r ≤ ρ := by
    have hden : 0 < M + 1 := by linarith
    have hfrac : M / (M + 1) ≤ 1 := (div_le_one hden).2 (by linarith)
    calc
      M * r ≤ M * (ρ / (M + 1)) :=
        mul_le_mul_of_nonneg_left hrMr hM
      _ = ρ * (M / (M + 1)) := by ring
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hfrac hρ
      _ = ρ := by ring
  have hrcontract : r ≤ D * ρ / (M * D + L * Y + 1) := by
    dsimp [r]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let S : ℝ := M * D + L * Y
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSden : 0 < S + 1 := by dsimp [S]; linarith
  have hfracS : S / (S + 1) ≤ 1 := (div_le_one hSden).2 (by linarith)
  have hcontract : r * (M * D + L * Y) ≤ D * ρ := by
    calc
      r * (M * D + L * Y) ≤ (D * ρ / (S + 1)) * S := by
        dsimp [S]
        exact mul_le_mul_of_nonneg_right hrcontract hS
      _ = D * ρ * (S / (S + 1)) := by
        dsimp [S]
        field_simp
      _ ≤ D * ρ * 1 :=
        mul_le_mul_of_nonneg_left hfracS (mul_nonneg hD hρ)
      _ = D * ρ := by ring
  have hAr : ∀ q, DifferentiableOn ℂ (A q) (Metric.ball c r) := by
    intro q
    exact (hA q).mono (Metric.ball_subset_ball hrR)
  have hDAr : ∀ q, ContinuousOn (DA q) (Metric.ball c r) := by
    intro q
    exact (hDA q).mono (Metric.ball_subset_ball hrR)
  have hAderivr : ∀ q ∈ s, ∀ w ∈ Metric.ball c r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q := by
    intro q hq w hw
    exact hAderiv q hq w (Metric.ball_subset_ball hrR hw)
  have hAboundr : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖A q w‖ ≤ M := by
    intro q hq w hw
    exact hA_bound q hq w (Metric.ball_subset_ball hrR hw)
  have hDAboundr : ∀ q ∈ s, ∀ w ∈ Metric.ball c r, ‖DA q w‖ ≤ L := by
    intro q hq w hw
    exact hDA_bound q hq w (Metric.ball_subset_ball hrR hw)
  have hsumBounds := parameterizedPicardSeries_value_and_fderiv_norm_le_of_geometric_bounds
    c r hr s A hAr DA y Dy M L Y D ρ hM hL hY hD hρ hρlt hMr hcontract
    hAboundr hDAboundr hy_bound hDy_bound
  refine ⟨r, hr, ?_⟩
  intro q hq z hz
  have hderiv := parameterizedPicardSeries_hasFDerivAt_of_geometric_bounds
    c r hr s hs hsconn A hAr DA hDAr y Dy M L Y D ρ
    hM hL hY hD hρ hρlt hMr hcontract
    hAderivr hAboundr hDAboundr hyderiv hy_bound hDy_bound hq₀ hq hz
  have hbound := hsumBounds q hq z hz
  have hfactor : (1 - ρ)⁻¹ = 2 := by norm_num [ρ]
  exact ⟨hderiv, by simpa [hfactor, mul_comm] using hbound.1,
    by simpa [hfactor, mul_comm] using hbound.2⟩

end DOZZ.Proofs
