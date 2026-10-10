/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.StandardGaussianProductStein
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Automatic Gaussian Stein integrability for bounded tests and bounded derivatives. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions NNReal

namespace DOZZ.Proofs

private lemma integrable_abs_mul_gaussianPDFReal_standard :
    Integrable (fun r : ℝ => |r| * gaussianPDFReal 0 1 r) volume := by
  have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := IsGaussian.integrable_id
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at hid
  have hsmul := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1)
    (by filter_upwards [] with r; exact gaussianPDF_lt_top)).mp hid
  have hmul : Integrable (fun r : ℝ => gaussianPDFReal 0 1 r * r) volume := by
    simpa [toReal_gaussianPDF, smul_eq_mul] using hsmul
  have hnorm := hmul.norm
  simpa [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _), mul_comm] using hnorm

/-- A bounded smooth scalar test and a bounded coordinate derivative automatically satisfy all
sectionwise density and global product-integrability assumptions of the finite-product Stein
lemma. -/
theorem gaussianReal_pi_coordinate_stein_of_bounded
    {n : ℕ} (i : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (D : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hg : ∀ y r, HasDerivAt
      (fun s => g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
        (s, y)))
      (D ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (r, y)) i) r)
    (hgMeas : Measurable g) (hDMeas : Measurable D)
    (B₁ B₂ : ℝ)
    (hgBound : ∀ x, ‖g x‖ ≤ B₁)
    (hDBound : ∀ x, ‖D x i‖ ≤ B₂) :
    ∫ x, x i * g x ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∫ x, D x i ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let μ := gaussianReal 0 1
  let ν := Measure.pi fun _ : Fin n => gaussianReal 0 1
  let μprod := μ.prod ν
  let : IsProbabilityMeasure ν := inferInstance
  let : IsProbabilityMeasure μprod := inferInstance
  have hfst : MeasurePreserving Prod.fst μprod μ := measurePreserving_fst
  have hid : Integrable (id : ℝ → ℝ) μ := IsGaussian.integrable_id
  have hfirst : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1) μprod := by
    have hmap : Integrable (id : ℝ → ℝ) (μprod.map Prod.fst) := by
      rw [hfst.map_eq]
      exact hid
    exact hmap.comp_measurable measurable_fst
  have hfirstAbs : Integrable (fun p : ℝ × (Fin n → ℝ) => ‖p.1‖) μprod := hfirst.norm
  have hleft : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      p.1 * g (e.symm p)) μprod := by
    have hdom : Integrable (fun p : ℝ × (Fin n → ℝ) => B₁ * ‖p.1‖) μprod :=
      hfirstAbs.const_mul B₁
    apply hdom.mono'
    · exact (measurable_fst.mul (hgMeas.comp e.symm.measurable)).aestronglyMeasurable
    · filter_upwards [] with p
      calc
        ‖p.1 * g (e.symm p)‖ = ‖p.1‖ * ‖g (e.symm p)‖ := norm_mul _ _
        _ ≤ ‖p.1‖ * B₁ := mul_le_mul_of_nonneg_left (hgBound _) (norm_nonneg _)
        _ = B₁ * ‖p.1‖ := by ring
  have hright : Integrable (fun p : ℝ × (Fin n → ℝ) => D (e.symm p) i) μprod := by
    have hmeas : Measurable (fun p : ℝ × (Fin n → ℝ) => D (e.symm p) i) :=
      Measurable.eval (hDMeas.comp e.symm.measurable)
    exact Integrable.of_bound hmeas.aestronglyMeasurable B₂
      (ae_of_all _ fun p => hDBound (e.symm p))
  have hgp : ∀ y : Fin n → ℝ, Integrable (fun r : ℝ =>
      g (e.symm (r, y)) * (-r * gaussianPDFReal 0 1 r)) volume := by
    intro y
    have hdom : Integrable (fun r : ℝ => B₁ * (|r| * gaussianPDFReal 0 1 r)) volume :=
      integrable_abs_mul_gaussianPDFReal_standard.const_mul B₁
    apply hdom.mono'
    · exact ((hgMeas.comp (by fun_prop)).mul
        ((measurable_id.neg.mul (measurable_gaussianPDFReal 0 1)))).aestronglyMeasurable
    · filter_upwards [] with r
      have hpdf := gaussianPDFReal_nonneg 0 1 r
      calc
        ‖g (e.symm (r, y)) * (-r * gaussianPDFReal 0 1 r)‖ =
            ‖g (e.symm (r, y))‖ * (|r| * gaussianPDFReal 0 1 r) := by
              simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpdf]
        _ ≤ B₁ * (|r| * gaussianPDFReal 0 1 r) :=
          mul_le_mul_of_nonneg_right (hgBound _) (mul_nonneg (abs_nonneg _) hpdf)
  have hDp : ∀ y : Fin n → ℝ, Integrable (fun r : ℝ =>
      D (e.symm (r, y)) i * gaussianPDFReal 0 1 r) volume := by
    intro y
    have hdom : Integrable (fun r : ℝ => B₂ * gaussianPDFReal 0 1 r) volume :=
      (integrable_gaussianPDFReal 0 1).const_mul B₂
    apply hdom.mono'
    · have hDsec : Measurable (fun r : ℝ => D (e.symm (r, y))) :=
        hDMeas.comp (by fun_prop)
      exact (Measurable.eval hDsec).aestronglyMeasurable.mul
        (measurable_gaussianPDFReal 0 1).aestronglyMeasurable
    · filter_upwards [] with r
      have hpdf := gaussianPDFReal_nonneg 0 1 r
      calc
        ‖D (e.symm (r, y)) i * gaussianPDFReal 0 1 r‖ =
            ‖D (e.symm (r, y)) i‖ * gaussianPDFReal 0 1 r := by
              simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpdf]
        _ ≤ B₂ * gaussianPDFReal 0 1 r :=
          mul_le_mul_of_nonneg_right (hDBound _) hpdf
  have hprod : ∀ y : Fin n → ℝ, Integrable (fun r : ℝ =>
      g (e.symm (r, y)) * gaussianPDFReal 0 1 r) volume := by
    intro y
    have hdom : Integrable (fun r : ℝ => B₁ * gaussianPDFReal 0 1 r) volume :=
      (integrable_gaussianPDFReal 0 1).const_mul B₁
    apply hdom.mono'
    · exact (hgMeas.comp (by fun_prop)).aestronglyMeasurable.mul
        (measurable_gaussianPDFReal 0 1).aestronglyMeasurable
    · filter_upwards [] with r
      have hpdf := gaussianPDFReal_nonneg 0 1 r
      calc
        ‖g (e.symm (r, y)) * gaussianPDFReal 0 1 r‖ =
            ‖g (e.symm (r, y))‖ * gaussianPDFReal 0 1 r := by
              simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpdf]
        _ ≤ B₁ * gaussianPDFReal 0 1 r :=
          mul_le_mul_of_nonneg_right (hgBound _) hpdf
  have hderiv : ∀ y r, HasDerivAt (fun s => (fun x => g x) (e.symm (s, y)))
      (D (e.symm (r, y)) i) r := hg
  have hleft' : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      p.1 * (fun x => g x) (e.symm p)) μprod := hleft
  have hright' : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      D (e.symm p) i) μprod := hright
  simpa [e, μ, ν, μprod] using
    gaussianReal_pi_coordinate_stein i (fun x _ => g x) D hderiv hgp hDp hprod hleft' hright'

/-- The bounded product Stein theorem gives covariance integration by parts for every linear image
of a standard Gaussian vector, including singular images. The derivative and the test itself only
need uniform pointwise bounds. -/
theorem gaussianLinearImage_pi_integration_by_parts_of_bounded
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : (Fin (n + 1) → ℝ) → ℝ)
    (D : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hderiv : ∀ k (y : Fin n → ℝ) r,
      HasDerivAt
        (fun s => G (fun i => ∑ l, A i l *
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (s, y) l))
        (∑ j, A j k * D
          (fun i => ∑ l, A i l *
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (r, y) l) j) r)
    (hGMeas : Measurable G) (hDMeas : Measurable D)
    (BG BD : ℝ)
    (hGBound : ∀ (x : Fin (n + 1) → ℝ),
      ‖G (fun i => ∑ l, A i l * x l)‖ ≤ BG)
    (hDBound : ∀ (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)),
      ‖D (fun i => ∑ l, A i l * x l) j‖ ≤ BD)
    (i : Fin (n + 1)) :
    ∫ x, (∑ k, A i k * x k) * G (fun r => ∑ l, A r l * x l)
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∑ j, (∑ k, A i k * A j k) *
        ∫ x, D (fun r => ∑ l, A r l * x l) j
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
  let T : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x i => ∑ l, A i l * x l
  let Gstd : (Fin (n + 1) → ℝ) → ℝ := fun x => G (T x)
  let Dstd : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x k =>
    ∑ j, A j k * D (T x) j
  have hTMeas : Measurable T := by fun_prop
  have hGstdMeas : Measurable Gstd := by
    exact hGMeas.comp hTMeas
  have hDstdMeas : Measurable Dstd := by
    fun_prop
  have hDstdBound (k : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
      ‖Dstd x k‖ ≤ ∑ j, |A j k| * BD := by
    calc
      ‖Dstd x k‖ = ‖∑ j, A j k * D (T x) j‖ := rfl
      _ ≤ ∑ j, ‖A j k * D (T x) j‖ := norm_sum_le _ _
      _ ≤ ∑ j, |A j k| * BD := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hDBound x j) (abs_nonneg _)
  have hcoord : ∀ k : Fin (n + 1),
      ∫ x, x k * Gstd x ∂μ = ∫ x, Dstd x k ∂μ := by
    intro k
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
    have hderiv' : ∀ y r, HasDerivAt (fun s => Gstd (e.symm (s, y)))
        (Dstd (e.symm (r, y)) k) r := by
      intro y r
      simpa [e, Gstd, Dstd, T] using hderiv k y r
    have hDbound' : ∀ x, ‖Dstd x k‖ ≤ ∑ j, |A j k| * BD := hDstdBound k
    exact gaussianReal_pi_coordinate_stein_of_bounded k Gstd Dstd hderiv'
      hGstdMeas hDstdMeas BG (∑ j, |A j k| * BD) hGBound hDbound'
  have hGint : ∀ k : Fin (n + 1), Integrable (fun x => x k * Gstd x) μ := by
    intro k
    have hxk : Integrable (fun x : Fin (n + 1) → ℝ => x k) μ :=
      MeasureTheory.integrable_eval IsGaussian.integrable_id
    have hdom : Integrable (fun x : Fin (n + 1) → ℝ => BG * ‖x k‖) μ :=
      hxk.norm.const_mul BG
    apply hdom.mono'
    · exact ((measurable_pi_apply k).mul hGstdMeas).aestronglyMeasurable
    · filter_upwards [] with x
      calc
        ‖x k * Gstd x‖ = ‖x k‖ * ‖Gstd x‖ := norm_mul _ _
        _ ≤ ‖x k‖ * BG := mul_le_mul_of_nonneg_left
          (by simpa [Gstd, T] using hGBound x) (norm_nonneg _)
        _ = BG * ‖x k‖ := by ring
  have hDint : ∀ j : Fin (n + 1), Integrable (fun x => Dstd x j) μ := by
    intro j
    exact Integrable.of_bound hDstdMeas.eval.aestronglyMeasurable
      (∑ k, |A k j| * BD) (ae_of_all _ (hDstdBound j))
  have hcoord' : ∀ k : Fin (n + 1),
      ∫ x, x k * G (T x) ∂μ = ∫ x, (∑ j, A j k * D (T x) j) ∂μ := by
    simpa [Gstd, Dstd, T] using hcoord
  have hGint' : ∀ k : Fin (n + 1),
      Integrable (fun x => x k * G (T x)) μ := by
    simpa [Gstd, T] using hGint
  have hDint' : ∀ j : Fin (n + 1),
      Integrable (fun x => D (T x) j) μ := by
    have hDbd : ∀ j x, ‖D (T x) j‖ ≤ BD := by
      intro j x
      simpa [T] using hDBound x j
    intro j
    exact Integrable.of_bound (hDMeas.comp hTMeas).eval.aestronglyMeasurable
      BD (ae_of_all _ (hDbd j))
  simpa [μ, T] using
    gaussianLinearImage_pi_integration_by_parts A G D hGint' hcoord' hDint' i

end DOZZ.Proofs
