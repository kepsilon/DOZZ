/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.PicardSum
public import DOZZ.Hypergeom.ODE.SegmentIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! An integral representation of Picard summands with varying parameters. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace DOZZ.Proofs

variable {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Picard summands for a family of linear systems, written recursively using segment integrals.
This form exposes parameter dependence that is hidden by the chosen primitive in the fixed-system
construction. -/
noncomputable def parameterizedPicardTerm (c : ℂ)
    (A : P → ℂ → E →L[ℂ] E) (y : P → E) : ℕ → P → ℂ → E
  | 0 => fun p _ => y p
  | n + 1 => fun p z =>
      letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
      ∫ t in (0 : ℝ)..1,
        (z - c) • A p (AffineMap.lineMap c z t)
          (parameterizedPicardTerm c A y n p (AffineMap.lineMap c z t))

/-- For each fixed parameter, the integral recursion equals the existing holomorphic Picard
summands on their disk. -/
theorem parameterizedPicardTerm_eq_holomorphicPicardTerm
    [CompleteSpace E]
    (c : ℂ) (r : ℝ) (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ p, DifferentiableOn ℂ (A p) (Metric.ball c r))
    (y : P → E) :
    ∀ n p z, z ∈ Metric.ball c r →
      parameterizedPicardTerm c A y n p z =
        holomorphicPicardTerm c r (A p) (hA p) (y p) n z := by
  intro n
  induction n with
  | zero =>
      intro p z hz
      simp [parameterizedPicardTerm, holomorphicPicardTerm, holomorphicPicardIterates]
  | succ n ih =>
      intro p z hz
      let D := holomorphicPicardIterates c r (A p) (hA p) (y p) n
      let f : ℂ → E := fun w => A p w (D.1 w)
      have hf : DifferentiableOn ℂ f (Metric.ball c r) :=
        (hA p).clm_apply D.2
      have hcenter : c ∈ Metric.ball c r := by
        have hr : 0 < r := lt_of_le_of_lt (dist_nonneg) (Metric.mem_ball.mp hz)
        exact Metric.mem_ball_self hr
      have hseg : MapsTo (AffineMap.lineMap c z) (Icc (0 : ℝ) 1)
          (Metric.ball c r) := (convex_ball c r).mapsTo_lineMap hcenter hz
      have hrec : holomorphicPicardTerm c r (A p) (hA p) (y p) (n + 1) z =
          ∫ t in (0 : ℝ)..1,
            (z - c) • f (AffineMap.lineMap c z t) := by
        change normalizedDiskPrimitive c r f 0 hf z = _
        calc
          normalizedDiskPrimitive c r f 0 hf z =
              normalizedDiskPrimitive c r f 0 hf z - (0 : E) := by simp
          _ = ∫ t in (0 : ℝ)..1, (z - c) • f (AffineMap.lineMap c z t) :=
            normalizedDiskPrimitive_sub_center_eq_segmentIntegral hf hz
      rw [hrec]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le zero_le_one] using ht
      have hw := hseg ht'
      let w := AffineMap.lineMap c z t
      change (z - c) • A p w
          (parameterizedPicardTerm c A y n p w) = (z - c) • f w
      rw [ih p w hw]
      rfl

/-- On a compact parameter family with common coefficient and initial-value bounds, every
parameterized Picard summand has the same factorial majorant. -/
theorem parameterizedPicardTerm_norm_le_of_uniform_bounds
    [CompleteSpace E]
    (c : ℂ) (r M Y : ℝ) (K : Set P)
    (A : P → ℂ → E →L[ℂ] E)
    (hA : ∀ p, DifferentiableOn ℂ (A p) (Metric.ball c r))
    (hM : 0 ≤ M)
    (hAbound : ∀ p ∈ K, ∀ z ∈ Metric.ball c r, ‖A p z‖ ≤ M)
    (y : P → E)
    (hy : ∀ p ∈ K, ‖y p‖ ≤ Y) :
    ∀ n p z, p ∈ K → z ∈ Metric.ball c r →
      ‖parameterizedPicardTerm c A y n p z‖ ≤
        Y * (M * max r 0) ^ n / (n.factorial : ℝ) := by
  intro n p z hp hz
  rw [parameterizedPicardTerm_eq_holomorphicPicardTerm c r A hA y n p z hz]
  have hterm := holomorphicPicardTerm_norm_le c r M (A p) (hA p) (y p)
    hM (fun w hw => hAbound p hp w hw) n z hz
  have hfactor : 0 ≤ (M * max r 0) ^ n / (n.factorial : ℝ) := by positivity
  calc
    ‖holomorphicPicardTerm c r (A p) (hA p) (y p) n z‖ ≤
        ‖y p‖ * (M * max r 0) ^ n / (n.factorial : ℝ) := hterm
    _ ≤ Y * (M * max r 0) ^ n / (n.factorial : ℝ) := by
      gcongr
      exact hy p hp

/-- The first Picard-step integrand has the usual product-rule derivative in parameters: one term
differentiates the coefficient operator and the other differentiates the initial vector. -/
theorem hasFDerivAt_parameterizedPicardIntegrand_zero
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c z w : ℂ) (A : P → ℂ → E →L[ℂ] E) (y : P → E) (p : P)
    (DA : P →L[ℂ] (E →L[ℂ] E)) (Dy : P →L[ℂ] E)
    (hA : HasFDerivAt (fun q => A q w) DA p)
    (hy : HasFDerivAt y Dy p) :
    HasFDerivAt (fun q => (z - c) • A q w (y q))
      ((z - c) • ((A p w).comp Dy + DA.flip (y p))) p := by
  exact (hA.clm_apply hy).const_smul (z - c)

/-- Bounds for the coefficient, its parameter derivative, the initial value, and its derivative
give a uniform scalar majorant for the differentiated first Picard integrand. -/
theorem norm_parameterizedPicardIntegrand_zero_fderiv_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c z w : ℂ) (A : P → ℂ → E →L[ℂ] E) (y : P → E) (p : P)
    (DA : P →L[ℂ] (E →L[ℂ] E)) (Dy : P →L[ℂ] E)
    (M L Y D : ℝ)
    (hA : ‖A p w‖ ≤ M) (hDA : ‖DA‖ ≤ L)
    (hy : ‖y p‖ ≤ Y) (hDy : ‖Dy‖ ≤ D) :
    ‖(z - c) • ((A p w).comp Dy + DA.flip (y p))‖ ≤
      ‖z - c‖ * (M * D + L * Y) := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (A p w)) hA
  have hL : 0 ≤ L := le_trans (norm_nonneg DA) hDA
  have hY : 0 ≤ Y := le_trans (norm_nonneg (y p)) hy
  have hD : 0 ≤ D := le_trans (norm_nonneg Dy) hDy
  have hcomp : ‖(A p w).comp Dy‖ ≤ M * D := by
    calc
      ‖(A p w).comp Dy‖ ≤ ‖A p w‖ * ‖Dy‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * ‖Dy‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ M * D := mul_le_mul_of_nonneg_left hDy hM
  have hflip : ‖DA.flip (y p)‖ ≤ L * Y := by
    calc
      ‖DA.flip (y p)‖ ≤ ‖DA.flip‖ * ‖y p‖ := (DA.flip).le_opNorm _
      _ = ‖DA‖ * ‖y p‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ L * ‖y p‖ := mul_le_mul_of_nonneg_right hDA (norm_nonneg _)
      _ ≤ L * Y := mul_le_mul_of_nonneg_left hy hL
  calc
    ‖(z - c) • ((A p w).comp Dy + DA.flip (y p))‖ =
        ‖z - c‖ * ‖(A p w).comp Dy + DA.flip (y p)‖ := norm_smul _ _
    _ ≤ ‖z - c‖ * (‖(A p w).comp Dy‖ + ‖DA.flip (y p)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖z - c‖ * (M * D + L * Y) := by
      gcongr


/-- Differentiation under the segment integral gives the parameter derivative of one Picard
recursion step whenever the integrand derivatives have an integrable uniform majorant. -/
theorem parameterizedPicardTerm_succ_hasFDerivAt_of_dominated
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c z : ℂ) (A : P → ℂ → E →L[ℂ] E) (y : P → E) (n : ℕ) (p : P)
    (s : Set P) (hs : s ∈ 𝓝 p)
    (F : P → ℝ → E) (F' : P → ℝ → P →L[ℂ] E) (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable (F q) (volume.restrict (Ι (0 : ℝ) 1)))
    (hF_int : IntervalIntegrable (F p) volume 0 1)
    (hF'_meas : AEStronglyMeasurable (F' p) (volume.restrict (Ι (0 : ℝ) 1)) )
    (hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ q ∈ s, ‖F' q t‖ ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume 0 1)
    (hF_deriv : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ q ∈ s,
      HasFDerivAt (fun q => F q t) (F' q t) q)
    (hF_eq : ∀ q t, F q t = (z - c) • A q (AffineMap.lineMap c z t)
      (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t))) :
    HasFDerivAt
      (fun q => parameterizedPicardTerm c A y (n + 1) q z)
      (∫ t in (0 : ℝ)..1, F' p t) p := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hIntegral := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (a := (0 : ℝ)) (b := 1) (μ := volume) hs hF_meas hF_int hF'_meas hbound
    hbound_int hF_deriv
  have hEq : (fun q => parameterizedPicardTerm c A y (n + 1) q z) =
      (fun q => ∫ t in (0 : ℝ)..1, F q t) := by
    funext q
    simp only [parameterizedPicardTerm]
    rw [intervalIntegral.integral_congr]
    intro t ht
    exact (hF_eq q t).symm
  rw [hEq]
  exact hIntegral

/-- A parameter-uniform bound on each previous Picard term and its parameter derivative supplies
the dominated-differentiation hypotheses for the next recursive step. The measurability and
integrability premises remain explicit so concrete ODE families can discharge them from their
spatial regularity. -/
theorem parameterizedPicardTerm_succ_hasFDerivAt_of_bounds
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c z : ℂ) (A : P → ℂ → E →L[ℂ] E)
    (DA : P → ℂ → P →L[ℂ] (E →L[ℂ] E))
    (y : P → E) (DT : P → ℂ → P →L[ℂ] E) (n : ℕ) (p : P) (s : Set P)
    (hs : s ∈ 𝓝 p) (M L Y D : ℝ)
    (hAderiv : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun q' => A q' (AffineMap.lineMap c z t))
        (DA q (AffineMap.lineMap c z t)) q)
    (hA_bound : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖A q (AffineMap.lineMap c z t)‖ ≤ M)
    (hDA_bound : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖DA q (AffineMap.lineMap c z t)‖ ≤ L)
    (hTderiv : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt
        (fun q' => parameterizedPicardTerm c A y n q'
          (AffineMap.lineMap c z t))
        (DT q (AffineMap.lineMap c z t)) q)
    (hT_bound : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t)‖ ≤ Y)
    (hDT_bound : ∀ q ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖DT q (AffineMap.lineMap c z t)‖ ≤ D)
    (hF_meas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable
        (fun t : ℝ => (z - c) • A q (AffineMap.lineMap c z t)
          (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t)))
        (volume.restrict (Ι (0 : ℝ) 1)))
    (hF_int : IntervalIntegrable
      (fun t : ℝ => (z - c) • A p (AffineMap.lineMap c z t)
        (parameterizedPicardTerm c A y n p (AffineMap.lineMap c z t))) volume 0 1)
    (hFderiv_meas : AEStronglyMeasurable
      (fun t : ℝ => (z - c) •
        ((A p (AffineMap.lineMap c z t)).comp
            (DT p (AffineMap.lineMap c z t)) +
          (DA p (AffineMap.lineMap c z t)).flip
            (parameterizedPicardTerm c A y n p (AffineMap.lineMap c z t))))
      (volume.restrict (Ι (0 : ℝ) 1))) :
    HasFDerivAt
      (fun q => parameterizedPicardTerm c A y (n + 1) q z)
      (∫ t in (0 : ℝ)..1, (z - c) •
        ((A p (AffineMap.lineMap c z t)).comp (DT p (AffineMap.lineMap c z t)) +
          (DA p (AffineMap.lineMap c z t)).flip
            (parameterizedPicardTerm c A y n p (AffineMap.lineMap c z t)))) p := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let F : P → ℝ → E := fun q t =>
    (z - c) • A q (AffineMap.lineMap c z t)
      (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t))
  let F' : P → ℝ → P →L[ℂ] E := fun q t =>
    (z - c) •
      ((A q (AffineMap.lineMap c z t)).comp (DT q (AffineMap.lineMap c z t)) +
        (DA q (AffineMap.lineMap c z t)).flip
          (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t)))
  let bound : ℝ → ℝ := fun _ => ‖z - c‖ * (M * D + L * Y)
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ q ∈ s, ‖F' q t‖ ≤ bound t := by
    filter_upwards [] with t
    intro ht q hq
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le zero_le_one] using ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
    exact norm_parameterizedPicardIntegrand_zero_fderiv_le c z
      (AffineMap.lineMap c z t) A
      (fun q => parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t)) q
      (DA q (AffineMap.lineMap c z t)) (DT q (AffineMap.lineMap c z t))
      M L Y D (hA_bound q hq t htcc) (hDA_bound q hq t htcc)
      (hT_bound q hq t htcc) (hDT_bound q hq t htcc)
  have hbound_int : IntervalIntegrable bound volume 0 1 := by
    dsimp [bound]
    exact intervalIntegrable_const
  have hFderiv : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ q ∈ s,
      HasFDerivAt (fun q => F q t) (F' q t) q := by
    filter_upwards [] with t
    intro ht q hq
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le zero_le_one] using ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
    exact hasFDerivAt_parameterizedPicardIntegrand_zero c z
      (AffineMap.lineMap c z t) A
      (fun q => parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t)) q
      (DA q (AffineMap.lineMap c z t)) (DT q (AffineMap.lineMap c z t))
      (hAderiv q hq t htcc) (hTderiv q hq t htcc)
  have hF_eq : ∀ q t,
      F q t = (z - c) • A q (AffineMap.lineMap c z t)
        (parameterizedPicardTerm c A y n q (AffineMap.lineMap c z t)) := by
    intro q t
    rfl
  exact parameterizedPicardTerm_succ_hasFDerivAt_of_dominated
    c z A y n p s hs F F' bound hF_meas hF_int hFderiv_meas hbound hbound_int
    hFderiv hF_eq


end DOZZ.Proofs
