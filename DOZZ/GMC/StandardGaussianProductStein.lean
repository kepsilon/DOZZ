/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.GaussianIntegrationByParts
public import DOZZ.GMC.FiniteGaussianTilt
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Coordinatewise Stein integration by parts for a finite product of standard Gaussians. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Topology MatrixOrder

namespace DOZZ.Proofs

/-- Lift one-dimensional Gaussian Stein integration by parts to one coordinate of a finite
product of independent standard normal variables. The hypotheses give the sectionwise density
integrability needed by the one-dimensional lemma and the product integrability needed for
Fubini. -/
theorem gaussianReal_pi_coordinate_stein
    {n : ℕ} (i : Fin (n + 1))
    (g D : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hg : ∀ y r, HasDerivAt
      (fun s => g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
        (s, y)) i)
      (D ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (r, y)) i) r)
    (hgp : ∀ y, Integrable (fun r => g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (r, y)) i *
        (-r * gaussianPDFReal 0 1 r)) volume)
    (hDp : ∀ y, Integrable (fun r => D
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (r, y)) i *
        gaussianPDFReal 0 1 r) volume)
    (hprod : ∀ y, Integrable (fun r => g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (r, y)) i *
        gaussianPDFReal 0 1 r) volume)
    (hleft : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm p) i)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    (hright : Integrable (fun p : ℝ × (Fin n → ℝ) => D
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm p) i)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) :
    ∫ x, x i * g x i ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∫ x, D x i ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let μ := gaussianReal 0 1
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hleft' : ∫ p, p.1 * g (e.symm p) i ∂(μ.prod ν) =
      ∫ y, ∫ r, r * g (e.symm (r, y)) i ∂μ ∂ν := by
    exact integral_prod_symm _ hleft
  have hright' : ∫ p, D (e.symm p) i ∂(μ.prod ν) =
      ∫ y, ∫ r, D (e.symm (r, y)) i ∂μ ∂ν := by
    exact integral_prod_symm _ hright
  have hsections : ∀ y, (∫ r, r * g (e.symm (r, y)) i ∂μ) =
      ∫ r, D (e.symm (r, y)) i ∂μ := by
    intro y
    have hstein := gaussianReal_standard_stein
      (fun r => g (e.symm (r, y)) i)
      (fun r => D (e.symm (r, y)) i)
      (fun r => hg y r)
      (by simpa [μ, e] using hgp y)
      (by simpa [μ, e] using hDp y)
      (by simpa [μ, e] using hprod y)
    simpa [μ] using hstein
  calc
    ∫ x, x i * g x i ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
        ∫ p, p.1 * g (e.symm p) i ∂(μ.prod ν) := by
          calc
            ∫ x, x i * g x i ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
                ∫ x, (e x).1 * g (e.symm (e x)) i ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
                  apply integral_congr_ae
                  filter_upwards [] with x
                  rw [e.symm_apply_apply]
                  simp [e]
            _ = ∫ p, p.1 * g (e.symm p) i ∂(μ.prod ν) :=
                  mp.integral_comp' (fun p => p.1 * g (e.symm p) i)
    _ = ∫ y, ∫ r, r * g (e.symm (r, y)) i ∂μ ∂ν := hleft'
    _ = ∫ y, ∫ r, D (e.symm (r, y)) i ∂μ ∂ν := by
          apply integral_congr_ae
          exact ae_of_all _ hsections
    _ = ∫ p, D (e.symm p) i ∂(μ.prod ν) := hright'.symm
    _ = ∫ x, D x i ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
          calc
            ∫ p, D (e.symm p) i ∂(μ.prod ν) =
                ∫ x, D (e.symm (e x)) i ∂(Measure.pi fun _ : Fin (n + 1) => μ) :=
                  (mp.integral_comp' (fun p => D (e.symm p) i)).symm
            _ = ∫ x, D x i ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
                  apply integral_congr_ae
                  filter_upwards [] with x
                  rw [e.symm_apply_apply]

/-- Apply the product Stein identity to a smooth test after a linear transformation. The
coordinate derivative is the corresponding column of `A` paired with the gradient `D`. -/
theorem gaussianLinearImage_pi_coordinate_stein
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
    (hgp : ∀ k (y : Fin n → ℝ), Integrable
      (fun r => G (fun i => ∑ l, A i l *
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (r, y) l) *
        (-r * gaussianPDFReal 0 1 r)) volume)
    (hDp : ∀ k (y : Fin n → ℝ), Integrable
      (fun r => (∑ j, A j k * D
          (fun i => ∑ l, A i l *
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (r, y) l) j) *
        gaussianPDFReal 0 1 r) volume)
    (hprod : ∀ k (y : Fin n → ℝ), Integrable
      (fun r => G (fun i => ∑ l, A i l *
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (r, y) l) *
        gaussianPDFReal 0 1 r) volume)
    (hleft : ∀ k, Integrable
      (fun p : ℝ × (Fin n → ℝ) => p.1 * G
        (fun i => ∑ l, A i l *
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm p l))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    (hright : ∀ k, Integrable
      (fun p : ℝ × (Fin n → ℝ) => ∑ j, A j k * D
        (fun i => ∑ l, A i l *
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm p l) j)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))) :
    ∀ k, ∫ x, x k * G (fun i => ∑ l, A i l * x l)
      ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∫ x, (∑ j, A j k * D (fun i => ∑ l, A i l * x l) j)
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  intro k
  let T : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x i => ∑ l, A i l * x l
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
  let g : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x _ => G (T x)
  let Dstd : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x j =>
    ∑ l, A l j * D (T x) l
  have hderiv' : ∀ y r, HasDerivAt (fun s => g (e.symm (s, y)) k)
      (Dstd (e.symm (r, y)) k) r := by
    intro y r
    simpa [g, Dstd, T, e] using hderiv k y r
  have hgp' : ∀ y, Integrable
      (fun r => g (e.symm (r, y)) k * (-r * gaussianPDFReal 0 1 r)) volume := by
    intro y
    simpa [g, T, e] using hgp k y
  have hDp' : ∀ y, Integrable
      (fun r => Dstd (e.symm (r, y)) k * gaussianPDFReal 0 1 r) volume := by
    intro y
    simpa [Dstd, T, e] using hDp k y
  have hprod' : ∀ y, Integrable
      (fun r => g (e.symm (r, y)) k * gaussianPDFReal 0 1 r) volume := by
    intro y
    simpa [g, T, e] using hprod k y
  have hleft' : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * g (e.symm p) k)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    simpa [g, T, e] using hleft k
  have hright' : Integrable (fun p : ℝ × (Fin n → ℝ) => Dstd (e.symm p) k)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    simpa [Dstd, T, e] using hright k
  simpa [g, Dstd, T] using gaussianReal_pi_coordinate_stein k g Dstd
    hderiv' hgp' hDp' hprod' hleft' hright'

/-- The coordinatewise product Stein identities give Gaussian integration by parts after any
linear image of the standard Gaussian vector. The covariance entries are the row inner products
of the matrix `A`, so the statement remains valid when the image covariance is singular. -/
theorem gaussianLinearImage_pi_integration_by_parts
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : (Fin (n + 1) → ℝ) → ℝ)
    (D : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hGint : ∀ k, Integrable
      (fun x => x k * G (fun r => ∑ l, A r l * x l))
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1))
    (hcoord : ∀ k,
      ∫ x, x k * G (fun r => ∑ l, A r l * x l)
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
        ∫ x, (∑ j, A j k * D (fun r => ∑ l, A r l * x l) j)
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1))
    (hDint : ∀ j, Integrable
      (fun x => D (fun r => ∑ l, A r l * x l) j)
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1))
    (i : Fin (n + 1)) :
    ∫ x, (∑ k, A i k * x k) * G (fun r => ∑ l, A r l * x l)
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∑ j, (∑ k, A i k * A j k) *
        ∫ x, D (fun r => ∑ l, A r l * x l) j
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let X : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun x i => ∑ k, A i k * x k
  have hterm (k : Fin (n + 1)) :
      Integrable (fun x : Fin (n + 1) → ℝ => A i k *
        (x k * G (fun r => ∑ l, A r l * x l))) μ := by
    exact (hGint k).const_mul _
  have hsumEq : (fun x : Fin (n + 1) → ℝ =>
      (∑ k, A i k * x k) * G (X x)) =
      fun x => ∑ k, A i k * (x k * G (X x)) := by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hsumD (k : Fin (n + 1)) :
      ∫ x, (∑ j, A j k * D (X x) j) ∂μ =
        ∑ j, A j k * ∫ x, D (X x) j ∂μ := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    · intro j hj
      exact (hDint j).const_mul _
  calc
    ∫ x, (∑ k, A i k * x k) * G (fun r => ∑ l, A r l * x l) ∂μ =
        ∫ x, ∑ k, A i k * (x k * G (X x)) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x => by rw [hsumEq])
    _ = ∑ k, A i k * ∫ x, x k * G (X x) ∂μ := by
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro k hk
            rw [integral_const_mul]
          · intro k hk
            exact hterm k
    _ = ∑ k, A i k * ∫ x, (∑ j, A j k * D (X x) j) ∂μ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hcoord k]
    _ = ∑ k, A i k * ∑ j, A j k * ∫ x, D (X x) j ∂μ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hsumD k]
    _ = ∑ j, (∑ k, A i k * A j k) * ∫ x, D (X x) j ∂μ := by
          calc
            _ = ∑ k, ∑ j, A i k * (A j k * ∫ x, D (X x) j ∂μ) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [Finset.mul_sum]
            _ = ∑ j, ∑ k, (A i k * A j k) *
                  ∫ x, D (X x) j ∂μ := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro j hj
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [Finset.sum_mul]


/-- The finite centered joint-Gaussian representation writes every Gaussian family as a linear image
of independent standard normals. The covariance is the row Gram matrix of the image matrix,
including when that matrix is singular. -/
theorem centeredJointlyGaussian_standardLinearRepresentation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (Z : Ω → Fin (n + 1) → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      P.map Z = (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
        (fun x => Matrix.mulVec A x) ∧
      ∀ i j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) =
        ∑ k, A i k * A j k := by
  classical
  obtain ⟨S, hS, hLaw, hEntry⟩ := represent P Z hZ
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := CFC.sqrt S
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let L : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) A
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hstd : stdGaussian E =
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
        (fun x => WithLp.toLp 2 x) := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    congr 1
    funext x
    have hb := b.sum_repr (WithLp.toLp 2 x)
    ext i
    simpa [b, EuclideanSpace.basisFun_repr] using (congrArg (fun y : E => y i) hb.symm).symm
  have hrootmap : ((stdGaussian E).map L).map (WithLp.ofLp) =
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
        (fun x => Matrix.mulVec A x) := by
    calc
      ((stdGaussian E).map L).map (WithLp.ofLp) =
          (stdGaussian E).map ((WithLp.ofLp) ∘ L) := by
            rw [Measure.map_map (WithLp.measurable_ofLp 2 (Fin (n + 1) → ℝ))
              L.continuous.measurable]
      _ = ((Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
          (fun x => WithLp.toLp 2 x)).map ((WithLp.ofLp) ∘ L) := by rw [hstd]
      _ = (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
          (((WithLp.ofLp) ∘ L) ∘ (fun x => WithLp.toLp 2 x)) := by
            rw [Measure.map_map (((WithLp.measurable_ofLp 2 (Fin (n + 1) → ℝ)).comp
              L.continuous.measurable)) (by fun_prop)]
      _ = _ := by
            congr 1
  let Y : Ω → E := fun ω => WithLp.toLp 2 (Z ω)
  have hmapY : P.map Y = multivariateGaussian 0 S := hLaw
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro i
    exact hZ.2.1 i
  have hYae : AEMeasurable Y P := by
    exact (WithLp.measurable_toLp 2 (Fin (n + 1) → ℝ)).aemeasurable.comp_aemeasurable hZae
  have hOfLp : Measurable (WithLp.ofLp : E → Fin (n + 1) → ℝ) :=
    WithLp.measurable_ofLp 2 (Fin (n + 1) → ℝ)
  have hmapZ : P.map Z =
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
        (fun x => Matrix.mulVec A x) := by
    calc
      P.map Z = (P.map Y).map (WithLp.ofLp) := by
        calc
          P.map Z = P.map (WithLp.ofLp ∘ Y) := by
            congr 1
          _ = (P.map Y).map (WithLp.ofLp) :=
            (AEMeasurable.map_map_of_aemeasurable hOfLp.aemeasurable hYae).symm
      _ = (multivariateGaussian 0 S).map (WithLp.ofLp) := by rw [hmapY]
      _ = ((stdGaussian E).map L).map (WithLp.ofLp) := by
        rw [multivariateGaussian]
        simp only [zero_add]
        rfl
      _ = _ := hrootmap
  have hAself : IsSelfAdjoint A := by
    dsimp [A]
    exact (CFC.sqrt_nonneg S).isSelfAdjoint
  have hAsq : A * A = S := by
    dsimp [A]
    exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hAsymm (i j : Fin (n + 1)) : A i j = A j i := by
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M i j) hAself
    simpa using h.symm
  refine ⟨A, hmapZ, ?_⟩
  intro i j
  rw [← hEntry i j]
  calc
    S i j = (A * A) i j := by rw [hAsq]
    _ = ∑ k, A i k * A j k := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hAsymm k j]


end DOZZ.Proofs
