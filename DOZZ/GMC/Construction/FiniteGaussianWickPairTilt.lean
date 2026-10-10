/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.Statements.GMC.GaussianVariance

/-! A pair of Wick weights is one finite-dimensional Gaussian tilt, with its cross covariance
factored out. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Under a finite-dimensional centered Gaussian law, the product of two Wick weights times any
nonnegative measurable observable is the two-root Cameron--Martin shift, with the cross-covariance
factor separated from the normalized joint tilt. No nonsingularity assumption is used. -/
theorem finite_gaussian_wick_pair_tilt
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z)
    (p q : ι) (γ : ℝ)
    (F : (ι → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω,
      ENNReal.ofReal (Real.exp (γ * Z ω p - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω p))) *
      ENNReal.ofReal (Real.exp (γ * Z ω q - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω q))) * F (Z ω) ∂P) =
    ENNReal.ofReal (Real.exp (γ ^ 2 / 2 *
      (DOZZ.gaussianCovariance P (fun ω => Z ω p) (fun ω => Z ω q) +
        DOZZ.gaussianCovariance P (fun ω => Z ω q) (fun ω => Z ω p)))) *
      (∫⁻ ω, F (fun i => Z ω i + γ *
        DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω p) + γ *
        DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω q)) ∂P) := by
  classical
  let a : ι → ℝ := fun i => (if i = p then γ else 0) + (if i = q then γ else 0)
  have hselect (g : ι → ℝ) (r : ι) :
      (∑ i, (if i = r then γ else 0) * g i) = γ * g r := by
    classical
    simp
  have hsum (g : ι → ℝ) : (∑ i, a i * g i) = γ * g p + γ * g q := by
    calc
      _ = (∑ i, (if i = p then γ else 0) * g i) +
          ∑ i, (if i = q then γ else 0) * g i := by
            simp only [a, add_mul, Finset.sum_add_distrib]
      _ = _ := by rw [hselect g p, hselect g q]
  have hlinear (ω : Ω) :
      (∑ i, a i * Z ω i) = γ * Z ω p + γ * Z ω q := hsum (fun i => Z ω i)
  have hrow (i : ι) :
      (∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) =
        γ * DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω p) +
          γ * DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω q) := by
    calc
      _ = (∑ j, (if j = p then γ else 0) *
            DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j)) +
          ∑ j, (if j = q then γ else 0) *
            DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              simp only [a]
              ring
      _ = _ := by
        rw [hselect, hselect]
  have hdouble : (∑ i, ∑ j, a i *
      DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) =
      γ ^ 2 * DOZZ.gaussianVariance P (fun ω => Z ω p) +
      γ ^ 2 * DOZZ.gaussianVariance P (fun ω => Z ω q) +
      γ ^ 2 * DOZZ.gaussianCovariance P (fun ω => Z ω p) (fun ω => Z ω q) +
      γ ^ 2 * DOZZ.gaussianCovariance P (fun ω => Z ω q) (fun ω => Z ω p) := by
    calc
      _ = ∑ i, a i * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω p) +
          γ * DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω q)) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              _ = ∑ j, a i * (DOZZ.gaussianCovariance P
                    (fun ω => Z ω i) (fun ω => Z ω j) * a j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = a i * ∑ j, DOZZ.gaussianCovariance P
                    (fun ω => Z ω i) (fun ω => Z ω j) * a j := by
                    rw [Finset.mul_sum]
              _ = _ := by rw [hrow]
      _ = ∑ i, ((a i * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω p))) +
          (a i * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω q)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, a i * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω p))) +
          ∑ i, a i * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω q)) := by
            rw [Finset.sum_add_distrib]
      _ = γ * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω p) (fun ω => Z ω p) +
          γ * DOZZ.gaussianCovariance P (fun ω => Z ω q) (fun ω => Z ω p)) +
          γ * (γ * DOZZ.gaussianCovariance P
            (fun ω => Z ω p) (fun ω => Z ω q) +
          γ * DOZZ.gaussianCovariance P (fun ω => Z ω q) (fun ω => Z ω q)) := by
            rw [hsum (fun i => γ * DOZZ.gaussianCovariance P
              (fun ω => Z ω i) (fun ω => Z ω p))]
            rw [hsum (fun i => γ * DOZZ.gaussianCovariance P
              (fun ω => Z ω i) (fun ω => Z ω q))]
            ring
      _ = _ := by
            simp only [DOZZ.gaussianVariance]
            ring
  have hweight (ω : Ω) :
      Real.exp (γ * Z ω p - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω p)) *
        Real.exp (γ * Z ω q - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω q)) =
      Real.exp (γ ^ 2 / 2 *
          (DOZZ.gaussianCovariance P (fun ω => Z ω p) (fun ω => Z ω q) +
            DOZZ.gaussianCovariance P (fun ω => Z ω q) (fun ω => Z ω p))) *
        Real.exp ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω j) * a j) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, hlinear ω, hdouble]
    congr 1
    ring
  have htilt := DOZZ.Proofs.finite_gaussian_tilt P Z hZ a F hF
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 / 2 *
    (DOZZ.gaussianCovariance P (fun ω => Z ω p) (fun ω => Z ω q) +
      DOZZ.gaussianCovariance P (fun ω => Z ω q) (fun ω => Z ω p))))
  calc
    _ = ∫⁻ ω, c * ENNReal.ofReal (Real.exp ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω j) * a j) / 2)) *
          F (Z ω) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), hweight ω,
          ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    _ = ∫⁻ ω, c * (ENNReal.ofReal (Real.exp ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω j) * a j) / 2)) *
          F (Z ω)) ∂P := by
        apply lintegral_congr_ae
        exact ae_of_all _ (fun ω => by ac_rfl)
    _ = c * (∫⁻ ω, ENNReal.ofReal (Real.exp ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P
            (fun ω => Z ω i) (fun ω => Z ω j) * a j) / 2)) *
          F (Z ω) ∂P) := by
        rw [lintegral_const_mul' c _ (by simp [c])]
    _ = _ := by
      rw [htilt]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [] with ω
      congr 1
      funext i
      rw [hrow i]
      ring

end DOZZ.Proofs
