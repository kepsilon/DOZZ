/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianIntegrationByParts
public import DOZZ.GMC.FiniteGaussianExponentialIntegrability

/-! Gaussian integration by parts for smooth tests with exponential-linear growth. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- A finite Gaussian integration-by-parts formula for a measurable test and its gradient with
exponential-linear growth. The envelope is integrable for every centered jointly Gaussian vector,
including singular ones. -/
theorem finite_gaussian_integration_by_parts_of_absExp_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (i : ι)
    (G : (ι → ℝ) → ℝ) (D : (ι → ℝ) → ι → ℝ)
    (hGmeas : Measurable G) (hDmeas : ∀ j, Measurable (fun z => D z j))
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (M : ℝ) (hM : 0 ≤ M)
    (hGbound : ∀ z, ‖G z‖ ≤ M * Real.exp (∑ j, c j * |z j|))
    (hDbound : ∀ z j, ‖D z j‖ ≤ M * Real.exp (∑ j, c j * |z j|))
    (hGdir : ∀ (x d : ι → ℝ) t,
      HasDerivAt (fun s => G (fun j => x j + s * d j))
        (∑ j, d j * D (fun j => x j + t * d j) j) t) :
    ∫ ω, Z ω i * G (Z ω) ∂P =
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        ∫ ω, D (Z ω) j ∂P := by
  classical
  let var : ℝ := gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)
  let shift : ι → ℝ := fun j =>
    gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i)
  let baseExp : Ω → ℝ := fun ω => Real.exp (∑ j, c j * |Z ω j|)
  let c' : ι → ℝ := fun j => c j + if j = i then 1 else 0
  let enlargedExp : Ω → ℝ := fun ω => Real.exp (∑ j, c' j * |Z ω j|)
  have hbaseExp : Integrable baseExp P := by
    simpa [baseExp] using centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ c
  have hcoordBaseExp : Integrable (fun ω => Z ω i * baseExp ω) P := by
    simpa [baseExp] using
      centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable P Z hZ c i
  have hlargeExp : Integrable enlargedExp P := by
    simpa [enlargedExp, c'] using
      centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ c'
  have hcoordLargeExp : Integrable (fun ω => Z ω i * enlargedExp ω) P := by
    simpa [enlargedExp, c'] using
      centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable P Z hZ c' i
  have hcov_symm (j : ι) :
      gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) = shift j := by
    simp [shift, gaussianCovariance, mul_comm]
  have hshiftBound : ∀ ω t,
      ∑ j, c j * |Z ω j + t * shift j| ≤
        ∑ j, c j * |Z ω j| + |t| * ∑ j, c j * |shift j| := by
    intro ω t
    calc
      _ ≤ ∑ j, c j * (|Z ω j| + |t| * |shift j|) := by
        apply Finset.sum_le_sum
        intro j hj
        have habs : |Z ω j + t * shift j| ≤ |Z ω j| + |t| * |shift j| := by
          calc
            _ ≤ |Z ω j| + |t * shift j| := abs_add_le _ _
            _ = |Z ω j| + |t| * |shift j| := by rw [abs_mul]
        exact mul_le_mul_of_nonneg_left habs (hc j)
      _ = (∑ j, c j * |Z ω j|) + |t| * ∑ j, c j * |shift j| := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        calc
          _ = ∑ j, |t| * (c j * |shift j|) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = |t| * ∑ j, c j * |shift j| := by rw [Finset.mul_sum]
  have hshiftExpBound (ω : Ω) (t : ℝ) :
      Real.exp (∑ j, c j * |Z ω j + t * shift j|) ≤
        Real.exp (∑ j, c j * |Z ω j|) *
          Real.exp (|t| * ∑ j, c j * |shift j|) := by
    calc
      _ ≤ Real.exp ((∑ j, c j * |Z ω j|) + |t| * ∑ j, c j * |shift j|) :=
        Real.exp_le_exp.mpr (hshiftBound ω t)
      _ = _ := by rw [Real.exp_add]
  let shiftFactor : ℝ := Real.exp (∑ j, c j * |shift j|)
  have hshiftFactor : 0 ≤ shiftFactor := by positivity
  have hGint : Integrable (fun ω => G (Z ω)) P := by
    apply (hbaseExp.const_mul M).mono'
    · exact hGmeas.aestronglyMeasurable.comp_aemeasurable
        (by
          apply AEMeasurable.of_eval
          intro j
          exact hZ.2.1 j)
    · filter_upwards [] with ω
      simpa [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hM (Real.exp_nonneg _)), baseExp] using hGbound (Z ω)
  have hDint (j : ι) : Integrable (fun ω => D (Z ω) j) P := by
    apply (hbaseExp.const_mul M).mono'
    · exact (hDmeas j).aestronglyMeasurable.comp_aemeasurable (by
        apply AEMeasurable.of_eval
        intro k
        exact hZ.2.1 k)
    · filter_upwards [] with ω
      simpa [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hM (Real.exp_nonneg _)), baseExp] using hDbound (Z ω) j
  have hShiftInt : ∀ t, Integrable
      (fun ω => G (fun j => Z ω j + t * shift j)) P := by
    intro t
    let sf : ℝ := Real.exp (|t| * ∑ j, c j * |shift j|)
    have hmeas : AEStronglyMeasurable
        (fun ω => G (fun j => Z ω j + t * shift j)) P := by
      exact hGmeas.aestronglyMeasurable.comp_aemeasurable (by
        apply AEMeasurable.of_eval
        intro j
        exact (hZ.2.1 j).add (aemeasurable_const.mul (aemeasurable_const)) )
    have hdom : Integrable (fun ω => (M * sf) * baseExp ω) P :=
      (hbaseExp.const_mul (M * sf))
    apply hdom.mono' hmeas
    filter_upwards [] with ω
    have hbound : ‖G (fun j => Z ω j + t * shift j)‖ ≤ M * sf * baseExp ω := by
      calc
        _ ≤ M * Real.exp (∑ j, c j * |Z ω j + t * shift j|) := hGbound _
        _ ≤ M * (baseExp ω * sf) := by
          dsimp [sf]
          exact mul_le_mul_of_nonneg_left (hshiftExpBound ω t) hM
        _ = M * sf * baseExp ω := by ring
    exact hbound
  have hLmeas : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable
      (fun ω => Real.exp (t * Z ω i - t ^ 2 / 2 * var) * G (Z ω)) P := by
    filter_upwards [] with t
    have harg : AEStronglyMeasurable
        (fun ω => t * Z ω i - t ^ 2 / 2 * var) P := by
      exact (hZ.2.1 i).aestronglyMeasurable.const_mul t |>.sub
        (aestronglyMeasurable_const.mul_const _)
    exact (Real.continuous_exp.comp_aestronglyMeasurable harg).mul
      hGint.aestronglyMeasurable
  have hLint : Integrable
      (fun ω => Real.exp (0 * Z ω i - 0 ^ 2 / 2 * var) * G (Z ω)) P := by
    simpa using hGint.const_mul 1
  have hLDmeas : AEStronglyMeasurable
      (fun ω => (Z ω i - 0 * var) *
        Real.exp (0 * Z ω i - 0 ^ 2 / 2 * var) * G (Z ω)) P := by
    have hbase := (hZ.2.1 i).aestronglyMeasurable.mul hGint.aestronglyMeasurable
    exact hbase.congr (ae_of_all P fun ω => by simp)
  have hLenv : Integrable enlargedExp P := hlargeExp
  have hLcoordenv : Integrable (fun ω => Z ω i * enlargedExp ω) P := hcoordLargeExp
  let tiltConst : ℝ := Real.exp (|var| / 2)
  have htiltConst : 0 ≤ tiltConst := by positivity
  let bL : Ω → ℝ := fun ω => M * tiltConst *
    (|Z ω i| + |var|) * enlargedExp ω
  have hbL : Integrable bL P := by
    have hcoordAbs : Integrable (fun ω => |Z ω i| * enlargedExp ω) P := by
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), enlargedExp] using
        hLcoordenv.norm
    have hsum := (hcoordAbs.const_mul (M * tiltConst)).add
      (hLenv.const_mul (M * tiltConst * |var|))
    convert hsum using 1; ext ω; simp [bL]; ring
  have hLbound : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      ‖(Z ω i - t * var) * Real.exp (t * Z ω i - t ^ 2 / 2 * var) * G (Z ω)‖ ≤ bL ω := by
    filter_upwards [] with ω t ht
    have ht' : |t| ≤ 1 := by
      have : |t - 0| < 1 := by simpa [Real.dist_eq] using ht
      simpa using (le_of_lt this)
    have harg : t * Z ω i - t ^ 2 / 2 * var ≤
        |Z ω i| + |var| / 2 := by
      have htSq : t ^ 2 ≤ 1 := by
        nlinarith [sq_abs t, sq_nonneg (|t|), abs_nonneg t]
      calc
        _ ≤ |t| * |Z ω i| + t ^ 2 / 2 * |var| := by
          have hfirst : t * Z ω i ≤ |t| * |Z ω i| := by
            calc
              _ ≤ |t * Z ω i| := le_abs_self _
              _ = |t| * |Z ω i| := abs_mul _ _
          have hsecond : -(t ^ 2 / 2 * var) ≤ t ^ 2 / 2 * |var| := by
            have ht2 : 0 ≤ t ^ 2 / 2 := by positivity
            calc
              _ = (t ^ 2 / 2) * (-var) := by ring
              _ ≤ (t ^ 2 / 2) * |var| :=
                mul_le_mul_of_nonneg_left (by simpa using (le_abs_self (-var))) ht2
          nlinarith
        _ ≤ |Z ω i| + |var| / 2 := by nlinarith [abs_nonneg (Z ω i), abs_nonneg var]
    have hweight : Real.exp (t * Z ω i - t ^ 2 / 2 * var) ≤
        tiltConst * Real.exp (|Z ω i|) := by
      calc
        _ ≤ Real.exp (|Z ω i| + |var| / 2) := Real.exp_le_exp.mpr harg
        _ = _ := by rw [Real.exp_add]; simp [tiltConst, mul_comm]
    have hsum : ∑ j, c' j * |Z ω j| =
        (∑ j, c j * |Z ω j|) + |Z ω i| := by
      dsimp [c']
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have hdelta : ∑ j, (if j = i then 1 else 0) * |Z ω j| = |Z ω i| := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hne
          have hij : i ≠ j := fun h => hne h.symm
          simp [hne]
        · simp
      rw [hdelta]
    have hexp : enlargedExp ω = baseExp ω * Real.exp |Z ω i| := by
      dsimp [enlargedExp, baseExp]
      rw [hsum, Real.exp_add]
    have hlin : |Z ω i - t * var| ≤ |Z ω i| + |var| := by
      calc
        _ ≤ |Z ω i| + |t * var| := abs_sub _ _
        _ = |Z ω i| + |t| * |var| := by rw [abs_mul]
        _ ≤ |Z ω i| + |var| := by nlinarith [abs_nonneg var]
    have hGbase : ‖G (Z ω)‖ ≤ M * baseExp ω := by
      simpa [baseExp] using hGbound (Z ω)
    calc
      _ = |Z ω i - t * var| *
          Real.exp (t * Z ω i - t ^ 2 / 2 * var) * ‖G (Z ω)‖ := by
            simp [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (Real.exp_nonneg _), mul_assoc]
      _ ≤ (|Z ω i| + |var|) *
          (tiltConst * Real.exp (|Z ω i|)) * (M * baseExp ω) := by
            gcongr
      _ = bL ω := by
            dsimp [bL]
            rw [hexp]
            dsimp [tiltConst]
            ring
  have hLdiff : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      HasDerivAt
        (fun s => Real.exp (s * Z ω i - s ^ 2 / 2 * var) * G (Z ω))
        ((Z ω i - t * var) * Real.exp (t * Z ω i - t ^ 2 / 2 * var) * G (Z ω)) t := by
    filter_upwards [] with ω t ht
    have hlin : HasDerivAt (fun s : ℝ => s * Z ω i - s ^ 2 / 2 * var)
        (Z ω i - t * var) t := by
      convert ((hasDerivAt_id t).const_mul (Z ω i)).sub
        (((hasDerivAt_id t).pow 2).const_mul (var / 2)) using 1
      · ext s
        simp [id_eq]
        ring_nf
      · simp [id_eq]
        ring_nf
    have hexp := (Real.hasDerivAt_exp (t * Z ω i - t ^ 2 / 2 * var)).comp t hlin
    convert hexp.const_mul (G (Z ω)) using 1
    · ext s
      simp
      ring
    · ring_nf
  have hRmeas : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable
      (fun ω => G (fun j => Z ω j + t * shift j)) P := by
    filter_upwards [] with t
    have harg : AEMeasurable (fun ω => fun j => Z ω j + t * shift j) P := by
      apply AEMeasurable.of_eval
      intro j
      exact (hZ.2.1 j).add aemeasurable_const
    exact hGmeas.aestronglyMeasurable.comp_aemeasurable harg
  have hRderivMeas : AEStronglyMeasurable
      (fun ω => ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * D (Z ω) j) P := by
    apply Finset.univ.aestronglyMeasurable_fun_sum
    intro j hj
    exact aestronglyMeasurable_const.mul
      ((hDmeas j).aestronglyMeasurable.comp_aemeasurable (by
        apply AEMeasurable.of_eval
        intro k
        exact hZ.2.1 k))
  let shiftMass : ℝ := ∑ j, c j * |shift j|
  let bR : Ω → ℝ := fun ω =>
    (∑ j, |gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j)|) *
      M * Real.exp shiftMass * baseExp ω
  have hbR : Integrable bR P := by
    exact hbaseExp.const_mul _
  have hRbound : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      ‖∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
        D (fun j => Z ω j + t * gaussianCovariance P (fun ω' => Z ω' j)
          (fun ω' => Z ω' i)) j‖ ≤ bR ω := by
    filter_upwards [] with ω t ht
    calc
      ‖∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
          D (fun j => Z ω j + t * shift j) j‖ ≤
          ∑ j, ‖gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
            D (fun j => Z ω j + t * shift j) j‖ := norm_sum_le _ _
      _ ≤ ∑ j, |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
          (M * (baseExp ω * Real.exp shiftMass)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hD := hDbound (fun k => Z ω k + t * shift k) j
        have hshift := hshiftExpBound ω t
        have ht' : |t| ≤ 1 := by
          have ht'' : |t - 0| < 1 := by simpa [Real.dist_eq] using ht
          simpa using (le_of_lt ht'')
        have hshiftMassNonneg : 0 ≤ shiftMass := by
          dsimp [shiftMass]
          exact Finset.sum_nonneg fun k hk => mul_nonneg (hc k) (abs_nonneg (shift k))
        have hfactor : Real.exp (|t| * shiftMass) ≤ Real.exp shiftMass := by
          apply Real.exp_le_exp.mpr
          calc
            |t| * shiftMass ≤ 1 * shiftMass :=
              mul_le_mul_of_nonneg_right ht' hshiftMassNonneg
            _ = shiftMass := by ring
        have hterm : ‖D (fun k => Z ω k + t * shift k) j‖ ≤
            M * (baseExp ω * Real.exp shiftMass) := by
          calc
            _ ≤ M * Real.exp (∑ k, c k * |Z ω k + t * shift k|) := hD
            _ ≤ M * (baseExp ω * Real.exp (|t| * shiftMass)) := by
              exact mul_le_mul_of_nonneg_left hshift hM
            _ ≤ M * (baseExp ω * Real.exp shiftMass) := by gcongr
        calc
          _ = |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
                ‖D (fun k => Z ω k + t * shift k) j‖ := by
              rw [norm_mul, Real.norm_eq_abs]
          _ ≤ |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
                (M * (baseExp ω * Real.exp shiftMass)) :=
              mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
          _ = |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
                (M * (baseExp ω * Real.exp shiftMass)) := by ring
      _ = (∑ j, |gaussianCovariance P (fun ω' => Z ω' i)
            (fun ω' => Z ω' j)|) * (M * (baseExp ω * Real.exp shiftMass)) := by
        rw [← Finset.sum_mul]
      _ = bR ω := by
        dsimp [bR]
        ring
  have hRdiff : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      HasDerivAt
        (fun s => G (fun j => Z ω j + s *
          gaussianCovariance P (fun ω' => Z ω' j) (fun ω' => Z ω' i)))
        (∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
          D (fun j => Z ω j + t *
            gaussianCovariance P (fun ω' => Z ω' j) (fun ω' => Z ω' i)) j) t := by
    filter_upwards [] with ω t ht
    have h := hGdir (fun j => Z ω j) shift t
    simpa [shift, hcov_symm] using h
  exact finite_gaussian_integration_by_parts P Z hZ i G hGmeas D
    (fun j => hDint j) hShiftInt 1 (by norm_num)
    hLmeas hLint hLDmeas bL hbL hLbound hLdiff
    hRmeas hRderivMeas bR hbR hRbound hRdiff


end DOZZ.Proofs
