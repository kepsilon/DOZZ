/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.GaussianInputs
public import DOZZ.GFFStructure.GaussianClosure
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Equality of finite test-evaluation laws for equator GFFs on arbitrary probability spaces. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions InnerProductSpace RealInnerProductSpace

namespace DOZZ.Proofs

/-- Any finite list of test evaluations has the same joint law under two equator GFF models.
Both vectors are Gaussian, centered, and have the same covariance matrix `gffCov`. -/
theorem equatorGFF_finite_test_evaluation_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    {ι : Type*} [Fintype ι] (f : ι → TestFn) :
    Measure.map (fun ω i => X ω (f i)) P =
      Measure.map (fun ω i => X' ω (f i)) P' := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let _ : IsProbabilityMeasure P' := hX'.1
  let E := EuclideanSpace ℝ ι
  let L : (ι → ℝ) ≃L[ℝ] E := (PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℝ).symm
  let TX : Ω → E := fun ω => L (fun i => X ω (f i))
  let TY : Ω' → E := fun ω => L (fun i => X' ω (f i))
  have hXjoint : IsCenteredJointlyGaussian P (fun ω i => X ω (f i)) :=
    equatorGFF_finite_evaluations_jointly_gaussian P X hX f
  have hYjoint : IsCenteredJointlyGaussian P' (fun ω i => X' ω (f i)) :=
    equatorGFF_finite_evaluations_jointly_gaussian P' X' hX' f
  have hXlinear : ∀ a : ι → ℝ,
      HasGaussianLaw (fun ω => ∑ i, a i * X ω (f i)) P := by
    intro a
    obtain ⟨v, hmap⟩ := (hXjoint.2.2 a).2
    have hsum : AEMeasurable (fun ω => ∑ i, a i * X ω (f i)) P :=
      (hXjoint.2.2 a).1.aemeasurable
    exact HasLaw.hasGaussianLaw ⟨hsum, hmap⟩
  have hYlinear : ∀ a : ι → ℝ,
      HasGaussianLaw (fun ω => ∑ i, a i * X' ω (f i)) P' := by
    intro a
    obtain ⟨v, hmap⟩ := (hYjoint.2.2 a).2
    have hsum : AEMeasurable (fun ω => ∑ i, a i * X' ω (f i)) P' :=
      (hYjoint.2.2 a).1.aemeasurable
    exact HasLaw.hasGaussianLaw ⟨hsum, hmap⟩
  have hXpi : HasGaussianLaw (fun ω i => X ω (f i)) P :=
    hasGaussianLaw_pi_of_linearCombinations
      (fun i ω => X ω (f i))
      (fun i => (hX.2 (f i)).1.aemeasurable) hXlinear
  have hYpi : HasGaussianLaw (fun ω i => X' ω (f i)) P' :=
    hasGaussianLaw_pi_of_linearCombinations
      (fun i ω => X' ω (f i))
      (fun i => (hX'.2 (f i)).1.aemeasurable) hYlinear
  have hXeuclid : HasGaussianLaw TX P := by
    simpa only [TX, Function.comp_def] using hXpi.map_equiv L
  have hYeuclid : HasGaussianLaw TY P' := by
    simpa only [TY, Function.comp_def] using hYpi.map_equiv L
  have hTXmeas : AEMeasurable TX P := hXeuclid.aemeasurable
  have hTYmeas : AEMeasurable TY P' := hYeuclid.aemeasurable
  have hTXgauss : IsGaussian (P.map TX) := hXeuclid.isGaussian_map
  have hTYgauss : IsGaussian (P'.map TY) := hYeuclid.isGaussian_map
  let _ : IsGaussian (P.map TX) := hTXgauss
  let _ : IsGaussian (P'.map TY) := hTYgauss
  have hmeanX : (P.map TX)[id] = 0 := by
    have hIdIntX : Integrable id (P.map TX) := IsGaussian.integrable_id
    rw [integral_map hTXmeas hIdIntX.aestronglyMeasurable]
    have hXcoord : ∀ i, Integrable (fun ω => X ω (f i)) P := fun i =>
      (equatorGFF_test_hasGaussianLaw X hX (f i)).integrable
    have hXsourceMean : (∫ ω, (fun i => X ω (f i)) ∂P) = 0 := by
      ext i
      rw [MeasureTheory.eval_integral hXcoord i]
      exact equatorGFF_test_integral X hX (f i)
    have hXvecMean : L.symm (∫ ω, TX ω ∂P) = 0 := by
      rw [← L.symm.integral_comp_comm (fun ω => TX ω)]
      simpa [TX] using hXsourceMean
    simpa using congrArg L hXvecMean
  have hmeanY : (P'.map TY)[id] = 0 := by
    have hIdIntY : Integrable id (P'.map TY) := IsGaussian.integrable_id
    rw [integral_map hTYmeas hIdIntY.aestronglyMeasurable]
    have hYcoord : ∀ i, Integrable (fun ω => X' ω (f i)) P' := fun i =>
      (equatorGFF_test_hasGaussianLaw X' hX' (f i)).integrable
    have hYsourceMean : (∫ ω, (fun i => X' ω (f i)) ∂P') = 0 := by
      ext i
      rw [MeasureTheory.eval_integral hYcoord i]
      exact equatorGFF_test_integral X' hX' (f i)
    have hYvecMean : L.symm (∫ ω, TY ω ∂P') = 0 := by
      rw [← L.symm.integral_comp_comm (fun ω => TY ω)]
      simpa [TY] using hYsourceMean
    simpa using congrArg L hYvecMean
  have hcov (u v : E) :
      covarianceBilin (P.map TX) u v = covarianceBilin (P'.map TY) u v := by
    rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
    rw [covariance_map (by fun_prop) (by fun_prop) hTXmeas,
      covariance_map (by fun_prop) (by fun_prop) hTYmeas]
    change covariance (fun ω => ⟪u, TX ω⟫_ℝ) (fun ω => ⟪v, TX ω⟫_ℝ) P =
      covariance (fun ω => ⟪u, TY ω⟫_ℝ) (fun ω => ⟪v, TY ω⟫_ℝ) P'
    have hTXcoord (ω : Ω) (i : ι) : TX ω i = X ω (f i) := by
      change (L (fun j => X ω (f j))) i = X ω (f i)
      rfl
    have hTYcoord (ω : Ω') (i : ι) : TY ω i = X' ω (f i) := by
      change (L (fun j => X' ω (f j))) i = X' ω (f i)
      rfl
    have hinnerX : (fun ω => ⟪u, TX ω⟫_ℝ) =
        fun ω => ∑ i, u i * X ω (f i) := by
      funext ω
      rw [PiLp.inner_apply]
      simp_rw [hTXcoord]
      simp [mul_comm]
    have hinnerY : (fun ω => ⟪u, TY ω⟫_ℝ) =
        fun ω => ∑ i, u i * X' ω (f i) := by
      funext ω
      rw [PiLp.inner_apply]
      simp_rw [hTYcoord]
      simp [mul_comm]
    have hinnerX' : (fun ω => ⟪v, TX ω⟫_ℝ) =
        fun ω => ∑ i, v i * X ω (f i) := by
      funext ω
      rw [PiLp.inner_apply]
      simp_rw [hTXcoord]
      simp [mul_comm]
    have hinnerY' : (fun ω => ⟪v, TY ω⟫_ℝ) =
        fun ω => ∑ i, v i * X' ω (f i) := by
      funext ω
      rw [PiLp.inner_apply]
      simp_rw [hTYcoord]
      simp [mul_comm]
    rw [hinnerX, hinnerX', hinnerY, hinnerY',
      covariance_fun_sum_fun_sum
        (hX := fun i => (equatorGFF_test_memLp X hX (f i)).const_mul (u.ofLp i))
        (hY := fun i => (equatorGFF_test_memLp X hX (f i)).const_mul (v.ofLp i)),
      covariance_fun_sum_fun_sum
        (hX := fun i => (equatorGFF_test_memLp X' hX' (f i)).const_mul (u.ofLp i))
        (hY := fun i => (equatorGFF_test_memLp X' hX' (f i)).const_mul (v.ofLp i))]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right,
      equatorGFF_test_covariance X hX, equatorGFF_test_covariance X' hX']
  have hmean : (P.map TX)[id] = (P'.map TY)[id] := hmeanX.trans hmeanY.symm
  have hcovBilin : covarianceBilin (P.map TX) = covarianceBilin (P'.map TY) := by
    ext u v
    exact hcov u v
  have hEqEuclid : P.map TX = P'.map TY := IsGaussian.ext hmean hcovBilin
  have hXvecMeas : Measurable (fun ω i => X ω (f i)) :=
    measurable_pi_iff.mpr fun i => (hX.2 (f i)).1
  have hYvecMeas : Measurable (fun ω i => X' ω (f i)) :=
    measurable_pi_iff.mpr fun i => (hX'.2 (f i)).1
  have hTXmeas' : Measurable TX := L.continuous.measurable.comp hXvecMeas
  have hTYmeas' : Measurable TY := L.continuous.measurable.comp hYvecMeas
  calc
    Measure.map (fun ω i => X ω (f i)) P = (P.map TX).map L.symm := by
      rw [Measure.map_map L.symm.continuous.measurable hTXmeas']
      congr 1
    _ = (P'.map TY).map L.symm := congrArg (fun μ => μ.map L.symm) hEqEuclid
    _ = Measure.map (fun ω i => X' ω (f i)) P' := by
      rw [Measure.map_map L.symm.continuous.measurable hTYmeas']
      congr 1


end DOZZ.Proofs
