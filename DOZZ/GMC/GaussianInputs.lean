/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GFFStructure.GaussianClosure

/-! Finite Gaussian inputs for the proofs of the GMC tilting statements. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A centered Gaussian process restricts to a centered jointly Gaussian finite family. -/
theorem centeredJointlyGaussian_of_isGaussianProcess
    {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (P : Measure Ω) (Z : T → Ω → ℝ) (hZ : IsGaussianProcess Z P)
    (hMean : ∀ i, (∫ ω, Z i ω ∂P) = 0) :
    IsCenteredJointlyGaussian P (fun ω i => Z i ω) := by
  refine ⟨hZ.isProbabilityMeasure, (fun i => hZ.aemeasurable i), ?_⟩
  intro a
  let S : Ω → ℝ := fun ω => ∑ i, a i * Z i ω
  have hScaled : IsGaussianProcess (fun i => fun ω => a i * Z i ω) P := by
    simpa only [smul_eq_mul] using hZ.smul a
  have hLaw : HasGaussianLaw S P := by
    simpa only [S, smul_eq_mul] using hScaled.hasGaussianLaw_fun_sum (I := Finset.univ)
  have hMeanS : (∫ ω, S ω ∂P) = 0 := by
    dsimp [S]
    rw [integral_finsetSum]
    · simp only [integral_const_mul, hMean, mul_zero, Finset.sum_const_zero]
    · intro i hi
      exact (hZ.hasGaussianLaw_eval i).integrable.const_mul (a i)
  refine ⟨hLaw.memLp_two, ⟨(Var[S; P]).toNNReal, ?_⟩⟩
  rw [hLaw.map_eq_gaussianReal, hMeanS]

/-- Every finite family of evaluations of an equator GFF is centered jointly Gaussian. -/
theorem equatorGFF_finite_evaluations_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : ι → TestFn) :
    IsCenteredJointlyGaussian P (fun ω i => X ω (f i)) := by
  exact centeredJointlyGaussian_of_isGaussianProcess P
    (fun i ω => X ω (f i))
    (equatorGFF_test_family_isGaussianProcess X hX f)
    (fun i => equatorGFF_test_integral X hX (f i))

/-- A finite family of GFF evaluations remains jointly Gaussian after adjoining a centered
`L²` limit of test evaluations. -/
theorem equatorGFF_finite_evaluations_with_L_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (L : Ω → ℝ)
    (hL : IsGaussianL2Limit P X L) (f : ι → TestFn) :
    IsCenteredJointlyGaussian P
      (fun (ω : Ω) (i : Option ι) => match i with
        | none => L ω
        | some j => X ω (f j)) := by
  obtain ⟨hLmem, fL, hLapprox⟩ := hL
  let _ : IsProbabilityMeasure P := hX.1
  let Z : ℕ → Option ι → Ω → ℝ := fun n i ω =>
    match i with
    | none => X ω (fL n)
    | some j => X ω (f j)
  let W : Option ι → Ω → ℝ := fun i ω =>
    match i with
    | none => L ω
    | some j => X ω (f j)
  have hZ : ∀ n, IsGaussianProcess (Z n) P := by
    intro n
    have h := equatorGFF_test_family_isGaussianProcess X hX
      (fun i : Option ι => match i with
        | none => fL n
        | some j => f j)
    exact h.congr fun i => by
      cases i <;> rfl
  have hW : ∀ i, MemLp (W i) 2 P := by
    intro i
    cases i with
    | none => exact hLmem
    | some j => exact equatorGFF_test_memLp X hX (f j)
  have hApprox : ∀ i,
      Tendsto (fun n => eLpNorm (fun ω => Z n i ω - W i ω) 2 P)
        atTop (𝓝 0) := by
    intro i
    cases i with
    | none =>
        have hcomm : ∀ n,
            eLpNorm (fun ω => X ω (fL n) - L ω) 2 P =
              eLpNorm (fun ω => L ω - X ω (fL n)) 2 P := by
          intro n
          exact eLpNorm_sub_comm _ _ _ _
        simpa only [Z, W, hcomm] using hLapprox
    | some j =>
        convert (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) using 1
        · funext n
          simp [Z, W]
  have hLimit := isGaussianProcess_of_eLpNorm_sub Z W hZ hW hApprox
  have hMeanL : (∫ ω, L ω ∂P) = 0 := by
    have hcomm : ∀ n,
        eLpNorm (fun ω => X ω (fL n) - L ω) 2 P =
          eLpNorm (fun ω => L ω - X ω (fL n)) 2 P := by
      intro n
      exact eLpNorm_sub_comm _ _ _ _
    have hLapprox' : Tendsto
        (fun n => eLpNorm (fun ω => X ω (fL n) - L ω) 2 P) atTop (𝓝 0) := by
      simpa only [hcomm] using hLapprox
    exact integral_eq_zero_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (fL n)) hLmem
      (fun n => equatorGFF_test_integral X hX (fL n)) hLapprox'
  simpa only [W] using
    centeredJointlyGaussian_of_isGaussianProcess P W hLimit fun i => by
      cases i with
      | none => exact hMeanL
      | some j => exact equatorGFF_test_integral X hX (f j)

end DOZZ.Proofs
