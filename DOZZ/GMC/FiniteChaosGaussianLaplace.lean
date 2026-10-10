/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosLaplaceEndpoint
public import DOZZ.GMC.StandardGaussianProductStein

/-! Finite Gaussian Laplace comparison via square-root standard Gaussian representations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- The finite Laplace comparison for arbitrary centered jointly Gaussian vectors. Each possibly
singular Gaussian law is represented as a square matrix image of independent standard normals. -/
theorem kahane_finite_laplace_lintegral
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] {n : ℕ}
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → Fin (n + 1) → ℝ) (Y : ΩY → Fin (n + 1) → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) (γ s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) ∂PY := by
  classical
  have : IsProbabilityMeasure PX := hX.1
  have : IsProbabilityMeasure PY := hY.1
  obtain ⟨A, hXlaw, hXcov⟩ := centeredJointlyGaussian_standardLinearRepresentation PX X hX
  obtain ⟨B, hYlaw, hYcov⟩ := centeredJointlyGaussian_standardLinearRepresentation PY Y hY
  let μ := standardGaussianFinMeasure n
  let TX : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x => Matrix.mulVec A x
  let TY : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x => Matrix.mulVec B x
  have hXlaw' : PX.map X = μ.map TX := by
    simpa [TX, μ, standardGaussianFinMeasure] using hXlaw
  have hYlaw' : PY.map Y = μ.map TY := by
    simpa [TY, μ, standardGaussianFinMeasure] using hYlaw
  let FX : (Fin (n + 1) → ℝ) → ℝ := fun z =>
    Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ z)
  let FY : (Fin (n + 1) → ℝ) → ℝ := fun z =>
    Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ z)
  have hXae : AEMeasurable X PX := by
    apply AEMeasurable.of_eval
    intro i
    exact hX.2.1 i
  have hYae : AEMeasurable Y PY := by
    apply AEMeasurable.of_eval
    intro i
    exact hY.2.1 i
  have hFXcont : Continuous FX := by
    change Continuous (fun z => Real.exp (-s * finiteChaosVectorMass a
      (finiteChaosMatrixRowVariance A) γ z))
    fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight]
  have hFYcont : Continuous FY := by
    change Continuous (fun z => Real.exp (-s * finiteChaosVectorMass a
      (finiteChaosMatrixRowVariance B) γ z))
    fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight]
  have hFXbound (z : Fin (n + 1) → ℝ) : ‖FX z‖ ≤ 1 := by
    have hmass := finiteChaosVectorMass_nonneg a (finiteChaosMatrixRowVariance A) γ ha z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hs, hmass]
  have hFYbound (z : Fin (n + 1) → ℝ) : ‖FY z‖ ≤ 1 := by
    have hmass := finiteChaosVectorMass_nonneg a (finiteChaosMatrixRowVariance B) γ ha z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hs, hmass]
  have hFXsrc : Integrable (fun ω => FX (X ω)) PX :=
    Integrable.of_bound
      (hFXcont.aestronglyMeasurable.comp_aemeasurable hXae) 1
      (ae_of_all PX fun ω => hFXbound (X ω))
  have hFYsrc : Integrable (fun ω => FY (Y ω)) PY :=
    Integrable.of_bound
      (hFYcont.aestronglyMeasurable.comp_aemeasurable hYae) 1
      (ae_of_all PY fun ω => hFYbound (Y ω))
  have hFXmap : Integrable FX (PX.map X) :=
    (integrable_map_measure hFXcont.aestronglyMeasurable hXae).mpr hFXsrc
  have hFYmap : Integrable FY (PY.map Y) :=
    (integrable_map_measure hFYcont.aestronglyMeasurable hYae).mpr hFYsrc
  have hVarX (i : Fin (n + 1)) :
      DOZZ.gaussianVariance PX (fun ω => X ω i) = finiteChaosMatrixRowVariance A i := by
    simpa [DOZZ.gaussianVariance, finiteChaosMatrixRowVariance,
      finiteChaosMatrixRowCovariance] using hXcov i i
  have hVarY (i : Fin (n + 1)) :
      DOZZ.gaussianVariance PY (fun ω => Y ω i) = finiteChaosMatrixRowVariance B i := by
    simpa [DOZZ.gaussianVariance, finiteChaosMatrixRowVariance,
      finiteChaosMatrixRowCovariance] using hYcov i i
  have hmassX (ω : ΩX) : DOZZ.finiteChaosMass PX X a γ ω =
      finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ (X ω) := by
    simp [DOZZ.finiteChaosMass, finiteChaosVectorMass, finiteChaosVectorWeight, hVarX]
  have hmassY (ω : ΩY) : DOZZ.finiteChaosMass PY Y a γ ω =
      finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ (Y ω) := by
    simp [DOZZ.finiteChaosMass, finiteChaosVectorMass, finiteChaosVectorWeight, hVarY]
  have hrealX :
      ∫ ω, Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω) ∂PX =
        ∫ x, FX (TX x) ∂μ := by
    calc
      ∫ ω, Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω) ∂PX =
          ∫ ω, FX (X ω) ∂PX := by
            apply integral_congr_ae
            exact ae_of_all PX fun ω => by simp [FX, hmassX]
      _ = ∫ z, FX z ∂PX.map X :=
        (integral_map hXae hFXmap.aestronglyMeasurable).symm
      _ = ∫ z, FX z ∂μ.map TX := by rw [hXlaw']
      _ = ∫ x, FX (TX x) ∂μ := by
        exact integral_map (by fun_prop : AEMeasurable TX μ)
          (hFXcont.aestronglyMeasurable : AEStronglyMeasurable FX (μ.map TX))
  have hrealY :
      ∫ ω, Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω) ∂PY =
        ∫ x, FY (TY x) ∂μ := by
    calc
      ∫ ω, Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω) ∂PY =
          ∫ ω, FY (Y ω) ∂PY := by
            apply integral_congr_ae
            exact ae_of_all PY fun ω => by simp [FY, hmassY]
      _ = ∫ z, FY z ∂PY.map Y :=
        (integral_map hYae hFYmap.aestronglyMeasurable).symm
      _ = ∫ z, FY z ∂μ.map TY := by rw [hYlaw']
      _ = ∫ x, FY (TY x) ∂μ := by
        exact integral_map (by fun_prop : AEMeasurable TY μ)
          (hFYcont.aestronglyMeasurable : AEStronglyMeasurable FY (μ.map TY))
  have hMatrixCov (i j : Fin (n + 1)) :
      finiteChaosMatrixRowCovariance A i j ≤ finiteChaosMatrixRowCovariance B i j := by
    change (∑ k, A i k * A j k) ≤ (∑ k, B i k * B j k)
    rw [← hXcov i j, ← hYcov i j]
    exact hcov i j
  have hmatrix := finiteChaosMatrixLaplaceInterpolationExpectation_endpoint_le
    A B a γ s ha hs hMatrixCov
  have hEndpoints := finiteChaosMatrixLaplaceInterpolationExpectation_endpoint_eq
    A B a γ s ha hs
  have hreal :
      ∫ ω, Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω) ∂PX ≤
        ∫ ω, Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω) ∂PY := by
    rw [hrealX, hrealY]
    have hmatrix' := hmatrix
    rw [hEndpoints.1, hEndpoints.2] at hmatrix'
    exact hmatrix'
  have hExpIntX : Integrable
      (fun ω => Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) PX := by
    rw [show (fun ω => Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) =
      fun ω => FX (X ω) by funext ω; simp [FX, hmassX]]
    exact hFXsrc
  have hExpIntY : Integrable
      (fun ω => Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) PY := by
    rw [show (fun ω => Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) =
      fun ω => FY (Y ω) by funext ω; simp [FY, hmassY]]
    exact hFYsrc
  have hnonnegX : 0 ≤ᵐ[PX]
      (fun ω => Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) :=
    ae_of_all PX fun ω => Real.exp_nonneg _
  have hnonnegY : 0 ≤ᵐ[PY]
      (fun ω => Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) :=
    ae_of_all PY fun ω => Real.exp_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hExpIntX hnonnegX,
    ← ofReal_integral_eq_lintegral_ofReal hExpIntY hnonnegY]
  exact ENNReal.ofReal_le_ofReal hreal


end DOZZ.Proofs
