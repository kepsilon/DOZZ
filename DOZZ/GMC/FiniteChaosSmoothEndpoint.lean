/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosInterpolationBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-! Endpoint Kahane comparison for smooth convex tests with bounded derivatives. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Smooth convex tests with bounded first and second derivatives satisfy finite Kahane order. -/
theorem kahane_finite_smooth_convex
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (F F' F'' : ℝ → ℝ) (B₁ B₂ : ℝ)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF''meas : Measurable F'') (hB₁ : ∀ x, ‖F' x‖ ≤ B₁)
    (hB₂ : ∀ x, ‖F'' x‖ ≤ B₂) (hF''nonneg : ∀ x, 0 ≤ x → 0 ≤ F'' x)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    (∫ ω, F (DOZZ.finiteChaosMass PX X a γ ω) ∂PX) ≤
      ∫ ω, F (DOZZ.finiteChaosMass PY Y a γ ω) ∂PY := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  let μ := PX.prod PY
  let vX : ι → ℝ := fun i => DOZZ.gaussianVariance PX (fun ω => X ω i)
  let vY : ι → ℝ := fun i => DOZZ.gaussianVariance PY (fun ω => Y ω i)
  let M : ℝ → ΩX × ΩY → ℝ := kahaneInterpolatedMass X Y vX vY a γ
  let T : ℝ → ΩX × ΩY → ℝ := fun t ω => F (M t ω)
  let D : ℝ → ΩX × ΩY → ℝ := kahaneInterpolatedTestDerivative X Y vX vY a γ F'
  let φ : ℝ → ℝ := fun t => ∫ ω, T t ω ∂μ
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hF'cont : Continuous F' := continuous_iff_continuousAt.mpr fun x => (hF' x).continuousAt
  have hB₁nonneg : 0 ≤ B₁ := (norm_nonneg (F' 0)).trans (hB₁ 0)
  have hvX (i : ι) : 0 ≤ vX i := by
    exact integral_nonneg fun ω => mul_self_nonneg (X ω i)
  have hvY (i : ι) : 0 ≤ vY i := by
    exact integral_nonneg fun ω => mul_self_nonneg (Y ω i)
  have hV : AEMeasurable (fun ω : ΩX × ΩY => (X ω.1, Y ω.2)) μ :=
    (aemeasurable_pi_iff.mpr hX.2.1).comp_fst.prodMk
      (aemeasurable_pi_iff.mpr hY.2.1).comp_snd
  have hM (s : ℝ) : AEMeasurable (M s) μ := by
    have h : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
        ∑ i, a i * Real.exp (γ * (Real.sqrt s * z.1 i + Real.sqrt (1 - s) * z.2 i) -
          γ ^ 2 / 2 * (s * vX i + (1 - s) * vY i))) := by fun_prop
    change AEMeasurable (fun ω => M s ω) μ
    simpa only [Function.comp_def, M, kahaneInterpolatedMass] using h.comp_aemeasurable hV
  have hT (s : ℝ) : AEStronglyMeasurable (T s) μ :=
    (hFcont.measurable.comp_aemeasurable (hM s)).aestronglyMeasurable
  have hD (s : ℝ) : AEStronglyMeasurable (D s) μ := by
    have h : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
        kahaneInterpolatedTestDerivative (fun x => x) (fun x => x) vX vY a γ F' s z) := by
      unfold kahaneInterpolatedTestDerivative kahaneInterpolatedMass
      fun_prop
    change AEStronglyMeasurable (fun ω => D s ω) μ
    simpa only [Function.comp_def, D, kahaneInterpolatedTestDerivative, kahaneInterpolatedMass] using
      (h.comp_aemeasurable hV).aestronglyMeasurable
  have hFgrowth (x : ℝ) : ‖F x‖ ≤ ‖F 0‖ + B₁ * ‖x‖ := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (fun y _ => (hF y).hasDerivWithinAt)
      (fun y _ => hB₁ y) convex_univ (mem_univ (0 : ℝ)) (mem_univ x)
    simp only [sub_zero] at h
    calc
      _ ≤ ‖F x - F 0‖ + ‖F 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F x - F 0) (F 0)
      _ ≤ _ := by linarith
  let b : ΩX × ΩY → ℝ := fun ω => ‖F 0‖ + B₁ * (∑ i, a i) *
    Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|))
  have hb : Integrable b μ := (integrable_const _).add
    ((kahaneEndpointAbsExp_integrable PX PY X Y hX hY γ).const_mul (B₁ * ∑ i, a i))
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ω : ΩX × ΩY) : ‖T s ω‖ ≤ b ω := by
    calc
      _ ≤ ‖F 0‖ + B₁ * ‖M s ω‖ := hFgrowth _
      _ ≤ _ := by
        change ‖F 0‖ + B₁ * ‖M s ω‖ ≤ ‖F 0‖ +
          (B₁ * ∑ i, a i) * Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|))
        apply add_le_add le_rfl
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (kahaneInterpolatedMass_norm_le_absExp X Y vX vY a hvX hvY ha γ s hs ω) hB₁nonneg
  have hInt (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : Integrable (T s) μ :=
    hb.mono' (hT s) (ae_of_all _ (hbound s hs))
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated (fun s _ => hT s) (fun s hs => ae_of_all _ (hbound s hs)) hb
    filter_upwards [] with ω
    have hMass : Continuous (fun s => M s ω) := by
      dsimp [M, kahaneInterpolatedMass]
      fun_prop
    exact (hFcont.comp hMass).continuousOn
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt φ (∫ ω, D t ω ∂μ) t ∧ (∫ ω, D t ω ∂μ) ≤ 0 := by
    let ε : ℝ := min t (1 - t) / 4
    have htpos : 0 < t := ht.1
    have htpos' : 0 < 1 - t := by linarith [ht.2]
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεt : 4 * ε ≤ t := by dsimp [ε]; linarith [min_le_left t (1 - t)]
    have hεt' : 4 * ε ≤ 1 - t := by dsimp [ε]; linarith [min_le_right t (1 - t)]
    let db : ΩX × ΩY → ℝ := fun ω => B₁ * (∑ i, a i) *
      Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|)) *
        (|γ| / (2 * Real.sqrt ε) * (∑ i, (|X ω.1 i| + |Y ω.2 i|)) +
          γ ^ 2 / 2 * ∑ i, |vX i - vY i|)
    have hdb := kahaneInterpolatedDerivativeEnvelope_integrable
      PX PY X Y hX hY vX vY a γ ε B₁
    have hDbound : ∀ᵐ ω ∂μ, ∀ s ∈ Metric.ball t ε, ‖D s ω‖ ≤ db ω := by
      filter_upwards [] with ω s hs
      have hsabs : |s - t| < ε := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
      have hsleft : ε ≤ s := by linarith [(abs_lt.mp hsabs).1]
      have hsright : ε ≤ 1 - s := by linarith [(abs_lt.mp hsabs).2]
      exact kahaneInterpolatedTestDerivative_norm_le_absExp X Y vX vY a hvX hvY ha
        γ ε s B₁ F' hB₁nonneg hB₁ hε hsleft hsright ω
    exact kahaneSmoothInterpolationExpectation_hasDerivAt_nonpos
      PX PY X Y hX hY a vX vY ha γ t ε F F' F'' B₁ B₂ hF hF'
      hF'cont.measurable hF''meas hB₁ hB₂ hF''nonneg hε (by linarith) (by linarith)
      (Filter.Eventually.of_forall hT) (hInt t ⟨ht.1.le, ht.2.le⟩) (hD t)
      db hdb hDbound (fun _ => rfl) (fun _ => rfl) hcov
  have hend := kahaneInterpolation_endpoint_le_of_derivative φ
    (fun t => ∫ ω, D t ω ∂μ) hcont (fun t ht => (hderiv t ht).1)
    (fun t ht => (hderiv t ht).2)
  have hzero : φ 0 = ∫ ω, F (DOZZ.finiteChaosMass PY Y a γ ω) ∂PY := by
    dsimp [φ, T, M, μ, kahaneInterpolatedMass]
    simp only [Real.sqrt_zero, Real.sqrt_one, zero_mul, one_mul, zero_add,
      sub_zero]
    change (∫ ω : ΩX × ΩY, F (DOZZ.finiteChaosMass PY Y a γ ω.2) ∂PX.prod PY) = _
    simpa only [probReal_univ, one_smul] using
      integral_fun_snd (μ := PX) (ν := PY) (fun ω => F (DOZZ.finiteChaosMass PY Y a γ ω))
  have hone : φ 1 = ∫ ω, F (DOZZ.finiteChaosMass PX X a γ ω) ∂PX := by
    dsimp [φ, T, M, μ, kahaneInterpolatedMass]
    simp only [Real.sqrt_zero, Real.sqrt_one, zero_mul, one_mul, add_zero, sub_self]
    change (∫ ω : ΩX × ΩY, F (DOZZ.finiteChaosMass PX X a γ ω.1) ∂PX.prod PY) = _
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := PX) (ν := PY) (fun ω => F (DOZZ.finiteChaosMass PX X a γ ω))
  rwa [hone, hzero] at hend


end DOZZ.Proofs
