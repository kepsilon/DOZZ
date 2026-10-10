/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.AdmissibleGMCRestriction
public import DOZZ.GMC.Moments.ExactScaleLimit
public import DOZZ.GMC.Moments.OpenBallApproximation
public import DOZZ.GMC.Moments.SetMassMeasurable

/-! Exact affine scaling of open-ball masses for arbitrary `IsGMCOf` versions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem gmc_test_integral_aemeasurable_of_support
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : MeasurableSet K)
    (hKunit : ∀ x ∈ K, ‖x‖ ≤ 1)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hfzero : ∀ x, x ∉ K → f x = 0) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  obtain ⟨Xc, hXc, hMlim⟩ := hM.2
  have hcut (n : ℕ) : AEMeasurable
      (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ n ω) P :=
    regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ n K hK hKunit f
      f.continuous.measurable hfzero
  have hconv := (hMlim f).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact hconv.aemeasurable hcut

/-- For a disk compactly contained in the logarithmic chart, the affine scaling law holds for its
mass, including the independent scalar Gaussian. The result applies to every `IsGMCOf` version. -/
theorem gmc_affine_openBall_mass_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1) :
    Measure.map (fun ω : Ω => fun _ : Fin 1 =>
      (M ω (Metric.ball a (c * R))).toReal) P =
    Measure.map (fun p : Ω × ℝ => fun _ : Fin 1 =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (M p.1 (Metric.ball 0 R)).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let σ : ℝ := -Real.log c
  let G : Measure ℝ := gaussianReal 0 ⟨σ,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have hG : IsProbabilityMeasure G := by
    simpa [G, σ] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure (P.prod G) := inferInstance
  let f : ℕ → BoundedContinuousFunction ℂ ℝ := fun n => openBallAffineApprox a c R n
  let g : ℕ → BoundedContinuousFunction ℂ ℝ := fun n => openBallApprox 0 R n
  have hfSupport (n : ℕ) : tsupport (f n : ℂ → ℝ) ⊆ Metric.closedBall a (c * R) :=
    openBallAffineApprox_tsupport_subset hc n
  have hgSupport (n : ℕ) : tsupport (g n : ℂ → ℝ) ⊆ Metric.closedBall 0 R :=
    openBallApprox_tsupport_subset 0 R n
  have hfzero (n : ℕ) (x : ℂ) (hx : x ∉ Metric.closedBall a (c * R)) : f n x = 0 :=
    boundedContinuousFunction_eq_zero_off_tsupport_subset (f n)
      (Metric.closedBall a (c * R)) (hfSupport n) x hx
  have hgzero (n : ℕ) (x : ℂ) (hx : x ∉ Metric.closedBall 0 R) : g n x = 0 :=
    boundedContinuousFunction_eq_zero_off_tsupport_subset (g n)
      (Metric.closedBall 0 R) (hgSupport n) x hx
  have htargetUnit : ∀ x ∈ Metric.closedBall a (c * R), ‖x‖ ≤ 1 := by
    intro x hx
    have hx' : ‖x - a‖ ≤ c * R := by
      change dist x a ≤ c * R at hx
      simpa [dist_eq_norm] using hx
    calc
      ‖x‖ = ‖(x - a) + a‖ := by congr 1; abel
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ c * R + ‖a‖ := by nlinarith
      _ ≤ 1 := by linarith [hTsmall]
  have hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1 := by
    intro x hx
    have hx' : ‖x‖ ≤ R := by
      change dist x 0 ≤ R at hx
      simpa using hx
    exact hx'.trans hRsmall.le
  have hfNonneg (n : ℕ) : ∀ x, 0 ≤ f n x := by
    intro x
    change 0 ≤ openBallApprox 0 R n ((c : ℂ)⁻¹ • (x - a))
    exact (openBallApproxFun_bounds 0 R n ((c : ℂ)⁻¹ • (x - a))).1
  let scaleFactor : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * σ)
  have hscaleFactor : Measurable scaleFactor := by
    dsimp [scaleFactor]
    fun_prop
  let targetCutoff : ℕ → Ω → Fin 1 → ℝ := fun n ω _ => ∫ x, f n x ∂M ω
  let sourceCutoff : ℕ → Ω × ℝ → Fin 1 → ℝ := fun n p _ =>
    scaleFactor p.2 * ∫ x, g n x ∂M p.1
  let targetLimit : Ω → Fin 1 → ℝ := fun ω _ =>
    (M ω (Metric.ball a (c * R))).toReal
  let sourceLimit : Ω × ℝ → Fin 1 → ℝ := fun p _ =>
    scaleFactor p.2 * (M p.1 (Metric.ball 0 R)).toReal
  have htargetIntMeas (n : ℕ) : AEMeasurable (fun ω => ∫ x, f n x ∂M ω) P := by
    exact gmc_test_integral_aemeasurable_of_support P X hX γ M hM
      (Metric.closedBall a (c * R)) Metric.isClosed_closedBall.measurableSet
      htargetUnit (f n) (hfzero n)
  have hsourceIntMeas (n : ℕ) : AEMeasurable (fun ω => ∫ x, g n x ∂M ω) P := by
    exact gmc_test_integral_aemeasurable_of_support P X hX γ M hM
      (Metric.closedBall 0 R) Metric.isClosed_closedBall.measurableSet
      hsourceUnit (g n) (hgzero n)
  have htargetCutoffMeas (n : ℕ) : AEMeasurable (targetCutoff n) P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact htargetIntMeas n
  have hsourceCutoffMeas (n : ℕ) : AEMeasurable (sourceCutoff n) (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P :=
      measurePreserving_fst.map_eq
    have hbase : AEMeasurable (fun p : Ω × ℝ => ∫ x, g n x ∂M p.1) (P.prod G) := by
      have hbase' : AEMeasurable (fun ω => ∫ x, g n x ∂M ω)
          (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
        rw [hfst]
        exact hsourceIntMeas n
      change AEMeasurable
        ((fun ω => ∫ x, g n x ∂M ω) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    change AEMeasurable
      (fun p : Ω × ℝ => scaleFactor p.2 * ∫ x, g n x ∂M p.1) (P.prod G)
    exact hfactor.mul hbase
  have htargetLimitMeas : AEMeasurable targetLimit P := by
    apply aemeasurable_pi_iff.2
    intro j
    have hmass := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2
      M hM (Metric.ball a (c * R)) Metric.isOpen_ball.measurableSet
    exact (ENNReal.measurable_toReal.comp_aemeasurable hmass)
  have hsourceLimitMeas : AEMeasurable sourceLimit (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hmass := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2
      M hM (Metric.ball 0 R) Metric.isOpen_ball.measurableSet
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P :=
      measurePreserving_fst.map_eq
    have hbase' : AEMeasurable (fun ω => (M ω (Metric.ball 0 R)).toReal)
        (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
      rw [hfst]
      exact ENNReal.measurable_toReal.comp_aemeasurable hmass
    have hbase : AEMeasurable
        (fun p : Ω × ℝ => (M p.1 (Metric.ball 0 R)).toReal) (P.prod G) := by
      change AEMeasurable
        ((fun ω => (M ω (Metric.ball 0 R)).toReal) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    change AEMeasurable
      (fun p : Ω × ℝ => scaleFactor p.2 * (M p.1 (Metric.ball 0 R)).toReal)
      (P.prod G)
    exact hfactor.mul hbase
  have htargetCoordConv (j : Fin 1) :
      TendstoInMeasure P (fun n ω => targetCutoff n ω j) atTop
        (fun ω => targetLimit ω j) := by
    have hpoint (ω : Ω) : Tendsto (fun n : ℕ => ∫ x, f n x ∂M ω) atTop
        (𝓝 ((M ω (Metric.ball a (c * R))).toReal)) := by
      let : IsFiniteMeasure (M ω) := hM.1 ω
      simpa [Measure.real_def] using openBallAffineApprox_integral_tendsto hc (M ω)
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (htargetIntMeas n).aestronglyMeasurable)
      (ae_of_all P hpoint)
  have hsourceConv :
      TendstoInMeasure P (fun n ω => ∫ x, g n x ∂M ω) atTop
        (fun ω => (M ω (Metric.ball 0 R)).toReal) := by
    have hpoint (ω : Ω) : Tendsto (fun n : ℕ => ∫ x, g n x ∂M ω) atTop
        (𝓝 ((M ω (Metric.ball 0 R)).toReal)) := by
      let : IsFiniteMeasure (M ω) := hM.1 ω
      simpa [Measure.real_def, g] using openBallApprox_integral_tendsto 0 R (M ω)
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (hsourceIntMeas n).aestronglyMeasurable)
      (ae_of_all P hpoint)
  have htargetConv : TendstoInMeasure P targetCutoff atTop targetLimit :=
    tendstoInMeasure_pi_finite P targetCutoff targetLimit htargetCoordConv
  have hsourceProductCoordConv (j : Fin 1) :
      TendstoInMeasure (P.prod G) (fun n p => sourceCutoff n p j) atTop
      (fun p => sourceLimit p j) := by
    exact tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => ∫ x, g n x ∂M ω)
      (fun ω => (M ω (Metric.ball 0 R)).toReal) scaleFactor hscaleFactor hsourceConv
  have hsourceProductConv : TendstoInMeasure (P.prod G) sourceCutoff atTop sourceLimit :=
    tendstoInMeasure_pi_finite (P.prod G) sourceCutoff sourceLimit hsourceProductCoordConv
  have hcutoffLaw (n : ℕ) : Measure.map (targetCutoff n) P =
      Measure.map (sourceCutoff n) (P.prod G) := by
    let fvec : Fin 1 → BoundedContinuousFunction ℂ ℝ := fun _ => f n
    have h := gmc_affine_test_vector_law P X hX γ M hM
      (a := a) (c := c) (R := R) hc hc1 hR hRsmall hTsmall
      fvec (fun _ x => hfNonneg n x) (fun _ => hfSupport n)
    have hvalues : (fun p : Ω × ℝ => fun j : Fin 1 =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * σ) *
          ∫ x, fvec j (a + c • x) ∂M p.1) = sourceCutoff n := by
      funext p j
      have htest (x : ℂ) : f n (a + c • x) = g n x := by
        exact openBallAffineApprox_comp_affine a c R hc.ne' n x
      change c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * σ) *
        ∫ x, f n (a + c • x) ∂M p.1 =
          scaleFactor p.2 * ∫ x, g n x ∂M p.1
      have hInt : (∫ x, f n (a + c • x) ∂M p.1) =
          ∫ x, g n x ∂M p.1 := by
        apply integral_congr_ae
        exact ae_of_all _ htest
      rw [hInt]
    rw [hvalues] at h
    simpa [targetCutoff, fvec, sourceCutoff, G, σ] using h
  exact gmc_limit_test_vector_law targetCutoff sourceCutoff targetLimit sourceLimit
    (fun n => htargetCutoffMeas n) (fun n => hsourceCutoffMeas n)
    htargetLimitMeas hsourceLimitMeas hcutoffLaw
    (fun j => htargetCoordConv j) (fun j => hsourceProductCoordConv j)

end DOZZ.Proofs
