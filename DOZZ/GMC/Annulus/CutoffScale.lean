/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.AdmissibleGMCRestriction
public import DOZZ.GMC.Moments.RegularizedScale
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ScaleLimit
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Moments.OpenBallApproximation
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Annulus.PositiveRoot
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Exact affine scaling of actual finite-cutoff open-ball masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- For actual circle cutoff measures, affine scaling preserves the full ball-mass law,
including the independent scalar Gaussian and the corresponding change of cutoff. -/
theorem regularizedGMC_affine_openBall_mass_law_CutoffScale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {a : ℂ} {c R r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
    (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1) :
    Measure.map (fun ω : Ω => fun _ : Fin 1 =>
      (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal) P =
    Measure.map (fun p : Ω × ℝ => fun _ : Fin 1 =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (regularizedGMC P Xc γ r p.1 (Metric.ball 0 R)).toReal)
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
  let targetCutoff : ℕ → Ω → Fin 1 → ℝ := fun n ω _ => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω
  let sourceCutoff : ℕ → Ω × ℝ → Fin 1 → ℝ := fun n p _ =>
    scaleFactor p.2 * ∫ x, g n x ∂regularizedGMC P Xc γ r p.1
  let targetLimit : Ω → Fin 1 → ℝ := fun ω _ =>
    (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal
  let sourceLimit : Ω × ℝ → Fin 1 → ℝ := fun p _ =>
    scaleFactor p.2 * (regularizedGMC P Xc γ r p.1 (Metric.ball 0 R)).toReal
  have htargetIntMeas (n : ℕ) : AEMeasurable (fun ω => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω) P := by
    exact regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ (r - Real.log c)
      (Metric.closedBall a (c * R)) Metric.isClosed_closedBall.measurableSet
      htargetUnit (f n) (f n).continuous.measurable (hfzero n)
  have hsourceIntMeas (n : ℕ) : AEMeasurable (fun ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) P := by
    exact regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ r
      (Metric.closedBall 0 R) Metric.isClosed_closedBall.measurableSet
      hsourceUnit (g n) (g n).continuous.measurable (hgzero n)
  have htargetCutoffMeas (n : ℕ) : AEMeasurable (targetCutoff n) P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact htargetIntMeas n
  have hsourceCutoffMeas (n : ℕ) : AEMeasurable (sourceCutoff n) (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P :=
      measurePreserving_fst.map_eq
    have hbase : AEMeasurable (fun p : Ω × ℝ => ∫ x, g n x ∂regularizedGMC P Xc γ r p.1) (P.prod G) := by
      have hbase' : AEMeasurable (fun ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω)
          (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
        rw [hfst]
        exact hsourceIntMeas n
      change AEMeasurable
        ((fun ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    change AEMeasurable
      (fun p : Ω × ℝ => scaleFactor p.2 * ∫ x, g n x ∂regularizedGMC P Xc γ r p.1) (P.prod G)
    exact hfactor.mul hbase
  have htargetLimitMeas : AEMeasurable targetLimit P := by
    apply aemeasurable_pi_iff.2
    intro j
    have hmass : AEMeasurable
        (fun ω => regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))) P :=
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc γ (r - Real.log c))).aemeasurable
    exact (ENNReal.measurable_toReal.comp_aemeasurable hmass)
  have hsourceLimitMeas : AEMeasurable sourceLimit (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hmass : AEMeasurable
        (fun ω => regularizedGMC P Xc γ r ω (Metric.ball 0 R)) P :=
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P :=
      measurePreserving_fst.map_eq
    have hbase' : AEMeasurable (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal)
        (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
      rw [hfst]
      exact ENNReal.measurable_toReal.comp_aemeasurable hmass
    have hbase : AEMeasurable
        (fun p : Ω × ℝ => (regularizedGMC P Xc γ r p.1 (Metric.ball 0 R)).toReal) (P.prod G) := by
      change AEMeasurable
        ((fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    change AEMeasurable
      (fun p : Ω × ℝ => scaleFactor p.2 * (regularizedGMC P Xc γ r p.1 (Metric.ball 0 R)).toReal)
      (P.prod G)
    exact hfactor.mul hbase
  have htargetCoordConv (j : Fin 1) :
      TendstoInMeasure P (fun n ω => targetCutoff n ω j) atTop
        (fun ω => targetLimit ω j) := by
    have hpoint (ω : Ω) (hfin : IsFiniteMeasure (regularizedGMC P Xc γ (r - Real.log c) ω)) : Tendsto (fun n : ℕ => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω) atTop
        (𝓝 ((regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal)) := by
      let := hfin
      simpa [Measure.real_def] using openBallAffineApprox_integral_tendsto hc (regularizedGMC P Xc γ (r - Real.log c) ω)
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (htargetIntMeas n).aestronglyMeasurable)
      ((regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)).mono hpoint)
  have hsourceConv :
      TendstoInMeasure P (fun n ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal) := by
    have hpoint (ω : Ω) (hfin : IsFiniteMeasure (regularizedGMC P Xc γ r ω)) : Tendsto (fun n : ℕ => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) atTop
        (𝓝 ((regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal)) := by
      let := hfin
      simpa [Measure.real_def, g] using openBallApprox_integral_tendsto 0 R (regularizedGMC P Xc γ r ω)
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (hsourceIntMeas n).aestronglyMeasurable)
      ((regularizedGMC_finite_ae P X hX Xc hXc γ r).mono hpoint)
  have htargetConv : TendstoInMeasure P targetCutoff atTop targetLimit :=
    tendstoInMeasure_pi_finite P targetCutoff targetLimit htargetCoordConv
  have hsourceProductCoordConv (j : Fin 1) :
      TendstoInMeasure (P.prod G) (fun n p => sourceCutoff n p j) atTop
      (fun p => sourceLimit p j) := by
    exact tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω)
      (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal) scaleFactor hscaleFactor hsourceConv
  have hsourceProductConv : TendstoInMeasure (P.prod G) sourceCutoff atTop sourceLimit :=
    tendstoInMeasure_pi_finite (P.prod G) sourceCutoff sourceLimit hsourceProductCoordConv
  have hcutoffLaw (n : ℕ) : Measure.map (targetCutoff n) P =
      Measure.map (sourceCutoff n) (P.prod G) := by
    let fvec : Fin 1 → BoundedContinuousFunction ℂ ℝ := fun _ => f n
    have h := regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ
      (a := a) (c := c) (R := R) (r := r) hc hc1 hR hsourceCut htargetCut hsourceUnit htargetUnit
      fvec (fun _ x => hfNonneg n x) (fun _ => hfSupport n)
    have hvalues : (fun p : Ω × ℝ => fun j : Fin 1 =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * σ) *
          ∫ x, fvec j (a + c • x) ∂regularizedGMC P Xc γ r p.1) = sourceCutoff n := by
      funext p j
      have htest (x : ℂ) : f n (a + c • x) = g n x := by
        exact openBallAffineApprox_comp_affine a c R hc.ne' n x
      change c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * σ) *
        ∫ x, f n (a + c • x) ∂regularizedGMC P Xc γ r p.1 =
          scaleFactor p.2 * ∫ x, g n x ∂regularizedGMC P Xc γ r p.1
      have hInt : (∫ x, f n (a + c • x) ∂regularizedGMC P Xc γ r p.1) =
          ∫ x, g n x ∂regularizedGMC P Xc γ r p.1 := by
        apply integral_congr_ae
        exact ae_of_all _ htest
      rw [hInt]
    rw [hvalues] at h
    simpa [targetCutoff, fvec, sourceCutoff, G, σ] using h
  exact gmc_limit_test_vector_law targetCutoff sourceCutoff targetLimit sourceLimit
    (fun n => htargetCutoffMeas n) (fun n => hsourceCutoffMeas n)
    htargetLimitMeas hsourceLimitMeas hcutoffLaw
    (fun j => htargetCoordConv j) (fun j => hsourceProductCoordConv j)

/-- Exact moment scaling at the actual finite cutoff, for every real order. -/
theorem regularizedGMC_affine_openBall_moment_scale_CutoffScale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {a : ℂ} {c R r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
    (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1) (p : ℝ) :
    gmcMassMoment P (regularizedGMC P Xc γ (r - Real.log c)) (Metric.ball a (c * R)) p =
    ENNReal.ofReal (c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) p := by
  classical
  let G : Measure ℝ := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let : IsProbabilityMeasure P := hX.1
  have hG : IsProbabilityMeasure G := by
    simpa [G] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure (P.prod G) := inferInstance
  let scaleFactor : ℝ → ℝ := fun w =>
    c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  let t : Ω → Fin 1 → ℝ := fun ω _ => (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal
  let s : Ω × ℝ → Fin 1 → ℝ := fun q _ =>
    scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal
  have hLaw := regularizedGMC_affine_openBall_mass_law_CutoffScale P X hX γ Xc hXc
    (a := a) (c := c) (R := R) hc hc1 hR hRsmall hTsmall hsourceCut htargetCut
  change Measure.map t P = Measure.map s (P.prod G) at hLaw
  have htCoord : AEMeasurable
      (fun ω => (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal) P := by
    exact ENNReal.measurable_toReal.comp_aemeasurable
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc γ (r - Real.log c))).aemeasurable
  have hsCoord : AEMeasurable
      (fun q : Ω × ℝ => scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)
      (P.prod G) := by
    have hbase : AEMeasurable (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal) P := by
      exact ENNReal.measurable_toReal.comp_aemeasurable
        ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
          (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable
    have hfst : Measure.map (fun q : Ω × ℝ => q.1) (P.prod G) = P :=
      measurePreserving_fst.map_eq
    have hbase' : AEMeasurable
        (fun q : Ω × ℝ => (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal) (P.prod G) := by
      have h' : AEMeasurable (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal)
          (Measure.map (fun q : Ω × ℝ => q.1) (P.prod G)) := by
        rw [hfst]
        exact hbase
      change AEMeasurable
        ((fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal) ∘ (fun q : Ω × ℝ => q.1))
        (P.prod G)
      exact h'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun q : Ω × ℝ => scaleFactor q.2) (P.prod G) := by
      have hm : Measurable scaleFactor := by
        dsimp [scaleFactor]
        fun_prop
      exact hm.comp_aemeasurable measurable_snd.aemeasurable
    change AEMeasurable
      (fun q : Ω × ℝ => scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)
      (P.prod G)
    exact hfactor.mul hbase'
  let ψ : (Fin 1 → ℝ) → ℝ≥0∞ := fun v => ENNReal.rpow (ENNReal.ofReal (v 0)) p
  have hψ : Measurable ψ := by
    dsimp [ψ]
    fun_prop
  have hmapIntegral :
      (∫⁻ v, ψ v ∂Measure.map t P) =
        ∫⁻ v, ψ v ∂Measure.map s (P.prod G) := by rw [hLaw]
  have hleft : gmcMassMoment P (regularizedGMC P Xc γ (r - Real.log c)) (Metric.ball a (c * R)) p =
      ∫⁻ v, ψ v ∂Measure.map t P := by
    rw [gmcMassMoment, lintegral_map' hψ.aemeasurable (aemeasurable_pi_iff.2
      (fun j => by simpa [t] using htCoord))]
    apply lintegral_congr_ae
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)] with ω hfin
    let _ := hfin
    simp [ψ, t, ENNReal.ofReal_toReal (measure_ne_top (regularizedGMC P Xc γ (r - Real.log c) ω) _)]
  have hright :
      (∫⁻ v, ψ v ∂Measure.map s (P.prod G)) =
        ∫⁻ q, ENNReal.rpow
          (ENNReal.ofReal (scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)) p
          ∂P.prod G := by
    rw [lintegral_map' hψ.aemeasurable (aemeasurable_pi_iff.2
      (fun j => by simpa [s] using hsCoord))]
  have hfactorMom : AEMeasurable
      (fun w => ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p) G := by
    have hm : Measurable scaleFactor := by
      dsimp [scaleFactor]
      fun_prop
    have hfac : AEMeasurable (fun w => ENNReal.ofReal (scaleFactor w)) G :=
      ENNReal.measurable_ofReal.comp_aemeasurable hm.aemeasurable
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfac
  have hbaseMom : AEMeasurable
      (fun ω => ENNReal.rpow (regularizedGMC P Xc γ r ω (Metric.ball 0 R)) p) P := by
    have hmass : AEMeasurable (fun ω => regularizedGMC P Xc γ r ω (Metric.ball 0 R)) P :=
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmass
  have hprod :
      (∫⁻ q, ENNReal.rpow
          (ENNReal.ofReal (scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)) p
          ∂P.prod G) =
        gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) p *
          ∫⁻ w, ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p ∂G := by
    calc
      _ = ∫⁻ q : Ω × ℝ, ENNReal.rpow (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)) p *
          ENNReal.rpow (ENNReal.ofReal (scaleFactor q.2)) p ∂P.prod G := by
        apply lintegral_congr_ae
        have hf : ∀ᵐ q : Ω × ℝ ∂P.prod G, IsFiniteMeasure (regularizedGMC P Xc γ r q.1) :=
          measurePreserving_fst.quasiMeasurePreserving.ae
            (regularizedGMC_finite_ae P X hX Xc hXc γ r)
        filter_upwards [hf] with q hfin
        let _ := hfin
        have hmassTop : regularizedGMC P Xc γ r q.1 (Metric.ball 0 R) ≠ ∞ :=
          measure_ne_top _ _
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmassTop]
        simpa [mul_comm] using
          (ENNReal.mul_rpow_of_ne_top (x := ENNReal.ofReal (scaleFactor q.2))
            (y := regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)) ENNReal.ofReal_ne_top hmassTop p)
      _ = _ := by
        rw [lintegral_prod_mul hbaseMom hfactorMom, gmcMassMoment]
  calc
    gmcMassMoment P (regularizedGMC P Xc γ (r - Real.log c)) (Metric.ball a (c * R)) p =
        ∫⁻ v, ψ v ∂Measure.map t P := hleft
    _ = ∫⁻ v, ψ v ∂Measure.map s (P.prod G) := hmapIntegral
    _ = ∫⁻ q, ENNReal.rpow
        (ENNReal.ofReal (scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)) p
        ∂P.prod G := hright
    _ = gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) p *
        ∫⁻ w, ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p ∂G := hprod
    _ = _ := by
      rw [gaussianScaleFactor_rpow_integral γ c p hc hc1]
      ac_rfl


/-- Radius-form finite-cutoff scaling. The reference cutoff is shifted by `log(s/R)`;
its circle radius is consequently the original circle radius multiplied by `R/s`.
The two explicit radius guards ensure all averaging circles stay in the exact chart. -/
theorem regularizedGMC_local_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : ℂ) {s R t : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hR : 0 < R)
    (hR1 : R < 1) (hz : ‖z‖ + s < 1)
    (hbase : R + Real.exp (-t) * (R / s) ≤ 1)
    (htarget : ‖z‖ + s + Real.exp (-t) ≤ 1) (p : ℝ) :
    gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball z s) p =
      ENNReal.ofReal ((s / R) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        gmcMassMoment P (regularizedGMC P Xc γ (t + Real.log (s / R)))
          (Metric.ball 0 R) p := by
  have hc : 0 < s / R := div_pos hs hR
  have hc1 : s / R ≤ 1 := (div_le_one hR).mpr hsR
  have he : Real.exp (-(t + Real.log (s / R))) = Real.exp (-t) * (R / s) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (s / R)), Real.exp_log hc, inv_div]
  have hsEq : s / R * R = s := div_mul_cancel₀ s hR.ne'
  have hsource : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-(t + Real.log (s / R))) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
    rw [he]
    exact (add_le_add hx le_rfl).trans hbase
  have htar : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) R},
      ‖z + (s / R) • x.1‖ + Real.exp (-((t + Real.log (s / R)) - Real.log (s / R))) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
    have hn : ‖z + (s / R) • x.1‖ ≤ ‖z‖ + s := by
      calc
        _ ≤ ‖z‖ + ‖(s / R) • x.1‖ := norm_add_le _ _
        _ = ‖z‖ + (s / R) * ‖x.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖z‖ + (s / R) * R := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hc.le)
        _ = _ := by rw [hsEq]
    rw [add_sub_cancel_right]
    exact (add_le_add hn le_rfl).trans htarget
  have h := regularizedGMC_affine_openBall_moment_scale_CutoffScale P X hX γ Xc hXc
    (a := z) (c := s / R) (R := R) (r := t + Real.log (s / R)) hc hc1 hR hR1
    (by simpa only [hsEq] using hz) hsource htar p
  simpa only [add_sub_cancel_right, hsEq] using h

/-- Spatial Hölder in the extended positive reals, including zero and infinite integrals. -/
theorem ennreal_lintegral_rpow_le_mass_rpow_mul_lintegral_rpow
    {S : Type*} [MeasurableSpace S] (ν : Measure S) (f : S → ℝ≥0∞)
    (hf : AEMeasurable f ν) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ x, f x ∂ν) ^ p ≤ (ν univ) ^ (p - 1) * ∫⁻ x, (f x) ^ p ∂ν := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp only [ENNReal.rpow_one, sub_self, ENNReal.rpow_zero, one_mul]
    exact le_rfl
  · let q := p / (p - 1)
    have hc : p.HolderConjugate q := by
      apply Real.holderConjugate_iff.mpr
      refine ⟨hp, ?_⟩
      dsimp [q]
      field_simp [ne_of_gt (by linarith : 0 < p), ne_of_gt (by linarith : 0 < p - 1)]
      ring
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hc hf
      (aemeasurable_const : AEMeasurable (fun _ : S => (1 : ℝ≥0∞)) ν)
    simp only [Pi.mul_apply, ENNReal.one_rpow, mul_one, lintegral_one] at h
    have he : (1 / q) * p = p - 1 := by
      dsimp [q]
      field_simp [ne_of_gt (by linarith : 0 < p), ne_of_gt (by linarith : 0 < p - 1)]
    have hp0 : 0 ≤ p := by linarith
    have hpne : p ≠ 0 := by linarith
    have hpow := ENNReal.rpow_le_rpow h hp0
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpne, ENNReal.rpow_one, he, mul_comm] at hpow
    exact hpow

/-- The actual mass at a coarse cutoff has a uniform higher-moment estimate on every bounded
Borel chart. The reference measure and covariance remainder both appear explicitly. -/
theorem regularizedGMC_coarse_chart_moment_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ R T p : ℝ) (hR : 0 ≤ R) (hp : 1 ≤ p)
    (O : Set ℂ) (hO : MeasurableSet O) (hchart : ∀ x ∈ O, ‖x‖ ≤ R)
    (r : ℝ) (hr : 0 ≤ r) (hrT : r ≤ T) :
    gmcMassMoment P (regularizedGMC P Xc γ r) O p ≤
      (gmcReferenceMeasure O) ^ p * ENNReal.ofReal
        (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R))) := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hW := measurable_gmcCircleWickDensity P X Xc hXc γ r
  have hWp : Measurable (fun q : Ω × ℂ => (gmcCircleWickDensity P Xc γ r q.1 q.2) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hW
  have hf (ω : Ω) : AEMeasurable (gmcCircleWickDensity P Xc γ r ω)
      (gmcReferenceMeasure.restrict O) :=
    (hW.comp (measurable_const.prodMk measurable_id)).aemeasurable
  change (∫⁻ ω, (regularizedGMC P Xc γ r ω O) ^ p ∂P) ≤ _
  calc
    _ ≤ ∫⁻ ω, (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂gmcReferenceMeasure ∂P := by
      apply lintegral_mono
      intro ω
      change (regularizedGMC P Xc γ r ω O) ^ p ≤ (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂gmcReferenceMeasure
      rw [regularizedGMC_mass_eq_wick_lintegral P X Xc hXc γ r O hO ω]
      have h := ennreal_lintegral_rpow_le_mass_rpow_mul_lintegral_rpow
        (gmcReferenceMeasure.restrict O) (gmcCircleWickDensity P Xc γ r ω) (hf ω) p hp
      simpa only [Measure.restrict_apply_univ] using h
    _ = (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, ∫⁻ ω, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂P ∂gmcReferenceMeasure := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        (measure_ne_top _ _)), lintegral_lintegral_swap hWp.aemeasurable]
    _ ≤ (gmcReferenceMeasure O) ^ (p - 1) * (gmcReferenceMeasure O *
        ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R)))) := by
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∫⁻ _x in O, ENNReal.ofReal (Real.exp
            (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R))) ∂gmcReferenceMeasure := by
          apply setLIntegral_mono' hO
          intro x hx
          exact gmcCircleWickDensity_coarse_convex_moment_bound P X hX Xc hXc γ R T p hR
            (Or.inr hp) r hr hrT x (hchart x hx)
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    _ = _ := by
      have he : (gmcReferenceMeasure O) ^ (p - 1) * gmcReferenceMeasure O =
          (gmcReferenceMeasure O) ^ p := by
        calc
          _ = (gmcReferenceMeasure O) ^ (p - 1) * (gmcReferenceMeasure O) ^ (1 : ℝ) :=
            by rw [ENNReal.rpow_one]
          _ = (gmcReferenceMeasure O) ^ ((p - 1) + 1) :=
            (ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)).symm
          _ = _ := by congr 1; ring
      rw [← mul_assoc, he]


end DOZZ.Proofs
