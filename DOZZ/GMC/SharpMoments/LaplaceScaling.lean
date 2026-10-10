/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.LaplaceTail
public import DOZZ.GMC.Annulus.CutoffScale

/-! # Exact scaling of cutoff Laplace transforms

On the exact logarithmic chart, the cutoff mass of a subdisk `B(a, cR)` has the law of
`c² e^{γ w - γ² log(1/c)/2}` times the mass of `B(0, R)` at the coarser cutoff, with an independent
Gaussian `w` of variance `log (1/c)`. For Laplace transforms in the logarithmic level this is a
Gaussian average of shifted reference Laplace transforms. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The Laplace transform of a subdisk mass is a Gaussian average of shifted reference Laplace
transforms at the source cutoff. -/
theorem cutoffLaplace_affine_ball_scaling
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {a : ℂ} {c R r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
    (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1) (y : ℝ) :
    cutoffLaplace P Xc γ (r - Real.log c) (Metric.ball a (c * R)) y =
      ∫ w, cutoffLaplace P Xc γ r (Metric.ball 0 R)
        (y + 2 * Real.log c + γ ^ 2 / 2 * Real.log c + γ * w)
        ∂gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩ := by
  classical
  let G : Measure ℝ := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let _ : IsProbabilityMeasure P := hX.1
  have hG : IsProbabilityMeasure G := by
    simpa [G] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)
  let _ : IsProbabilityMeasure G := hG
  let _ : IsProbabilityMeasure (P.prod G) := inferInstance
  let scaleFactor : ℝ → ℝ := fun w =>
    c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have hscale : Measurable scaleFactor := by
    dsimp [scaleFactor]
    fun_prop
  let t : Ω → Fin 1 → ℝ := fun ω _ =>
    (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal
  let s : Ω × ℝ → Fin 1 → ℝ := fun q _ =>
    scaleFactor q.2 * (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal
  have hLaw := regularizedGMC_affine_openBall_mass_law_CutoffScale P X hX γ Xc hXc
    (a := a) (c := c) (R := R) hc hc1 hR hRsmall hTsmall hsourceCut htargetCut
  change Measure.map t P = Measure.map s (P.prod G) at hLaw
  have hball : MeasurableSet (Metric.ball a (c * R)) := Metric.isOpen_ball.measurableSet
  have hball0 : MeasurableSet (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball.measurableSet
  have htm : Measurable t := by
    rw [measurable_pi_iff]
    intro _
    exact measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ _ _ hball
  have hsm : Measurable s := by
    rw [measurable_pi_iff]
    intro _
    exact (hscale.comp measurable_snd).mul
      ((measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r _ hball0).comp measurable_fst)
  let ψ : (Fin 1 → ℝ) → ℝ := fun v => Real.exp (-(Real.exp y) * v 0)
  have hψ : Measurable ψ := by
    dsimp [ψ]
    fun_prop
  -- Integrals of `ψ` against the two equal laws agree.
  have hleft : cutoffLaplace P Xc γ (r - Real.log c) (Metric.ball a (c * R)) y =
      ∫ v, ψ v ∂Measure.map t P := by
    rw [integral_map htm.aemeasurable hψ.aestronglyMeasurable]
    rfl
  have hmid : (∫ v, ψ v ∂Measure.map t P) = ∫ v, ψ v ∂Measure.map s (P.prod G) := by
    rw [hLaw]
  have hright : (∫ v, ψ v ∂Measure.map s (P.prod G)) =
      ∫ q, Real.exp (-(Real.exp y) * (scaleFactor q.2 *
        (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)) ∂P.prod G := by
    rw [integral_map hsm.aemeasurable hψ.aestronglyMeasurable]
  have hint : Integrable (fun q : Ω × ℝ => Real.exp (-(Real.exp y) * (scaleFactor q.2 *
      (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal))) (P.prod G) := by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun q => ?_)
    · exact (Real.measurable_exp.comp (((hscale.comp measurable_snd).mul
        ((measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r _ hball0).comp
          measurable_fst)).const_mul _)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply cutoffLaplace_integrand_le_one _ _ (Real.exp_pos y).le
      exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hswap := integral_prod_symm (μ := P) (ν := G) _ hint
  rw [hleft, hmid, hright, hswap]
  apply integral_congr_ae
  filter_upwards [] with w
  unfold cutoffLaplace
  apply integral_congr_ae
  filter_upwards [] with ω
  congr 1
  have hexp : Real.exp y * scaleFactor w =
      Real.exp (y + 2 * Real.log c + γ ^ 2 / 2 * Real.log c + γ * w) := by
    dsimp [scaleFactor]
    rw [show c ^ 2 = Real.exp (2 * Real.log c) by
      rw [show (2 : ℝ) * Real.log c = Real.log c + Real.log c by ring, Real.exp_add,
        Real.exp_log hc]
      ring]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

end DOZZ.Proofs
