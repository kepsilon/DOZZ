/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.Moments.RegularizedScale
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ScaleLimit

/-! Exact affine scaling of arbitrary `IsGMCOf` limits on a compact logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The exact-scale identity for arbitrary `IsGMCOf` versions, expressed jointly on finite
families of nonnegative compactly supported tests. The independent Gaussian comes from the
constant shift in the logarithmic covariance, and the affine Jacobian is `c^2`. -/
theorem gmc_affine_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
    (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hf_nonneg : ∀ j x, 0 ≤ f j x)
    (hf_support : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ Metric.closedBall a (c * R)) :
    Measure.map (fun ω j => ∫ x, f j x ∂M ω) P =
      Measure.map (fun p : Ω × ℝ => fun j =>
        c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
          ∫ x, f j (a + c • x) ∂M p.1)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)) := by
  classical
  obtain ⟨Xc, hXc, hMlim⟩ := hM.2
  let σ : ℝ := -Real.log c
  let G : Measure ℝ := gaussianReal 0 ⟨σ,
    neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩
  have hG : IsProbabilityMeasure G := by
    simpa [G, σ] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)
  let : IsProbabilityMeasure P := hX.1
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure (P.prod G) := inferInstance
  let gap : ℝ := min (1 - R) (1 - (‖a‖ + c * R))
  have hgap : 0 < gap := by
    dsimp [gap]
    exact lt_min (by linarith) (by linarith)
  have hsmallEvent : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < gap := by
    have hlim : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    exact hlim.eventually (isOpen_Iio.mem_nhds hgap)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEvent
  have hNgap : Real.exp (-(N : ℝ)) ≤ gap := le_of_lt (hN N le_rfl)
  have hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1 := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      have hxmem : x ∈ Metric.closedBall (0 : ℂ) R := hx
      change dist x 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    exact hxR.trans hRsmall.le
  have htargetUnit : ∀ x ∈ Metric.closedBall a (c * R), ‖x‖ ≤ 1 := by
    intro x hx
    have hxR : ‖x - a‖ ≤ c * R := by
      change dist x a ≤ c * R at hx
      simpa only [dist_eq_norm] using hx
    calc
      ‖x‖ = ‖(x - a) + a‖ := by congr 1; abel
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ c * R + ‖a‖ := by nlinarith [hxR]
      _ ≤ 1 := by linarith [hTsmall]
  have hsourceCut (n : ℕ) (x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) :
      ‖x.1‖ + Real.exp (-((N + n : ℕ) : ℝ)) ≤ 1 := by
    have hxR : ‖x.1‖ ≤ R := by
      have hxmem : x.1 ∈ Metric.closedBall (0 : ℂ) R := x.2
      change dist x.1 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    have hn : (N : ℝ) ≤ ((N + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N n
    have hexp : Real.exp (-((N + n : ℕ) : ℝ)) ≤ Real.exp (-(N : ℝ)) :=
      Real.exp_le_exp.mpr (neg_le_neg hn)
    have hgapS : gap ≤ 1 - R := by dsimp [gap]; exact min_le_left _ _
    linarith [hexp.trans hNgap]
  have htargetCut (n : ℕ) (x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) :
      ‖a + c • x.1‖ + Real.exp (-(((N + n : ℕ) : ℝ) - Real.log c)) ≤ 1 := by
    have hxR : ‖x.1‖ ≤ R := by
      have hxmem : x.1 ∈ Metric.closedBall (0 : ℂ) R := x.2
      change dist x.1 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    have hnorm : ‖a + c • x.1‖ ≤ ‖a‖ + c * R := by
      calc
        ‖a + c • x.1‖ ≤ ‖a‖ + ‖c • x.1‖ := norm_add_le _ _
        _ = ‖a‖ + c * ‖x.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖a‖ + c * R := by nlinarith [mul_le_mul_of_nonneg_left hxR (le_of_lt hc)]
    have hexpScale (s : ℝ) : Real.exp (-(s - Real.log c)) ≤ Real.exp (-s) := by
      calc
        Real.exp (-(s - Real.log c)) = Real.exp (-s) * c := by
          rw [show -(s - Real.log c) = (-s) + Real.log c by ring, Real.exp_add,
            Real.exp_log hc]
        _ = c * Real.exp (-s) := by ring
        _ ≤ Real.exp (-s) := by
          calc
            c * Real.exp (-s) ≤ 1 * Real.exp (-s) :=
              mul_le_mul_of_nonneg_right hc1 (Real.exp_nonneg _)
            _ = Real.exp (-s) := one_mul _
    have hn : (N : ℝ) ≤ ((N + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N n
    have hexp : Real.exp (-(((N + n : ℕ) : ℝ) - Real.log c)) ≤
        Real.exp (-(N : ℝ)) := (hexpScale _).trans <|
          Real.exp_le_exp.mpr (neg_le_neg hn)
    have hgapT : gap ≤ 1 - (‖a‖ + c * R) := by
      dsimp [gap]
      exact min_le_right _ _
    linarith [hexp.trans hNgap]
  let affine : ContinuousMap ℂ ℂ := ⟨fun x => a + c • x, by fun_prop⟩
  let g : Fin m → BoundedContinuousFunction ℂ ℝ := fun j => (f j).compContinuous affine
  have htargetZero (j : Fin m) : ∀ x, x ∉ Metric.closedBall a (c * R) → f j x = 0 :=
    boundedContinuousFunction_eq_zero_off_tsupport_subset (f j)
      (Metric.closedBall a (c * R)) (hf_support j)
  have himage : (fun x : ℂ => a + c • x) '' Metric.closedBall (0 : ℂ) R =
      Metric.closedBall a (c * R) := complex_affine_image_closedBall hc
  have hinj : Function.Injective (fun x : ℂ => a + c • x) := by
    intro x y hxy
    have hsmul : c • x = c • y := add_left_cancel hxy
    exact (smul_right_injective ℂ hc.ne') hsmul
  have hbaseZero (j : Fin m) : ∀ x, x ∉ Metric.closedBall (0 : ℂ) R → g j x = 0 := by
    intro x hx
    change f j (a + c • x) = 0
    apply htargetZero j
    intro hy
    have hy' : a + c • x ∈ (fun y : ℂ => a + c • y) '' Metric.closedBall (0 : ℂ) R := by
      rw [himage]
      exact hy
    obtain ⟨y, hyball, hyEq⟩ := hy'
    have hxy : x = y := hinj (by simpa using hyEq.symm)
    exact hx (hxy ▸ hyball)
  have hg_nonneg : ∀ j x, 0 ≤ g j x := by
    intro j x
    simpa [g, BoundedContinuousFunction.compContinuous_apply, affine] using hf_nonneg j _
  let scaleFactor : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * σ)
  have hscaleFactor : Measurable scaleFactor := by
    dsimp [scaleFactor]
    fun_prop
  let scaleSeq : ℕ → ℝ := fun n => ((N + n : ℕ) : ℝ)
  have hscaleSeq : Tendsto scaleSeq atTop atTop := by
    dsimp [scaleSeq]
    simpa only [Nat.cast_add] using
      (tendsto_atTop_add_const_left atTop (N : ℝ) tendsto_natCast_atTop_atTop)
  let targetSeq : ℕ → ℝ := fun n => scaleSeq n - Real.log c
  have htargetSeq : Tendsto targetSeq atTop atTop := by
    dsimp [targetSeq]
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-Real.log c) hscaleSeq)
  let targetCutoff : ℕ → Ω → Fin m → ℝ := fun n ω j =>
    ∫ x, f j x ∂regularizedGMC P Xc γ (targetSeq n) ω
  let baseCutoff : ℕ → Ω → Fin m → ℝ := fun n ω j =>
    ∫ x, g j x ∂regularizedGMC P Xc γ (scaleSeq n) ω
  let limitTarget : Ω → Fin m → ℝ := fun ω j => ∫ x, f j x ∂M ω
  let limitBase : Ω → Fin m → ℝ := fun ω j => ∫ x, g j x ∂M ω
  let cutoffProduct : ℕ → Ω × ℝ → Fin m → ℝ := fun n p j =>
    scaleFactor p.2 * baseCutoff n p.1 j
  let limitProduct : Ω × ℝ → Fin m → ℝ := fun p j =>
    scaleFactor p.2 * limitBase p.1 j
  have hconvTarget (j : Fin m) :
      TendstoInMeasure P (fun n ω => targetCutoff n ω j) atTop
        (fun ω => limitTarget ω j) := by
    change TendstoInMeasure P
      ((fun r ω => ∫ x, f j x ∂regularizedGMC P Xc γ r ω) ∘ targetSeq) atTop
      (fun ω => ∫ x, f j x ∂M ω)
    exact (hMlim (f j)).comp htargetSeq
  have hconvBase (j : Fin m) :
      TendstoInMeasure P (fun n ω => baseCutoff n ω j) atTop
        (fun ω => limitBase ω j) := by
    change TendstoInMeasure P
      ((fun r ω => ∫ x, g j x ∂regularizedGMC P Xc γ r ω) ∘ scaleSeq) atTop
      (fun ω => ∫ x, g j x ∂M ω)
    exact (hMlim (g j)).comp hscaleSeq
  have hcutTarget (n : ℕ) (j : Fin m) : AEMeasurable
      (fun ω => targetCutoff n ω j) P := by
    apply regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ (targetSeq n)
      (Metric.closedBall a (c * R)) Metric.isClosed_closedBall.measurableSet htargetUnit
      (f j) (f j).continuous.measurable (htargetZero j)
  have hcutBase (n : ℕ) (j : Fin m) : AEMeasurable
      (fun ω => baseCutoff n ω j) P := by
    apply regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ (scaleSeq n)
      (Metric.closedBall (0 : ℂ) R) Metric.isClosed_closedBall.measurableSet hsourceUnit
      (g j) (g j).continuous.measurable (hbaseZero j)
  have hcutTargetVec (n : ℕ) : AEMeasurable (targetCutoff n) P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact hcutTarget n j
  have hcutProduct (n : ℕ) : AEMeasurable (cutoffProduct n) (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P := by
      exact measurePreserving_fst.map_eq
    have hbase : AEMeasurable (fun p : Ω × ℝ => baseCutoff n p.1 j) (P.prod G) := by
      have hbase' : AEMeasurable (fun ω => baseCutoff n ω j)
          (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
        rw [hfst]
        exact hcutBase n j
      change AEMeasurable
        ((fun ω => baseCutoff n ω j) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    exact (hfactor.mul hbase)
  have hlimitTarget : AEMeasurable limitTarget P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact (hconvTarget j).aemeasurable (fun n => hcutTarget n j)
  have hlimitProduct : AEMeasurable limitProduct (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hbaseP : AEMeasurable (fun ω => limitBase ω j) P :=
      (hconvBase j).aemeasurable (fun n => hcutBase n j)
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P := by
      exact measurePreserving_fst.map_eq
    have hbase : AEMeasurable (fun p : Ω × ℝ => limitBase p.1 j) (P.prod G) := by
      have hbase' : AEMeasurable (fun ω => limitBase ω j)
          (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
        rw [hfst]
        exact hbaseP
      change AEMeasurable
        ((fun ω => limitBase ω j) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    exact hfactor.mul hbase
  have hcutLaw (n : ℕ) : Measure.map (targetCutoff n) P =
      Measure.map (cutoffProduct n) (P.prod G) := by
    have h := regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ
      (a := a) (c := c) (R := R) (r := scaleSeq n) hc hc1 hR
      (hsourceCut n) (htargetCut n) hsourceUnit htargetUnit f hf_nonneg hf_support
    simpa [targetCutoff, cutoffProduct, baseCutoff, scaleFactor, scaleSeq,
      targetSeq, σ, G, g, BoundedContinuousFunction.compContinuous_apply, affine] using h
  have hconvProduct (j : Fin m) :
      TendstoInMeasure (P.prod G) (fun n p => cutoffProduct n p j) atTop
        (fun p => limitProduct p j) :=
    tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => baseCutoff n ω j) (fun ω => limitBase ω j) scaleFactor
      hscaleFactor (hconvBase j)
  have hconvProductVec : TendstoInMeasure (P.prod G) cutoffProduct atTop limitProduct :=
    tendstoInMeasure_pi_finite (P.prod G) cutoffProduct limitProduct hconvProduct
  exact gmc_limit_test_vector_law targetCutoff cutoffProduct limitTarget limitProduct
    (fun n => hcutTargetVec n) hcutProduct hlimitTarget hlimitProduct hcutLaw
    hconvTarget hconvProduct

end DOZZ.Proofs
