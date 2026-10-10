/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.CircleAverageL2Geometry
public import DOZZ.GFFStructure.CircleVersion

/-!
# Joint circle-average versions

The canonical L² family has Gaussian increments with the same logarithmic-potential bounds as circle
averages. Spatial Kolmogorov modifications at each fixed logarithmic radius, followed by raw-sigma
gluing, produce the jointly measurable circle-average witness (`DOZZ.IsCircleAverage`) on the
original field space.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace DOZZ.Proofs

/-- Variance of an increment of the canonical L² circle family. -/
theorem circleL2_increment_variance_formula
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : (ℂ × ℝ) → Ω → ℝ)
    (hmem : ∀ p, MemLp (Y p) 2 P)
    (hcov : ∀ p q, covariance (Y p) (Y q) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
    (x y : ℂ) (r s : ℝ) :
    variance (fun ω => Y (x, r) ω - Y (y, s) ω) P = r + s +
      (∫ z, Real.log (max (Real.exp (-r)) ‖x-z‖) ∂circleMeasure y s) +
      (∫ z, Real.log (max (Real.exp (-s)) ‖y-z‖) ∂circleMeasure x r) := by
  let p : ℂ × ℝ := (x, r)
  let q : ℂ × ℝ := (y, s)
  let Lp := ∫ z, Real.log (normPlus z) ∂circleMeasure x r
  let Lq := ∫ z, Real.log (normPlus z) ∂circleMeasure y s
  let A := ∫ z, Real.log (max (Real.exp (-r)) ‖x-z‖) ∂circleMeasure y s
  let B := ∫ z, Real.log (max (Real.exp (-s)) ‖y-z‖) ∂circleMeasure x r
  have hdiagP : covariance (Y p) (Y p) P = r + 2 * Lp := by
    calc
      covariance (Y p) (Y p) P = circleSelfEnergy x r := by
        simpa only [circleSelfEnergy] using hcov p p
      _ = r + 2 * Lp := by simpa only [Lp] using circleSelfEnergy_eq x r
  have hdiagQ : covariance (Y q) (Y q) P = s + 2 * Lq := by
    calc
      covariance (Y q) (Y q) P = circleSelfEnergy y s := by
        simpa only [circleSelfEnergy] using hcov q q
      _ = s + 2 * Lq := by simpa only [Lq] using circleSelfEnergy_eq y s
  have hcrossPQ : covariance (Y p) (Y q) P = -A + Lq + Lp := by
    calc
      covariance (Y p) (Y q) P =
          ∫ z, ∫ w, gffKernel z w ∂circleMeasure x r ∂circleMeasure y s := hcov p q
      _ = -A + Lq + Lp := by
        simpa only [A, Lp, Lq] using
          (integral_integral_gffKernel_eq_logmax y x s r)
  have hcrossQP : covariance (Y q) (Y p) P = -B + Lp + Lq := by
    calc
      covariance (Y q) (Y p) P =
          ∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure x r := hcov q p
      _ = -B + Lp + Lq := by
        simpa only [B, Lp, Lq] using
          (integral_integral_gffKernel_eq_logmax x y r s)
  have hdiff : AEMeasurable (fun ω => Y p ω - Y q ω) P :=
    (hmem p).aemeasurable.sub (hmem q).aemeasurable
  have hExpand := covariance_fun_sub_fun_sub (hmem p) (hmem q) (hmem p) (hmem q)
  have hVariance : variance (fun ω => Y p ω - Y q ω) P =
      covariance (Y p) (Y p) P - covariance (Y p) (Y q) P -
        covariance (Y q) (Y p) P + covariance (Y q) (Y q) P := by
    rw [← covariance_self hdiff, hExpand]
  rw [show (fun ω => Y (x, r) ω - Y (y, s) ω) = fun ω => Y p ω - Y q ω by rfl,
    hVariance, hdiagP, hcrossPQ, hcrossQP, hdiagQ]
  dsimp [A, B, Lp, Lq]
  ring

/-- Same-radius circle increments have variance at most a constant times center distance. -/
theorem circleL2_increment_variance_le_center
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : (ℂ × ℝ) → Ω → ℝ)
    (hmem : ∀ p, MemLp (Y p) 2 P)
    (hcov : ∀ p q, covariance (Y p) (Y q) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
    (x y : ℂ) (r : ℝ) :
    variance (fun ω => Y (x, r) ω - Y (y, r) ω) P ≤
      2 * Real.exp r * ‖x-y‖ := by
  let A := ∫ z, Real.log (max (Real.exp (-r)) ‖x-z‖) ∂circleMeasure y r
  let B := ∫ z, Real.log (max (Real.exp (-r)) ‖y-z‖) ∂circleMeasure x r
  rw [circleL2_increment_variance_formula Y hmem hcov x y r r]
  have hA := integral_circle_logmax_sub_le y x r r
  have hB := integral_circle_logmax_sub_le x y r r
  have hA' : A + r ≤ ‖x-y‖ / Real.exp (-r) := by
    dsimp [A] at hA ⊢
    simpa only [Real.log_exp, sub_neg_eq_add, abs_zero, sub_self, add_zero,
      norm_sub_rev] using hA
  have hB' : B + r ≤ ‖x-y‖ / Real.exp (-r) := by
    dsimp [B] at hB ⊢
    simpa only [Real.log_exp, sub_neg_eq_add, abs_zero, sub_self, add_zero,
      norm_sub_rev] using hB
  have hsum : r + r + A + B ≤ 2 * (‖x-y‖ / Real.exp (-r)) := by nlinarith
  have hexp : (Real.exp (-r))⁻¹ = Real.exp r := by
    rw [Real.exp_neg, inv_inv]
  calc
    r + r + A + B ≤ 2 * (‖x-y‖ / Real.exp (-r)) := hsum
    _ = 2 * Real.exp r * ‖x-y‖ := by rw [div_eq_mul_inv, hexp]; ring

/-- The circle L² field on the plane satisfies Kolmogorov's continuity moment criterion. -/
theorem circleL2_isKolmogorovProcess_at_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : (ℂ × ℝ) → Ω → ℝ)
    (hmeas : ∀ p, Measurable (Y p))
    (hmem : ∀ p, MemLp (Y p) 2 P)
    (hproc : IsGaussianProcess (fun p ω => Y p ω) P)
    (hmean : ∀ p, (∫ ω, Y p ω ∂P) = 0)
    (hcov : ∀ p q, covariance (Y p) (Y q) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
    (r : ℝ) :
    ∃ M : ℝ≥0, IsKolmogorovProcess (fun x : ℂ => fun ω => Y (x, r) ω) P 8 4 M := by
  let A := ∫ x : ℝ, |x| ^ 8 ∂gaussianReal 0 1
  let C := 2 * Real.exp r
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let M : ℝ≥0 := ⟨C ^ 4 * A, mul_nonneg (pow_nonneg hC _) hA⟩
  let hprocR : IsGaussianProcess (fun x : ℂ => fun ω => Y (x, r) ω) P :=
    hproc.comp_right (fun x => (x, r))
  refine ⟨M, IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun x => hmeas (x, r)) ?_ (by norm_num) (by norm_num)⟩
  intro x y
  let U : Ω → ℝ := fun ω => Y (x, r) ω - Y (y, r) ω
  have hG : HasGaussianLaw U P := hprocR.hasGaussianLaw_fun_sub (s := x) (t := y)
  have hmeanU : (∫ ω, U ω ∂P) = 0 := by
    have hi := integral_sub ((hmem (x, r)).integrable (by norm_num))
      ((hmem (y, r)).integrable (by norm_num))
    simpa [U, hmean] using hi
  have hvariance := circleL2_increment_variance_le_center Y hmem hcov x y r
  have hvariance' : variance U P ≤ C * dist x y := by
    simpa [U, C, dist_eq_norm] using hvariance
  have hmoment : (∫ ω, |U ω| ^ 8 ∂P) ≤ (C ^ 4 * A) * dist x y ^ 4 := by
    have hm := hasGaussianLaw_integral_abs_pow_le U hG hmeanU 4 hvariance'
    change _ ≤ (C * dist x y) ^ 4 * A at hm
    exact hm.trans_eq (by dsimp [C, A]; ring)
  have hi : Integrable (fun ω => |U ω| ^ 8) P := by
    simpa only [Real.norm_eq_abs] using
      (hG.memLp (p := (8 : ℝ≥0∞)) (by norm_num)).integrable_norm_pow'
  have hlin := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (U ω)) 8))
  have hconv : (∫⁻ ω, edist (Y (x, r) ω) (Y (y, r) ω) ^ (8 : ℝ) ∂P) =
      ENNReal.ofReal (∫ ω, |U ω| ^ 8 ∂P) := by
    rw [hlin]
    apply lintegral_congr
    intro ω
    rw [edist_dist, Real.dist_eq]
    simpa only [ENNReal.rpow_ofNat, U] using (ENNReal.ofReal_pow (abs_nonneg (U ω)) 8).symm
  rw [hconv]
  have hb := ENNReal.ofReal_le_ofReal hmoment
  rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hC _) hA),
    ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist x y) 4] at hb
  change _ ≤ ENNReal.ofReal (C ^ 4 * A) * ENNReal.ofReal (dist x y) ^ 4 at hb
  rw [edist_dist, ENNReal.rpow_ofNat, ← ENNReal.ofReal_coe_nnreal (p := M)]
  exact hb

/-- A continuous sample modification at one fixed logarithmic radius. -/
theorem exists_continuous_circleL2_modification_at_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : (ℂ × ℝ) → Ω → ℝ)
    (hmeas : ∀ p, Measurable (Y p))
    (hmem : ∀ p, MemLp (Y p) 2 P)
    (hproc : IsGaussianProcess (fun p ω => Y p ω) P)
    (hmean : ∀ p, (∫ ω, Y p ω ∂P) = 0)
    (hcov : ∀ p q, covariance (Y p) (Y q) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
    (r : ℝ) :
    ∃ Z : ℂ → Ω → ℝ,
      (∀ x, Measurable (Z x)) ∧
      (∀ ω, Continuous (fun x => Z x ω)) ∧
      ∀ x, Z x =ᵐ[P] fun ω => Y (x, r) ω := by
  obtain ⟨M, hM⟩ := circleL2_isKolmogorovProcess_at_radius
    Y hmeas hmem hproc hmean hcov r
  have hcover := isCoverWithBoundedCoveringNumber_balls ℂ
  rw [show Module.finrank ℝ ℂ = 2 by exact Complex.finrank_real_complex] at hcover
  obtain ⟨Z, hZmeas, hZeq, hZholder⟩ := exists_modification_holder' hcover
    hM.IsAEKolmogorovProcess (fun n => by finiteness) (by norm_num) (by norm_num)
  have hZcont (ω : Ω) : Continuous (fun x => Z x ω) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨U, hU, hholder⟩ := hZholder ω x
    obtain ⟨C, hC⟩ := hholder (1/16) (by norm_num) (by norm_num)
    exact (hC.continuousOn (by norm_num)).continuousAt hU
  exact ⟨Z, hZmeas, hZcont, hZeq⟩

/-- The supplied equator field has a jointly measurable circle-average process on its raw space. -/
theorem exists_equatorGFF_circle_average_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨f, W, Y, hgap, hcross, hW, hY, hproc, hmean, hcov⟩ :=
    exists_equatorGFF_circle_L2_geometry X hX
  have hmeas (p : ℂ × ℝ) : Measurable (Y p) := (hY p).2.1
  have hmem (p : ℂ × ℝ) : MemLp (Y p) 2 P := (hY p).2.2.1
  have hmod (r : ℝ) := exists_continuous_circleL2_modification_at_radius
    Y hmeas hmem hproc hmean hcov r
  choose Z hZmeas hZcont hZeq using hmod
  have hjoint (r : ℝ) := exists_raw_joint_continuous_modification P
    (equatorGFFRawDistributionSigma X)
    (fun ω x => Z r x ω) (ae_of_all P (hZcont r))
    (fun x => ⟨Y (x, r), (hY (x, r)).1, (hZeq r x).symm⟩)
  choose G hGjoint hGae using hjoint
  let Xc : Ω → ℂ → ℝ → ℝ := fun ω x r => G r ω x
  have hmap : Measurable[mΩ] (fun ω => fun g : TestFn => X ω g) :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := by
    dsimp [equatorGFFRawDistributionSigma]
    exact hmap.comap_le
  let mℂ : MeasurableSpace ℂ := borel ℂ
  have hprod : (equatorGFFRawDistributionSigma X).prod mℂ ≤ mΩ.prod mℂ := by
    rw [MeasurableSpace.prod, MeasurableSpace.prod]
    exact sup_le_sup (MeasurableSpace.comap_mono hm0) le_rfl
  have hmeasXc (r : ℝ) : Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r) := by
    change Measurable (fun p : Ω × ℂ => G r p.1 p.2)
    exact (hGjoint r).mono hprod le_rfl
  have hXcY (x : ℂ) (r : ℝ) : (fun ω => Xc ω x r) =ᵐ[P] fun ω => Y (x, r) ω := by
    filter_upwards [hGae r, hZeq r x] with ω hG hZ
    exact (hG x).trans hZ
  refine ⟨Xc, hmeasXc, fun x r => ?_, ?_⟩
  · exact MemLp.ae_eq (hXcY x r).symm (hmem (x, r))
  · intro x r g hg
    let p : ℂ × ℝ := (x, r)
    let U : ℕ → Lp ℝ 2 P := fun n =>
      (equatorGFF_test_memLp X hX (g n)).toLp (fun ω => X ω (g n))
    have hUT : Tendsto U atTop (𝓝 (W p)) := by
      exact equatorGFF_testL2_tendsto_to_circle_limit X hX x r
        (f p) (hgap p) (W p) (hW p) g hg
    have hTarget : (fun ω => Xc ω x r) =ᵐ[P] ⇑(W p) := by
      exact (hXcY x r).trans (hY p).2.2.2.1
    exact tendsto_eLpNorm_sub_of_L2_versions P U (W p)
      (fun n ω => X ω (g n)) (fun ω => Xc ω x r)
      (fun n => (equatorGFF_test_memLp X hX (g n)).coeFn_toLp.symm)
      hTarget hUT

end DOZZ.Proofs
