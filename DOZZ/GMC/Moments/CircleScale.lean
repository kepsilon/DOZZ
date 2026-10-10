/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.CircleAverageGaussian
public import DOZZ.GMC.Moments.GaussianFDD

/-! Local covariance scaling for equator circle averages. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Dilating a circle by a positive factor is the pushforward of its normalized arclength
measure. Logarithmic radius is shifted by the inverse dilation. -/
theorem circleMeasure_scale {c : ℝ} (hc : 0 < c) (x : ℂ) (s : ℝ) :
    circleMeasure (c * x) (s - Real.log c) =
      Measure.map (fun z : ℂ => c * z) (circleMeasure x s) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let scale : ℂ → ℂ := fun z => c * z
  have hrad : Real.exp (-(s - Real.log c)) = c * Real.exp (-s) := by
    calc
      Real.exp (-(s - Real.log c)) = Real.exp (Real.log c + -s) := by congr 1; ring
      _ = Real.exp (Real.log c) * Real.exp (-s) := Real.exp_add _ _
      _ = c * Real.exp (-s) := by rw [Real.exp_log hc]
  have hcircle :
      (fun θ : ℝ => circleMap (c * x) (Real.exp (-(s - Real.log c))) θ) =
        scale ∘ circleMap x (Real.exp (-s)) := by
    funext θ
    dsimp [scale]
    rw [circleMap, circleMap, hrad]
    push_cast
    ring
  have hscale : Measurable scale := by fun_prop
  have hangle : Measurable (circleMap x (Real.exp (-s))) :=
    measurable_circleMap _ _
  unfold circleMeasure
  change ENNReal.ofReal (2 * Real.pi)⁻¹ •
      μ.map (circleMap (c * x) (Real.exp (-(s - Real.log c)))) =
    Measure.map scale
      (ENNReal.ofReal (2 * Real.pi)⁻¹ • μ.map (circleMap x (Real.exp (-s))))
  rw [Measure.map_smul _ hscale.aemeasurable,
    Measure.map_map hscale hangle, ← hcircle]

/-- The clipped logarithmic interaction of two circles gains `log c` under a common dilation.
The proof uses the pushforward formula for normalized arclength, so it also covers tangent and
intersecting circles without branch analysis of the closed potential series. -/
theorem circleLogPotential_scale {c : ℝ} (hc : 0 < c) (x y : ℂ) (r s : ℝ) :
    circleLogPotential ‖c * x - c * y‖₊
        ⟨Real.exp (-(r - Real.log c)), Real.exp_pos _⟩
        ⟨Real.exp (-(s - Real.log c)), Real.exp_pos _⟩ =
      Real.log c + circleLogPotential ‖x - y‖₊
        ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨Real.exp (-s), Real.exp_pos _⟩ := by
  let f : ℂ → ℝ := fun w => Real.log (max (Real.exp (-(s - Real.log c))) ‖w - c * y‖)
  let g : ℂ → ℝ := fun w => Real.log (max (Real.exp (-s)) ‖w - y‖)
  have hfcont : Continuous f := by
    dsimp [f]
    have hdist : Continuous (fun w : ℂ => ‖w - c * y‖) := by fun_prop
    exact (continuous_const.max hdist).log
      (fun _ => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))
  have hgcont : Continuous g := by
    dsimp [g]
    have hdist : Continuous (fun w : ℂ => ‖w - y‖) := by fun_prop
    exact (continuous_const.max hdist).log
      (fun _ => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))
  have hfint : Integrable f (circleMeasure (c * x) (r - Real.log c)) :=
    integrable_circleMeasure_of_circleIntegrable _ _ hfcont.measurable
      hfcont.continuousOn.circleIntegrable'
  have hgint : Integrable g (circleMeasure x r) :=
    integrable_circleMeasure_of_circleIntegrable _ _ hgcont.measurable
      hgcont.continuousOn.circleIntegrable'
  have hscale : Measurable (fun z : ℂ => c * z) := by fun_prop
  have hrad : Real.exp (-(s - Real.log c)) = c * Real.exp (-s) := by
    calc
      Real.exp (-(s - Real.log c)) = Real.exp (Real.log c + -s) := by congr 1; ring
      _ = Real.exp (Real.log c) * Real.exp (-s) := Real.exp_add _ _
      _ = c * Real.exp (-s) := by rw [Real.exp_log hc]
  have hintegrand (z : ℂ) : f (c * z) = Real.log c + g z := by
    dsimp [f, g]
    have hnorm : ‖c * z - c * y‖ = c * ‖z - y‖ := by
      rw [← mul_sub, norm_mul]
      have hcNorm : ‖(c : ℂ)‖ = c := by simp [abs_of_pos hc]
      rw [hcNorm]
    rw [hrad, hnorm, ← mul_max_of_nonneg _ _ hc.le,
      Real.log_mul hc.ne' (ne_of_gt
        (lt_of_lt_of_le (Real.exp_pos (-s)) (le_max_left _ _)))]
  calc
    circleLogPotential ‖c * x - c * y‖₊
        ⟨Real.exp (-(r - Real.log c)), Real.exp_pos _⟩
        ⟨Real.exp (-(s - Real.log c)), Real.exp_pos _⟩ =
      ∫ w, f w ∂circleMeasure (c * x) (r - Real.log c) := by
        symm
        exact integral_logmax_circleMeasure_eq_closed _ _ _ (Real.exp_pos _)
    _ = ∫ z, f (c * z) ∂circleMeasure x r := by
        rw [circleMeasure_scale hc x r]
        exact integral_map hscale.aemeasurable hfcont.measurable.aestronglyMeasurable
    _ = ∫ z, (Real.log c + g z) ∂circleMeasure x r := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hintegrand
    _ = Real.log c + ∫ z, g z ∂circleMeasure x r := by
        let _ := circleMeasure_isProbability x r
        rw [integral_add (integrable_const _) hgint, integral_const, probReal_univ, one_smul]
    _ = Real.log c + circleLogPotential ‖x - y‖₊
        ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨Real.exp (-s), Real.exp_pos _⟩ := by
        rw [integral_logmax_circleMeasure_eq_closed]

/-- The regular pinning potential vanishes when the entire averaging circle is in the unit
logarithmic chart. -/
theorem circleLogPotential_pin_eq_zero_of_inside {x : ℂ} {r : ℝ}
    (hinside : ‖x‖ + Real.exp (-r) ≤ 1) :
    circleLogPotential ‖x‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ = 0 := by
  rw [← integral_log_normPlus_circleMeasure_eq_closed]
  have hzero : (fun w : ℂ => Real.log (normPlus w)) =ᵐ[circleMeasure x r] fun _ => 0 := by
    filter_upwards [ae_norm_sub_le_center_add_circleMeasure x 0 r] with w hw
    have hinside' : ‖x - 0‖ + Real.exp (-r) ≤ 1 := by simpa using hinside
    have hn : ‖w‖ ≤ 1 := by
      simpa only [sub_zero] using hw.trans hinside'
    simp [normPlus, max_eq_left hn]
  rw [integral_congr_ae hzero, integral_zero]

/-- In the unit logarithmic chart, common dilation adds one independent scalar variance to every
pair of circle averages. -/
theorem circleAverage_covariance_scale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    {c : ℝ} (hscale : 0 < c) (x y : ℂ) (r s : ℝ)
    (hx : ‖x‖ + Real.exp (-r) ≤ 1) (hy : ‖y‖ + Real.exp (-s) ≤ 1)
    (hcx : ‖c * x‖ + Real.exp (-(r - Real.log c)) ≤ 1)
    (hcy : ‖c * y‖ + Real.exp (-(s - Real.log c)) ≤ 1) :
    covariance (fun ω => Xc ω (c * x) (r - Real.log c))
        (fun ω => Xc ω (c * y) (s - Real.log c)) P =
      covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P - Real.log c := by
  rw [circleAverage_covariance P X Xc hX hc (c * x) (c * y)
      (r - Real.log c) (s - Real.log c),
    circleAverage_covariance P X Xc hX hc x y r s,
    circleLogPotential_scale hscale x y r s,
    circleLogPotential_pin_eq_zero_of_inside hcx,
    circleLogPotential_pin_eq_zero_of_inside hcy,
    circleLogPotential_pin_eq_zero_of_inside hx,
    circleLogPotential_pin_eq_zero_of_inside hy]
  ring

/-- Translation does not affect the local logarithmic covariance, so the common-scalar
covariance shift also holds for an affine map `x ↦ a + c*x`. -/
theorem circleAverage_covariance_affine_scale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    {a : ℂ} {c : ℝ} (hscale : 0 < c) (x y : ℂ) (r s : ℝ)
    (hx : ‖x‖ + Real.exp (-r) ≤ 1) (hy : ‖y‖ + Real.exp (-s) ≤ 1)
    (hax : ‖a + c * x‖ + Real.exp (-(r - Real.log c)) ≤ 1)
    (hay : ‖a + c * y‖ + Real.exp (-(s - Real.log c)) ≤ 1) :
    covariance (fun ω => Xc ω (a + c * x) (r - Real.log c))
        (fun ω => Xc ω (a + c * y) (s - Real.log c)) P =
      covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P - Real.log c := by
  rw [circleAverage_covariance P X Xc hX hc (a + c * x) (a + c * y)
      (r - Real.log c) (s - Real.log c),
    circleAverage_covariance P X Xc hX hc x y r s]
  have hdiff : (a + c * x) - (a + c * y) = c * x - c * y := by ring
  rw [hdiff]
  rw [circleLogPotential_scale hscale x y r s]
  rw [circleLogPotential_pin_eq_zero_of_inside hax,
    circleLogPotential_pin_eq_zero_of_inside hay,
    circleLogPotential_pin_eq_zero_of_inside hx,
    circleLogPotential_pin_eq_zero_of_inside hy]
  ring

/-- Finite-dimensional circle-average laws transform by adjoining one independent Gaussian scalar.
This is the precise field-law input for the finite-cutoff chaos scaling identity. -/
theorem circleAverage_scaled_fdd_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    {c : ℝ} (hscale : 0 < c) (hc_le : c ≤ 1)
    (z : ι → ℂ) (r : ι → ℝ)
    (hbase : ∀ i, ‖z i‖ + Real.exp (-r i) ≤ 1)
    (hscaled : ∀ i, ‖c * z i‖ + Real.exp (-(r i - Real.log c)) ≤ 1) :
    Measure.map (fun ω i => Xc ω (c * z i) (r i - Real.log c)) P =
      Measure.map (fun p : Ω × ℝ => fun i => Xc p.1 (z i) (r i) + p.2)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos (le_of_lt hscale) hc_le)⟩)) := by
  let : IsProbabilityMeasure P := hX.1
  let v : ℝ≥0 := ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos (le_of_lt hscale) hc_le)⟩
  let G : Measure ℝ := gaussianReal 0 v
  let A : ι → Ω → ℝ := fun i ω => Xc ω (z i) (r i)
  let T : Ω → ι → ℝ := fun ω i => Xc ω (c * z i) (r i - Real.log c)
  let B : Ω × ℝ → ι → ℝ := fun p i => A i p.1 + p.2
  have hW : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v) G := by
    exact ⟨aemeasurable_id, Measure.map_id⟩
  have hA : IsCenteredJointlyGaussian P (fun ω i => A i ω) := by
    simpa [A] using circleAverage_finite_family_jointly_gaussian P X hX Xc hc
      (fun i => (z i, r i))
  have hT : IsCenteredJointlyGaussian P T := by
    simpa [T] using circleAverage_finite_family_jointly_gaussian P X hX Xc hc
      (fun i => (c * z i, r i - Real.log c))
  have hB : IsCenteredJointlyGaussian (P.prod G) B := by
    simpa [A, B, G] using
      isCenteredJointlyGaussian_add_independent_scalar (fun ω i => Xc ω (z i) (r i))
        (id : ℝ → ℝ) hA hW
  have hcircleMean := (circleAverage_isGaussianProcess P X Xc hX hc).2
  have hTmean (i : ι) : (∫ ω, T ω i ∂P) = 0 := by
    exact hcircleMean (c * z i) (r i - Real.log c)
  have hAmean (i : ι) : (∫ ω, A i ω ∂P) = 0 := by
    exact hcircleMean (z i) (r i)
  have hBmean (i : ι) : (∫ p, B p i ∂(P.prod G)) = 0 := by
    exact coord_mean (P.prod G) B hB i
  have htargetCov (i j : ι) :
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
        covariance (fun ω => T ω i) (fun ω => T ω j) P := by
    calc
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
          ∫ ω, T ω i * T ω j ∂P := rfl
      _ = covariance (fun ω => T ω i) (fun ω => T ω j) P := by
        symm
        simp only [ProbabilityTheory.covariance]
        rw [hTmean i, hTmean j]
        simp
  have hshiftCov (i j : ι) :
      gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) =
        covariance (fun p => B p i) (fun p => B p j) (P.prod G) := by
    calc
      gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) =
          ∫ p, B p i * B p j ∂(P.prod G) := rfl
      _ = covariance (fun p => B p i) (fun p => B p j) (P.prod G) := by
        symm
        simp only [ProbabilityTheory.covariance]
        rw [hBmean i, hBmean j]
        simp
  have hproductCov (i j : ι) :
      covariance (fun p : Ω × ℝ => A i p.1 + p.2)
          (fun p => A j p.1 + p.2) (P.prod G) =
        covariance (A i) (A j) P + (v : ℝ) := by
    let Ai : Ω → ℝ := A i
    let Aj : Ω → ℝ := A j
    have hAi : MemLp Ai 2 P := hc.2.1 (z i) (r i)
    have hAj : MemLp Aj 2 P := hc.2.1 (z j) (r j)
    have hScalar : MemLp (id : ℝ → ℝ) 2 G := by
      exact memLp_id_gaussianReal 2
    let AiProd : Ω × ℝ → ℝ := fun p => Ai p.1
    let AjProd : Ω × ℝ → ℝ := fun p => Aj p.1
    let WProd : Ω × ℝ → ℝ := fun p => p.2
    have hAiProd : MemLp AiProd 2 (P.prod G) := hAi.comp_fst G
    have hAjProd : MemLp AjProd 2 (P.prod G) := hAj.comp_fst G
    have hWProd : MemLp WProd 2 (P.prod G) := hScalar.comp_snd P
    have hBaseCov : covariance Ai Aj P = covariance AiProd AjProd (P.prod G) := by
      have hAiMap : AEStronglyMeasurable Ai ((P.prod G).map Prod.fst) := by
        rw [measurePreserving_fst.map_eq]
        exact hAi.aestronglyMeasurable
      have hAjMap : AEStronglyMeasurable Aj ((P.prod G).map Prod.fst) := by
        rw [measurePreserving_fst.map_eq]
        exact hAj.aestronglyMeasurable
      have h := covariance_map_fun hAiMap hAjMap measurable_fst.aemeasurable
      simpa [AiProd, AjProd] using h
    have hNoiseCov : covariance WProd WProd (P.prod G) = (v : ℝ) := by
      have hWMap : AEStronglyMeasurable (id : ℝ → ℝ) ((P.prod G).map Prod.snd) := by
        rw [measurePreserving_snd.map_eq]
        exact hScalar.aestronglyMeasurable
      have h := covariance_map_fun hWMap hWMap measurable_snd.aemeasurable
      rw [measurePreserving_snd.map_eq] at h
      calc
        covariance WProd WProd (P.prod G) = covariance (id : ℝ → ℝ) id G := by
          simpa [WProd] using h.symm
        _ = variance (id : ℝ → ℝ) G := covariance_self hScalar.aemeasurable
        _ = (v : ℝ) := by simp [G]
    have hcross₁ : covariance AiProd WProd (P.prod G) = 0 :=
      covariance_fst_snd_prod hAi hScalar
    have hcross₂ : covariance WProd AjProd (P.prod G) = 0 := by
      rw [covariance_comm]
      exact covariance_fst_snd_prod hAj hScalar
    change covariance (AiProd + WProd) (AjProd + WProd) (P.prod G) = _
    rw [covariance_add_left hAiProd hWProd (hAjProd.add hWProd),
      covariance_add_right hAiProd hAjProd hWProd,
      covariance_add_right hWProd hAjProd hWProd]
    rw [hcross₁, hcross₂, hNoiseCov, ← hBaseCov]
    ring
  have hcov (i j : ι) :
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
        gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) := by
    calc
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
          covariance (fun ω => T ω i) (fun ω => T ω j) P := htargetCov i j
      _ = covariance (A i) (A j) P - Real.log c := by
          exact circleAverage_covariance_scale P X Xc hX hc hscale (z i) (z j)
            (r i) (r j) (hbase i) (hbase j) (hscaled i) (hscaled j)
      _ = covariance (A i) (A j) P + (v : ℝ) := by
          have hv : (v : ℝ) = -Real.log c := rfl
          rw [hv]
          ring
      _ = covariance (fun p => B p i) (fun p => B p j) (P.prod G) :=
          (hproductCov i j).symm
      _ = gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) :=
          (hshiftCov i j).symm
  exact map_eq_of_centeredJointlyGaussian_of_covariance_eq P (P.prod G) T B hT hB hcov

/-- Affine form of `circleAverage_scaled_fdd_law`, used for exact scaling of masses in disks
whose center is not the origin. -/
theorem circleAverage_affine_scaled_fdd_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    {a : ℂ} {c : ℝ} (hscale : 0 < c) (hc_le : c ≤ 1)
    (z : ι → ℂ) (r : ι → ℝ)
    (hbase : ∀ i, ‖z i‖ + Real.exp (-r i) ≤ 1)
    (hscaled : ∀ i, ‖a + c * z i‖ + Real.exp (-(r i - Real.log c)) ≤ 1) :
    Measure.map (fun ω i => Xc ω (a + c * z i) (r i - Real.log c)) P =
      Measure.map (fun p : Ω × ℝ => fun i => Xc p.1 (z i) (r i) + p.2)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos (le_of_lt hscale) hc_le)⟩)) := by
  let : IsProbabilityMeasure P := hX.1
  let v : ℝ≥0 := ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos (le_of_lt hscale) hc_le)⟩
  let G : Measure ℝ := gaussianReal 0 v
  let A : ι → Ω → ℝ := fun i ω => Xc ω (z i) (r i)
  let T : Ω → ι → ℝ := fun ω i => Xc ω (a + c * z i) (r i - Real.log c)
  let B : Ω × ℝ → ι → ℝ := fun p i => A i p.1 + p.2
  have hW : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v) G := by
    exact ⟨aemeasurable_id, Measure.map_id⟩
  have hA : IsCenteredJointlyGaussian P (fun ω i => A i ω) := by
    simpa [A] using circleAverage_finite_family_jointly_gaussian P X hX Xc hc
      (fun i => (z i, r i))
  have hT : IsCenteredJointlyGaussian P T := by
    simpa [T] using circleAverage_finite_family_jointly_gaussian P X hX Xc hc
      (fun i => (a + c * z i, r i - Real.log c))
  have hB : IsCenteredJointlyGaussian (P.prod G) B := by
    simpa [A, B, G] using
      isCenteredJointlyGaussian_add_independent_scalar (fun ω i => Xc ω (z i) (r i))
        (id : ℝ → ℝ) hA hW
  have hcircleMean := (circleAverage_isGaussianProcess P X Xc hX hc).2
  have hTmean (i : ι) : (∫ ω, T ω i ∂P) = 0 := by
    exact hcircleMean (a + c * z i) (r i - Real.log c)
  have hAmean (i : ι) : (∫ ω, A i ω ∂P) = 0 := by
    exact hcircleMean (z i) (r i)
  have hBmean (i : ι) : (∫ p, B p i ∂(P.prod G)) = 0 := by
    exact coord_mean (P.prod G) B hB i
  have htargetCov (i j : ι) :
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
        covariance (fun ω => T ω i) (fun ω => T ω j) P := by
    calc
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
          ∫ ω, T ω i * T ω j ∂P := rfl
      _ = covariance (fun ω => T ω i) (fun ω => T ω j) P := by
        symm
        simp only [ProbabilityTheory.covariance]
        rw [hTmean i, hTmean j]
        simp
  have hshiftCov (i j : ι) :
      gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) =
        covariance (fun p => B p i) (fun p => B p j) (P.prod G) := by
    calc
      gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) =
          ∫ p, B p i * B p j ∂(P.prod G) := rfl
      _ = covariance (fun p => B p i) (fun p => B p j) (P.prod G) := by
        symm
        simp only [ProbabilityTheory.covariance]
        rw [hBmean i, hBmean j]
        simp
  have hproductCov (i j : ι) :
      covariance (fun p : Ω × ℝ => A i p.1 + p.2)
          (fun p => A j p.1 + p.2) (P.prod G) = covariance (A i) (A j) P + (v : ℝ) := by
    let Ai : Ω → ℝ := A i
    let Aj : Ω → ℝ := A j
    have hAi : MemLp Ai 2 P := hc.2.1 (z i) (r i)
    have hAj : MemLp Aj 2 P := hc.2.1 (z j) (r j)
    have hScalar : MemLp (id : ℝ → ℝ) 2 G := memLp_id_gaussianReal 2
    let AiProd : Ω × ℝ → ℝ := fun p => Ai p.1
    let AjProd : Ω × ℝ → ℝ := fun p => Aj p.1
    let WProd : Ω × ℝ → ℝ := fun p => p.2
    have hAiProd : MemLp AiProd 2 (P.prod G) := hAi.comp_fst G
    have hAjProd : MemLp AjProd 2 (P.prod G) := hAj.comp_fst G
    have hWProd : MemLp WProd 2 (P.prod G) := hScalar.comp_snd P
    have hBaseCov : covariance Ai Aj P = covariance AiProd AjProd (P.prod G) := by
      have hAiMap : AEStronglyMeasurable Ai ((P.prod G).map Prod.fst) := by
        rw [measurePreserving_fst.map_eq]
        exact hAi.aestronglyMeasurable
      have hAjMap : AEStronglyMeasurable Aj ((P.prod G).map Prod.fst) := by
        rw [measurePreserving_fst.map_eq]
        exact hAj.aestronglyMeasurable
      have h := covariance_map_fun hAiMap hAjMap measurable_fst.aemeasurable
      simpa [AiProd, AjProd] using h
    have hNoiseCov : covariance WProd WProd (P.prod G) = (v : ℝ) := by
      have hWMap : AEStronglyMeasurable (id : ℝ → ℝ) ((P.prod G).map Prod.snd) := by
        rw [measurePreserving_snd.map_eq]
        exact hScalar.aestronglyMeasurable
      have h := covariance_map_fun hWMap hWMap measurable_snd.aemeasurable
      rw [measurePreserving_snd.map_eq] at h
      calc
        covariance WProd WProd (P.prod G) = covariance (id : ℝ → ℝ) id G := by
          simpa [WProd] using h.symm
        _ = variance (id : ℝ → ℝ) G :=
          covariance_self hScalar.aestronglyMeasurable.aemeasurable
        _ = (v : ℝ) := by simp [G]
    have hcross₁ : covariance AiProd WProd (P.prod G) = 0 :=
      covariance_fst_snd_prod hAi hScalar
    have hcross₂ : covariance WProd AjProd (P.prod G) = 0 := by
      rw [covariance_comm]
      exact covariance_fst_snd_prod hAj hScalar
    change covariance (AiProd + WProd) (AjProd + WProd) (P.prod G) = _
    rw [covariance_add_left hAiProd hWProd (hAjProd.add hWProd),
      covariance_add_right hAiProd hAjProd hWProd,
      covariance_add_right hWProd hAjProd hWProd]
    rw [hcross₁, hcross₂, hNoiseCov, ← hBaseCov]
    ring
  have hcov (i j : ι) :
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
        gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) := by
    calc
      gaussianCovariance P (fun ω => T ω i) (fun ω => T ω j) =
          covariance (fun ω => T ω i) (fun ω => T ω j) P := htargetCov i j
      _ = covariance (A i) (A j) P - Real.log c := by
          exact circleAverage_covariance_affine_scale P X Xc hX hc hscale
            (z i) (z j) (r i) (r j) (hbase i) (hbase j) (hscaled i) (hscaled j)
      _ = covariance (A i) (A j) P + (v : ℝ) := by
          have hv : (v : ℝ) = -Real.log c := rfl
          rw [hv]
          ring
      _ = covariance (fun p => B p i) (fun p => B p j) (P.prod G) :=
          (hproductCov i j).symm
      _ = gaussianCovariance (P.prod G) (fun p => B p i) (fun p => B p j) :=
          (hshiftCov i j).symm
  exact map_eq_of_centeredJointlyGaussian_of_covariance_eq P (P.prod G) T B hT hB hcov

end DOZZ.Proofs
