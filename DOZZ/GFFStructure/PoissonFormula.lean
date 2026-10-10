/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonL2
public import Mathlib.Analysis.Complex.JensenFormula
/-!
# Exact Poisson covariance and compact continuous versions

The logarithmic boundary Poisson formula and the regular disk Green reproduction identify actual
collar-limit covariances with the numerator logarithm in the harmonic covariance formula of
`DOZZ.exists_exteriorPinned_markov_uniform`. Their increments have an explicit quadratic bound on
every compact inner disk. Gaussian eighth moments and the proved dimension-two covering estimate
construct jointly measurable continuous versions on these disks in the original probability space.
Circle-integrable boundary data admit smooth harmonic Poisson extensions. Identification and gluing
of those extensions, and the Dirichlet distribution assembly, remain separate steps.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs

/-- Unit-circle integration of a Poisson weighted observable is its disk Poisson average. -/
theorem integral_unitPoissonWeight_mul_eq_circleAverage (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ u, unitPoissonWeight c ρ z u*f (c+ρ • u) ∂circleMeasure 0 0) =
      Real.circleAverage (poissonKernel c z*f) c ρ := by
  have hm : Measurable (fun u : ℂ => unitPoissonWeight c ρ z u*f (c+ρ • u)) := by
    exact (measurable_unitPoissonWeight c z ρ).mul (hf.comp (by fun_prop))
  rw [integral_circleMeasure_eq_circleAverage 0 0 _ hm]
  simp only [neg_zero, Real.exp_zero]
  rw [Real.circleAverage_def, Real.circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only [Pi.mul_apply]
  have hn : ‖circleMap 0 1 θ‖ = 1 := by simp only [norm_circleMap_zero, abs_one]
  rw [unitPoissonWeight_eq_poissonKernel c z (circleMap 0 1 θ) ρ hρ hn]
  have he : c+ρ • circleMap 0 1 θ = circleMap c ρ θ := by
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
  rw [he]

/-- The boundary logarithm is reproduced at every interior point. -/
theorem integral_unitPoissonWeight_boundary_log (c z v : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hv : ‖v‖ = 1) :
    (∫ u, unitPoissonWeight c ρ z u*Real.log ‖ρ • u-ρ • v‖ ∂circleMeasure 0 0) =
      Real.log ‖z-(c+ρ • v)‖ := by
  have hb : c+ρ • v ∈ sphere c ρ := by
    rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ, hv, mul_one]
  have he : (fun u : ℂ => Real.log ‖ρ • u-ρ • v‖) =
      (fun u : ℂ => Real.log ‖(c+ρ • u)-(c+ρ • v)‖) := by
    funext u
    congr 2
    abel
  have he' : (fun u : ℂ => unitPoissonWeight c ρ z u*Real.log ‖ρ • u-ρ • v‖) =
      (fun u : ℂ => unitPoissonWeight c ρ z u*Real.log ‖(c+ρ • u)-(c+ρ • v)‖) :=
    congrArg (fun f : ℂ → ℝ => fun u => unitPoissonWeight c ρ z u*f u) he
  rw [he', integral_unitPoissonWeight_mul_eq_circleAverage c z ρ hρ
    (fun u => Real.log ‖u-(c+ρ • v)‖) (by fun_prop)]
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact circleAverage_re_herglotzRieszKernel_mul_log hb hz

/-- With an interior pole, the boundary logarithm reproduces the regular Green numerator. -/
theorem integral_unitPoissonWeight_interior_log (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) :
    (∫ u, unitPoissonWeight c ρ z u*Real.log ‖c+ρ • u-w‖ ∂circleMeasure 0 0) =
      Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖-Real.log ρ := by
  have heq : ∀ᵐ u ∂circleMeasure 0 0,
      unitPoissonWeight c ρ z u*Real.log ‖c+ρ • u-w‖ =
        unitPoissonWeight c ρ z u*
          (Real.log ‖(ρ : ℂ)^2-((c+ρ • u)-c)*star (w-c)‖-Real.log ρ) := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
    have hu' : ‖u‖ = 1 := by simpa only [sub_zero, neg_zero, Real.exp_zero] using hu
    have hs : c+ρ • u ∈ sphere c ρ := by
      rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hρ, hu', mul_one]
    have hne : c+ρ • u ≠ w := by
      intro h
      have hn := mem_sphere_iff_norm.mp hs
      rw [h] at hn
      exact (mem_ball_iff_norm.mp hw).ne hn
    have hratio := diskGreen_ratio_eq_one_on_sphere c (c+ρ • u) w ρ hρ hs hw
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      div_eq_one_iff_eq (mul_ne_zero hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))] at hratio
    rw [hratio, Real.log_mul hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))]
    ring
  rw [integral_congr_ae heq]
  have hf : Integrable (fun u : ℂ => unitPoissonWeight c ρ z u*
      Real.log ‖(ρ : ℂ)^2-((c+ρ • u)-c)*star (w-c)‖) (circleMeasure 0 0) := by
    let _ := circleMeasure_isProbability (0 : ℂ) 0
    obtain ⟨M,hM⟩ := (isCompact_closedBall c ρ).exists_bound_of_continuousOn
      ((contDiffOn_diskGreen_regular c w ρ hρ hw).continuousOn)
    let K := ρ^2/(ρ-‖z-c‖)^2
    apply (integrable_const (K*M)).mono'
      ((measurable_unitPoissonWeight c z ρ).mul (by fun_prop)).aestronglyMeasurable
    filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
    have hu' : ‖u‖ = 1 := by simpa only [sub_zero, neg_zero, Real.exp_zero] using hu
    have hball : c+ρ • u ∈ closedBall c ρ := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hρ, hu', mul_one]
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (unitPoissonWeight_nonneg c z u ρ hρ hz)]
    exact mul_le_mul (unitPoissonWeight_le c z u ρ ‖z-c‖ hρ
      (mem_ball_iff_norm.mp hz) le_rfl hu') (hM _ hball) (norm_nonneg _)
      (by dsimp only [K]; positivity)
  simp_rw [mul_sub]
  rw [integral_sub hf ((integrable_unitPoissonWeight c z ρ hρ hz).mul_const _),
    integral_mul_const, integral_unitPoissonWeight c z ρ hρ hz, one_mul]
  have hi := integral_unitPoissonWeight_mul_eq_circleAverage c z ρ hρ
    (fun v : ℂ => Real.log ‖(ρ : ℂ)^2-(v-c)*star (w-c)‖) (by fun_prop)
  rw [hi]
  exact congrArg (fun t : ℝ => t-Real.log ρ)
    (circleAverage_poisson_diskGreen_regular c z w ρ hρ hz hw)

/-- The double Poisson boundary log energy is the literal regular numerator logarithm. -/
theorem integral_unitPoissonWeight_pair_log (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) :
    (∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
      Real.log ‖ρ • p.1-ρ • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) =
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖-Real.log ρ := by
  let a := (max ‖z-c‖ ‖w-c‖+ρ)/2
  have haρ : a < ρ := by
    have hzw := max_lt (mem_ball_iff_norm.mp hz) (mem_ball_iff_norm.mp hw)
    dsimp only [a]
    linarith
  have hza : ‖z-c‖ ≤ a := by dsimp only [a]; linarith [le_max_left ‖z-c‖ ‖w-c‖, mem_ball_iff_norm.mp hz]
  have hwa : ‖w-c‖ ≤ a := by dsimp only [a]; linarith [le_max_right ‖z-c‖ ‖w-c‖, mem_ball_iff_norm.mp hw]
  have hi := integrable_poisson_radial_circleLog c z w ρ a ρ ρ ρ hρ haρ hza hwa
    le_rfl le_rfl le_rfl le_rfl
  rw [integral_prod_symm _ hi]
  have heq : ∀ᵐ v ∂circleMeasure 0 0,
      (∫ u, unitPoissonWeight c ρ z u*unitPoissonWeight c ρ w v*
        Real.log ‖ρ • u-ρ • v‖ ∂circleMeasure 0 0) =
          unitPoissonWeight c ρ w v*Real.log ‖c+ρ • v-z‖ := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with v hv
    have hv' : ‖v‖ = 1 := by simpa only [sub_zero, neg_zero, Real.exp_zero] using hv
    calc
      _ = unitPoissonWeight c ρ w v*(∫ u, unitPoissonWeight c ρ z u*
          Real.log ‖ρ • u-ρ • v‖ ∂circleMeasure 0 0) := by
        rw [← integral_const_mul]
        congr 1
        funext u
        ring
      _ = unitPoissonWeight c ρ w v*Real.log ‖c+ρ • v-z‖ := by
        rw [integral_unitPoissonWeight_boundary_log c z v ρ hρ hz hv', norm_sub_rev z]
  rw [integral_congr_ae heq, integral_unitPoissonWeight_interior_log c w z ρ hρ hw hz]
  congr 2
  calc
    _ = ‖star ((ρ : ℂ)^2-(z-c)*star (w-c))‖ := by
      simp only [Complex.star_def, map_sub, map_pow, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      congr 1
      ring
    _ = _ := norm_star _

/-- The Poisson collar covariance agrees with the harmonic covariance formula of
`DOZZ.exists_exteriorPinned_markov_uniform`. -/
theorem exteriorPinned_poisson_rawLimit_covariance_closed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z w : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ)
    (H J : Ω → ℝ) (hH : MemLp H 2 P) (hJ : MemLp J 2 P)
    (hHl : Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-H ω) 2 P) atTop (𝓝 0))
    (hJl : Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
      (canonicalPoissonCollarTest c w ρ ε hρ hε hw k)-J ω) 2 P) atTop (𝓝 0)) :
    covariance H J P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ := by
  rw [exteriorPinned_poisson_rawLimit_covariance P X Xc hX hc c z w R ρ ε δ hR hρ hε
    hεδ hpin hz hw H J hH hJ hHl hJl, integral_unitPoissonWeight_pair_log c z w ρ hρ hz hw]
  ring

/-- The diagonal regular Green numerator is the positive squared-radius gap. -/
theorem norm_diskGreen_numerator_self (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) :
    ‖(ρ : ℂ)^2-(z-c)*star (z-c)‖ = ρ^2-‖z-c‖^2 := by
  have he : (ρ : ℂ)^2-(z-c)*star (z-c) = ((ρ^2-‖z-c‖^2 : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_sub, Complex.ofReal_pow]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (poissonNumerator_pos c z ρ hρ hz)]

/-- The regular numerator's squared norm is the product of the diagonal gaps plus distance. -/
theorem norm_diskGreen_numerator_sq (c z w : ℂ) (ρ : ℝ) :
    ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖^2 =
      (ρ^2-‖z-c‖^2)*(ρ^2-‖w-c‖^2)+ρ^2*‖z-w‖^2 := by
  have hi := diskGreen_norm_identity ρ (z-c) (w-c)
  rw [show (z-c)-(w-c) = z-w by ring] at hi
  linarith

/-- The exact harmonic covariance gives a logarithmic formula for its increment variance. -/
theorem poisson_gaussian_increment_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (R ρ : ℝ) (hρ : 0 < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ)
    (hmem : ∀ z, MemLp (H z) 2 P)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖)
    (z w : {z : ℂ // z ∈ ball c ρ}) :
    variance (fun ω => H z ω-H w ω) P =
      Real.log (1+ρ^2*‖z.1-w.1‖^2/((ρ^2-‖z.1-c‖^2)*(ρ^2-‖w.1-c‖^2))) := by
  have hz := poissonNumerator_pos c z.1 ρ hρ z.2
  have hw := poissonNumerator_pos c w.1 ρ hρ w.2
  have hn := norm_ne_zero_iff.mpr (diskGreen_numerator_ne c z.1 w.1 ρ hρ z.2 w.2)
  have hm := ((hmem z).sub (hmem w)).aestronglyMeasurable.aemeasurable
  change variance (H z-H w) P = _
  rw [← covariance_self hm]
  change covariance (fun ω => H z ω-H w ω) (fun ω => H z ω-H w ω) P = _
  rw [covariance_fun_sub_fun_sub (hmem z) (hmem w) (hmem z) (hmem w)]
  rw [covariance_comm (H w) (H z)]
  simp_rw [hcov]
  rw [norm_diskGreen_numerator_self c z.1 ρ hρ z.2,
    norm_diskGreen_numerator_self c w.1 ρ hρ w.2]
  have he : 1+ρ^2*‖z.1-w.1‖^2/((ρ^2-‖z.1-c‖^2)*(ρ^2-‖w.1-c‖^2)) =
      ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖^2 /
        ((ρ^2-‖z.1-c‖^2)*(ρ^2-‖w.1-c‖^2)) := by
    rw [norm_diskGreen_numerator_sq]
    field_simp
  rw [he, Real.log_div (pow_ne_zero 2 hn) (mul_ne_zero hz.ne' hw.ne'),
    Real.log_pow, Real.log_mul hz.ne' hw.ne']
  ring

/-- Compact-disk harmonic increments have a quadratic distance bound with explicit geometry. -/
theorem poisson_gaussian_increment_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (R ρ a : ℝ)
    (hρ : 0 < ρ) (ha : 0 ≤ a) (haρ : a < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ)
    (hmem : ∀ z, MemLp (H z) 2 P)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖)
    (z w : {z : ℂ // z ∈ ball c ρ}) (hz : ‖z.1-c‖ ≤ a) (hw : ‖w.1-c‖ ≤ a) :
    variance (fun ω => H z ω-H w ω) P ≤ ρ^2/(ρ^2-a^2)^2*‖z.1-w.1‖^2 := by
  rw [poisson_gaussian_increment_variance P c R ρ hρ H hmem hcov]
  have hgap : 0 < ρ^2-a^2 := by nlinarith
  have hzg : ρ^2-a^2 ≤ ρ^2-‖z.1-c‖^2 := by nlinarith [norm_nonneg (z.1-c)]
  have hwg : ρ^2-a^2 ≤ ρ^2-‖w.1-c‖^2 := by nlinarith [norm_nonneg (w.1-c)]
  have hprod : (ρ^2-a^2)^2 ≤ (ρ^2-‖z.1-c‖^2)*(ρ^2-‖w.1-c‖^2) := by
    simpa only [pow_two] using mul_le_mul hzg hwg hgap.le (hgap.le.trans hzg)
  have hzgpos := hgap.trans_le hzg
  have hwgpos := hgap.trans_le hwg
  have hq : 0 ≤ ρ^2*‖z.1-w.1‖^2/((ρ^2-‖z.1-c‖^2)*(ρ^2-‖w.1-c‖^2)) := by positivity
  have hl := Real.log_le_sub_one_of_pos (by linarith :
    0 < 1+ρ^2*‖z.1-w.1‖^2/((ρ^2-‖z.1-c‖^2)*(ρ^2-‖w.1-c‖^2)))
  have hd := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖z.1-w.1‖))
    (sq_pos_of_pos hgap) hprod
  have he : ρ^2*‖z.1-w.1‖^2/(ρ^2-a^2)^2 =
      ρ^2/(ρ^2-a^2)^2*‖z.1-w.1‖^2 := by ring
  rw [he] at hd
  linarith

/-- Actual collar limits with centered measurable Gaussian coordinates and the harmonic covariance
formula of `DOZZ.exists_exteriorPinned_markov_uniform`. -/
theorem exists_exteriorPinned_poisson_gaussian_family_closed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) :
    ∃ H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ, IsGaussianProcess H P ∧
      (∀ z, Measurable (H z) ∧ MemLp (H z) 2 P ∧ (∫ ω, H z ω ∂P) = 0 ∧
        Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
          (canonicalPoissonCollarTest c z.1 ρ ε hρ hε z.2 k)-H z ω) 2 P) atTop (𝓝 0)) ∧
      (∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖) := by
  obtain ⟨H,hG,hH⟩ := exists_exteriorPinned_poisson_gaussian_family
    P X Xc hX hc c R ρ ε δ hR hρ hε hεδ hpin
  refine ⟨H,hG,hH,fun z w => ?_⟩
  exact exteriorPinned_poisson_rawLimit_covariance_closed P X Xc hX hc c z.1 w.1 R ρ ε δ
    hR hρ hε hεδ hpin z.2 w.2 (H z) (H w) (hH z).2.1 (hH w).2.1 (hH z).2.2.2 (hH w).2.2.2

/-- Covering exponents pull back exactly along an isometric embedding. -/
theorem hasBoundedCoveringNumber_of_isometry {T U : Type*}
    [EMetricSpace T] [PseudoEMetricSpace U] (f : T → U) (hf : Isometry f)
    (A : Set T) (C : ℝ≥0∞) (d : ℝ)
    (hA : HasBoundedCoveringNumber (f '' A) C d) : HasBoundedCoveringNumber A C d := by
  constructor
  · simpa only [hf.ediam_image] using hA.ediam_lt_top
  · intro ε hε
    have hε' : (ε : ℝ≥0∞) ≤ ediam (f '' A) := by rwa [hf.ediam_image]
    simpa only [hf.coveringNumber_image] using hA.coveringNumber_le ε hε'

/-- Gaussian harmonic coordinates restricted to a compact inner disk meet Kolmogorov's condition. -/
theorem poisson_gaussian_isKolmogorovProcess_on_closedBall
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℂ) (R ρ a : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (haρ : a < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ) (hG : IsGaussianProcess H P)
    (hmeas : ∀ z, Measurable (H z)) (hmem : ∀ z, MemLp (H z) 2 P)
    (hmean : ∀ z, (∫ ω, H z ω ∂P) = 0)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖) :
    ∃ M : ℝ≥0, IsKolmogorovProcess
      (fun z : {z : ℂ // z ∈ closedBall c a} =>
        H ⟨z.1,mem_ball_iff_norm.mpr ((mem_closedBall_iff_norm.mp z.2).trans_lt haρ)⟩)
      P 8 8 M := by
  let ι (z : {z : ℂ // z ∈ closedBall c a}) : {z : ℂ // z ∈ ball c ρ} :=
    ⟨z.1,mem_ball_iff_norm.mpr ((mem_closedBall_iff_norm.mp z.2).trans_lt haρ)⟩
  let C := ρ^2/(ρ^2-a^2)^2
  let A := ∫ x : ℝ, |x|^8 ∂gaussianReal 0 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hA : 0 ≤ A := integral_nonneg (fun x => pow_nonneg (abs_nonneg x) _)
  let M : ℝ≥0 := ⟨C^4*A,mul_nonneg (pow_nonneg hC _) hA⟩
  refine ⟨M,IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun z => hmeas (ι z)) ?_ (by norm_num) (by norm_num)⟩
  intro z w
  let U : Ω → ℝ := fun ω => H (ι z) ω-H (ι w) ω
  have hU : HasGaussianLaw U P := hG.hasGaussianLaw_fun_sub (s := ι z) (t := ι w)
  have hzero : (∫ ω, U ω ∂P) = 0 := by
    rw [integral_sub ((hmem (ι z)).integrable (by norm_num))
      ((hmem (ι w)).integrable (by norm_num)), hmean, hmean, sub_self]
  have hv : variance U P ≤ C*dist z w^2 := by
    simpa only [ι, Subtype.dist_eq, dist_eq_norm, C] using
      poisson_gaussian_increment_variance_le P c R ρ a hρ ha haρ H hmem hcov (ι z) (ι w)
        (mem_closedBall_iff_norm.mp z.2) (mem_closedBall_iff_norm.mp w.2)
  have hm : (∫ ω, |U ω|^8 ∂P) ≤ (C^4*A)*dist z w^8 := by
    have hh := hasGaussianLaw_integral_abs_pow_le U hU hzero 4 hv
    change _ ≤ (C*dist z w^2)^4*A at hh
    exact hh.trans_eq (by ring)
  have hi : Integrable (fun ω => |U ω|^8) P := by
    simpa only [Real.norm_eq_abs] using
      (hU.memLp (p := (8 : ℝ≥0∞)) (by norm_num)).integrable_norm_pow'
  have hlin := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (U ω)) 8))
  have he : (∫⁻ ω, edist (H (ι z) ω) (H (ι w) ω)^(8 : ℝ) ∂P) =
      ENNReal.ofReal (∫ ω, |U ω|^8 ∂P) := by
    rw [hlin]
    apply lintegral_congr
    intro ω
    rw [edist_dist, Real.dist_eq]
    simpa only [ENNReal.rpow_ofNat, U] using (ENNReal.ofReal_pow (abs_nonneg (U ω)) 8).symm
  rw [he]
  have hb := ENNReal.ofReal_le_ofReal hm
  rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hC _) hA),
    ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist z w) 8] at hb
  change _ ≤ ENNReal.ofReal (C^4*A)*ENNReal.ofReal (dist z w)^8 at hb
  rw [edist_dist, ENNReal.rpow_ofNat, ← ENNReal.ofReal_coe_nnreal (p := M)]
  exact hb

/-- On every compact inner disk the actual Gaussian Poisson family has a measurable
continuous modification, constructed from its original coordinates. -/
theorem exists_continuous_poisson_gaussian_on_closedBall
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℂ) (R ρ a : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (haρ : a < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ) (hG : IsGaussianProcess H P)
    (hmeas : ∀ z, Measurable (H z)) (hmem : ∀ z, MemLp (H z) 2 P)
    (hmean : ∀ z, (∫ ω, H z ω ∂P) = 0)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖) :
    ∃ Z : {z : ℂ // z ∈ closedBall c a} → Ω → ℝ,
      (∀ z, Measurable (Z z)) ∧ (∀ ω, Continuous (fun z => Z z ω)) ∧
      (∀ z, Z z =ᵐ[P] H ⟨z.1,
        mem_ball_iff_norm.mpr ((mem_closedBall_iff_norm.mp z.2).trans_lt haρ)⟩) := by
  obtain ⟨M,hM⟩ := poisson_gaussian_isKolmogorovProcess_on_closedBall
    P c R ρ a hρ ha.le haρ H hG hmeas hmem hmean hcov
  let aNN : ℝ≥0 := ⟨a,ha.le⟩
  have hcover := hasCoveringExponent_closedBall c aNN (by exact_mod_cast ha)
  have heq : (Subtype.val : {z : ℂ // z ∈ closedBall c a} → ℂ) '' univ =
      Metric.closedEBall c (aNN : ℝ≥0∞) := by
    rw [image_univ, Subtype.range_coe, Metric.closedEBall_coe]
    rfl
  rw [← heq, show Module.finrank ℝ ℂ = 2 by exact Complex.finrank_real_complex] at hcover
  have hsub := hasBoundedCoveringNumber_of_isometry
    (Subtype.val : {z : ℂ // z ∈ closedBall c a} → ℂ) isometry_subtype_coe univ _ _ hcover
  obtain ⟨Z,hZm,hZe,hZh,_⟩ := exists_modification_holder'' hsub isOpen_univ hM
    (by finiteness) (by norm_num) (by norm_num)
  refine ⟨Z,hZm,fun ω => ?_,fun z => hZe z (mem_univ z)⟩
  obtain ⟨C,hC⟩ := hZh (1/4) (by norm_num) (by norm_num) ω
  exact continuousOn_univ.mp (hC.continuousOn (by norm_num))



end DOZZ.Proofs
