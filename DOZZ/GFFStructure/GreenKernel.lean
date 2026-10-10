/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonCollar
public import DOZZ.GFF.LocalSchur

/-!
# Disk Green geometry and the exact restriction-energy bound

The literal zero extension `DOZZ.diskGreenKernel` is nonnegative and symmetric. Its regular
logarithmic numerator is smooth and harmonic on a neighborhood of the closed disk; its raw Green
ratio has zero logarithm on the boundary. The local diagonal-log estimate
`DOZZ.integrable_log_norm_sub_sq_on_pair_ball` proves square integrability on the disk product.
Actual test pairings are integrable, Fubini identifies the iterated covariance
`DOZZ.diskGreenCovariance`, and a Hilbert–Schmidt bound controls it by the disk L² restrictions.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal

namespace DOZZ.Proofs

/-- The disk Green numerator-distance identity. -/
theorem diskGreen_norm_identity (ρ : ℝ) (u v : ℂ) :
    ‖(ρ : ℂ)^2-u*star v‖^2 - ρ^2*‖u-v‖^2 =
      (ρ^2-‖u‖^2)*(ρ^2-‖v‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The regular Green numerator cannot vanish for two interior points. -/
theorem diskGreen_numerator_ne (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) :
    (ρ : ℂ)^2-(z-c)*star (w-c) ≠ 0 := by
  have hgapz := poissonNumerator_pos c z ρ hρ hz
  have hgapw := poissonNumerator_pos c w ρ hρ hw
  have hi := diskGreen_norm_identity ρ (z-c) (w-c)
  intro hzero
  rw [hzero, norm_zero, zero_pow (by norm_num)] at hi
  have hp := mul_pos hgapz hgapw
  have hs : 0 ≤ ρ^2*‖(z-c)-(w-c)‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- The disk Green ratio exceeds one off the diagonal inside the disk. -/
theorem one_lt_diskGreen_ratio (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (hzw : z ≠ w) :
    1 < ‖((ρ : ℂ)^2-(z-c)*star (w-c))/((ρ : ℂ)*(z-w))‖ := by
  have hi := diskGreen_norm_identity ρ (z-c) (w-c)
  have hgap := mul_pos (poissonNumerator_pos c z ρ hρ hz) (poissonNumerator_pos c w ρ hρ hw)
  have he : (z-c)-(w-c) = z-w := by ring
  rw [he] at hi
  have hn : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hnum : ρ*‖z-w‖ < ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ := by
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith only [hi, hgap])
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  exact (one_lt_div (mul_pos hρ hn)).mpr hnum

/-- The literal zero-extended disk Green kernel is nonnegative everywhere. -/
theorem diskGreenKernel_nonneg (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (z w : ℂ) :
    0 ≤ diskGreenKernel c ρ hρ z w := by
  unfold diskGreenKernel
  split_ifs with h
  · exact (Real.log_pos (one_lt_diskGreen_ratio c z w ρ hρ h.1 h.2.1 h.2.2)).le
  · exact le_rfl


/-- The regular numerator has a uniform upper bound on the disk product. -/
theorem diskGreen_numerator_norm_le (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) :
    ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ ≤ 2*ρ^2 := by
  have hz' : ‖z-c‖ ≤ ρ := (mem_ball_iff_norm.mp hz).le
  have hw' : ‖w-c‖ ≤ ρ := (mem_ball_iff_norm.mp hw).le
  calc
    _ ≤ ‖(ρ : ℂ)^2‖+‖(z-c)*star (w-c)‖ := norm_sub_le _ _
    _ = ρ^2+‖z-c‖*‖w-c‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, norm_mul, norm_star]
    _ ≤ 2*ρ^2 := by linarith only [mul_le_mul hz' hw' (norm_nonneg _) hρ.le]

/-- The disk Green ratio is controlled by the planar diagonal singularity. -/
theorem diskGreen_ratio_le (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (hzw : z ≠ w) :
    ‖((ρ : ℂ)^2-(z-c)*star (w-c))/((ρ : ℂ)*(z-w))‖ ≤ 2*ρ/‖z-w‖ := by
  have hd : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  calc
    _ ≤ (2*ρ^2)/(ρ*‖z-w‖) :=
      div_le_div_of_nonneg_right (diskGreen_numerator_norm_le c z w ρ hρ hz hw) (by positivity)
    _ = 2*ρ/‖z-w‖ := by field_simp [hρ.ne', hd.ne']

/-- The logarithmic Green kernel is bounded by an explicit diagonal logarithm. -/
theorem diskGreenKernel_le_log_sub (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (hzw : z ≠ w) :
    diskGreenKernel c ρ hρ z w ≤ Real.log (2*ρ)-Real.log ‖z-w‖ := by
  have hratio := one_lt_diskGreen_ratio c z w ρ hρ hz hw hzw
  have hlog := Real.log_le_log (zero_lt_one.trans hratio)
    (diskGreen_ratio_le c z w ρ hρ hz hw hzw)
  rw [Real.log_div (by positivity : 2*ρ ≠ 0)
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))] at hlog
  rw [diskGreenKernel, ite_eq_left ⟨hz, hw, hzw⟩]
  exact hlog

/-- The literal kernel has a global absolute-value majorant, also off the disk and diagonal. -/
theorem abs_diskGreenKernel_le (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (z w : ℂ) :
    |diskGreenKernel c ρ hρ z w| ≤ |Real.log (2*ρ)|+|Real.log ‖z-w‖| := by
  rw [abs_of_nonneg (diskGreenKernel_nonneg c ρ hρ z w)]
  by_cases h : z ∈ ball c ρ ∧ w ∈ ball c ρ ∧ z ≠ w
  · apply (diskGreenKernel_le_log_sub c z w ρ hρ h.1 h.2.1 h.2.2).trans
    linarith [le_abs_self (Real.log (2*ρ)), neg_le_abs (Real.log ‖z-w‖)]
  · simp only [diskGreenKernel, h, ↓reduceIte]
    positivity

/-- The squared kernel admits a square-integrable diagonal logarithm majorant. -/
theorem diskGreenKernel_sq_le (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (z w : ℂ) :
    (diskGreenKernel c ρ hρ z w)^2 ≤ 2*(Real.log (2*ρ))^2 + 2*(Real.log ‖z-w‖)^2 := by
  have h := abs_diskGreenKernel_le c ρ hρ z w
  have hn := diskGreenKernel_nonneg c ρ hρ z w
  rw [abs_of_nonneg hn] at h
  have ha := abs_nonneg (Real.log (2*ρ))
  have hb := abs_nonneg (Real.log ‖z-w‖)
  have hsq := pow_le_pow_left₀ hn h 2
  linarith only [hsq, sq_nonneg (|Real.log (2*ρ)|-|Real.log ‖z-w‖|), sq_abs (Real.log (2*ρ)),
    sq_abs (Real.log ‖z-w‖)]

/-- Joint measurability includes the zero extension and the chosen diagonal values. -/
theorem measurable_diskGreenKernel (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (fun p : ℂ × ℂ => diskGreenKernel c ρ hρ p.1 p.2) := by
  unfold diskGreenKernel
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact (isOpen_ball.measurableSet.preimage measurable_fst).inter
    ((isOpen_ball.measurableSet.preimage measurable_snd).inter
      (measurableSet_eq_fun measurable_fst measurable_snd).compl)

/-- The Green kernel is square integrable on every bounded planar product. -/
theorem integrable_diskGreenKernel_sq_on_pair_ball (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (R : ℝ) :
    IntegrableOn (fun p : ℂ × ℂ => (diskGreenKernel c ρ hρ p.1 p.2)^2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) (volume.prod volume) := by
  let B := ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have hBfin : μ B ≠ ∞ := by
    change ((volume : Measure ℂ).prod volume) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) ≠ ∞
    rw [Measure.prod_prod]
    have hb : volume (ball (0 : ℂ) R) ≠ ∞ := measure_ball_lt_top.ne
    exact ENNReal.mul_ne_top hb hb
  let _ := (isFiniteMeasure_restrict.mpr hBfin : IsFiniteMeasure (μ.restrict B))
  have hlog : Integrable (fun p : ℂ × ℂ => (Real.log ‖p.1-p.2‖)^2) (μ.restrict B) :=
    DOZZ.integrable_log_norm_sub_sq_on_pair_ball R
  have hmajor : Integrable (fun p : ℂ × ℂ =>
      2*(Real.log (2*ρ))^2+2*(Real.log ‖p.1-p.2‖)^2) (μ.restrict B) :=
    (integrable_const _).add (hlog.const_mul 2)
  apply hmajor.mono' ((measurable_diskGreenKernel c ρ hρ).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact diskGreenKernel_sq_le c ρ hρ p.1 p.2)


/-- The disk is contained in an explicit origin-centered ball. -/
theorem disk_subset_origin_ball (c : ℂ) (ρ : ℝ) :
    ball c ρ ⊆ ball (0 : ℂ) (‖c‖+ρ+1) := by
  intro z hz
  have hz' := mem_ball_iff_norm.mp hz
  have hn : ‖z‖ ≤ ‖z-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (z-c) c
  apply mem_ball.mpr
  rw [dist_zero_right]
  linarith

/-- Square integrability holds on the actual disk product. -/
theorem integrable_diskGreenKernel_sq_on_disk (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (fun p : ℂ × ℂ => (diskGreenKernel c ρ hρ p.1 p.2)^2)
      ((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))) := by
  rw [Measure.prod_restrict]
  exact (integrable_diskGreenKernel_sq_on_pair_ball c ρ hρ (‖c‖+ρ+1)).mono_set
    (Set.prod_mono (disk_subset_origin_ball c ρ) (disk_subset_origin_ball c ρ))

/-- The exact Green kernel belongs to the disk product L² space. -/
theorem memLp_diskGreenKernel_two (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    MemLp (fun p : ℂ × ℂ => diskGreenKernel c ρ hρ p.1 p.2) 2
      ((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))) := by
  apply DOZZ.memLp_two_of_integrable_norm_sq (measurable_diskGreenKernel c ρ hρ).aestronglyMeasurable
  simpa only [Real.norm_eq_abs, sq_abs] using integrable_diskGreenKernel_sq_on_disk c ρ hρ

/-- Tensor products of global tests belong to L² on the actual disk product. -/
theorem memLp_testFnTensor_two_on_disk (c : ℂ) (ρ : ℝ) (f g : TestFn) :
    MemLp (fun p : ℂ × ℂ => f p.1*g p.2) 2
      ((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))) := by
  have h := DOZZ.memLp_testFnTensor_two_on_ball (‖c‖+ρ+1) f g
  rw [Measure.prod_restrict] at h ⊢
  exact h.mono_measure (Measure.restrict_mono
    (Set.prod_mono (disk_subset_origin_ball c ρ) (disk_subset_origin_ball c ρ)) le_rfl)

/-- Weighted Green pairings of global tests are integrable on the disk product. -/
theorem integrable_diskGreenTestPair (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    Integrable (fun p : ℂ × ℂ => f p.1*diskGreenKernel c ρ hρ p.1 p.2*g p.2)
      ((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))) := by
  have h := (memLp_diskGreenKernel_two c ρ hρ).integrable_mul
    (memLp_testFnTensor_two_on_disk c ρ f g)
  convert h using 1
  funext p
  simp only [Pi.mul_apply]
  ring

/-- Fubini identifies the literal iterated Green covariance `DOZZ.diskGreenCovariance` with its
product pairing. -/
theorem diskGreenCovariance_eq_product (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    diskGreenCovariance c ρ hρ f g =
      ∫ p : ℂ × ℂ, f p.1*diskGreenKernel c ρ hρ p.1 p.2*g p.2
        ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))) := by
  rw [diskGreenCovariance, integral_prod _ (integrable_diskGreenTestPair c ρ hρ f g)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [← integral_const_mul]
    congr 1
    funext w
    ring)

/-- The test tensor's squared integral factors into the two disk L² norms. -/
theorem integral_sq_testFnTensor_on_disk (c : ℂ) (ρ : ℝ) (f g : TestFn) :
    (∫ p : ℂ × ℂ, ‖f p.1*g p.2‖^2
      ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ)))) =
        (∫ z in ball c ρ, ‖f z‖^2)*(∫ w in ball c ρ, ‖g w‖^2) := by
  simp_rw [norm_mul, mul_pow]
  exact integral_prod_mul (fun z : ℂ => ‖f z‖^2) (fun w : ℂ => ‖g w‖^2)

/-- The Hilbert–Schmidt bound is in the literal disk-restriction norms needed by Markov. -/
theorem abs_diskGreenCovariance_le_diskL2 (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    |diskGreenCovariance c ρ hρ f g| ≤
      (∫ p : ℂ × ℂ, ‖diskGreenKernel c ρ hρ p.1 p.2‖^2
        ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ)))) ^ (1/2 : ℝ) *
          ((∫ z in ball c ρ, ‖f z‖^2)*(∫ w in ball c ρ, ‖g w‖^2)) ^ (1/2 : ℝ) := by
  rw [diskGreenCovariance_eq_product]
  have h := DOZZ.abs_integral_mul_le_l2
    ((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ)))
    (memLp_diskGreenKernel_two c ρ hρ) (memLp_testFnTensor_two_on_disk c ρ f g)
  have he : (fun p : ℂ × ℂ => f p.1*diskGreenKernel c ρ hρ p.1 p.2*g p.2) =
      (fun p : ℂ × ℂ => diskGreenKernel c ρ hρ p.1 p.2*(f p.1*g p.2)) := by
    funext p
    ring
  rw [he]
  simpa only [integral_sq_testFnTensor_on_disk] using h


/-- The regular numerator stays nonzero on the closed disk when the pole is interior. -/
theorem diskGreen_numerator_ne_on_closedBall (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ closedBall c ρ) (hw : w ∈ ball c ρ) :
    (ρ : ℂ)^2-(z-c)*star (w-c) ≠ 0 := by
  have hz' : ‖z-c‖ ≤ ρ := mem_closedBall_iff_norm.mp hz
  have hw' : ‖w-c‖ < ρ := mem_ball_iff_norm.mp hw
  intro hzero
  have he : (ρ : ℂ)^2 = (z-c)*star (w-c) := sub_eq_zero.mp hzero
  have hn := congrArg norm he
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
    norm_mul, norm_star] at hn
  have hp := mul_le_mul_of_nonneg_right hz' (norm_nonneg (w-c))
  linarith only [hn, hp, mul_lt_mul_of_pos_left hw' hρ]

/-- The regular logarithmic numerator is harmonic on a neighborhood of the closed disk. -/
theorem harmonicOnNhd_diskGreen_regular (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hw : w ∈ ball c ρ) :
    InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) (closedBall c ρ) := by
  intro z hz
  exact AnalyticAt.harmonicAt_log_norm (by fun_prop)
    (diskGreen_numerator_ne_on_closedBall c z w ρ hρ hz hw)

/-- All derivatives of the regular logarithmic numerator exist on the closed disk. -/
theorem contDiffOn_diskGreen_regular (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hw : w ∈ ball c ρ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℂ => Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) (closedBall c ρ) := by
  intro z hz
  have hp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => (ρ : ℂ)^2-(z-c)*star (w-c)) z := by fun_prop
  exact ((hp.norm ℝ (diskGreen_numerator_ne_on_closedBall c z w ρ hρ hz hw)).log
    (norm_ne_zero_iff.mpr (diskGreen_numerator_ne_on_closedBall c z w ρ hρ hz hw))).contDiffWithinAt

/-- Poisson's formula reproduces the regular logarithmic potential in the interior. -/
theorem circleAverage_poisson_diskGreen_regular (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) :
    Real.circleAverage
      (poissonKernel c z • (fun v : ℂ => Real.log ‖(ρ : ℂ)^2-(v-c)*star (w-c)‖)) c ρ =
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ :=
  (harmonicOnNhd_diskGreen_regular c w ρ hρ hw).circleAverage_poissonKernel_smul hz

/-- Inside the disk, off its diagonal, the literal Green kernel splits into three logs. -/
theorem diskGreenKernel_eq_log_parts (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (hzw : z ≠ w) :
    diskGreenKernel c ρ hρ z w =
      Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖-Real.log ρ-Real.log ‖z-w‖ := by
  rw [diskGreenKernel, ite_eq_left ⟨hz, hw, hzw⟩, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  rw [Real.log_div (norm_ne_zero_iff.mpr (diskGreen_numerator_ne c z w ρ hρ hz hw))
    (mul_ne_zero hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))),
    Real.log_mul hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))]
  ring

/-- The raw Green ratio equals one on the boundary, with an interior pole. -/
theorem diskGreen_ratio_eq_one_on_sphere (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ sphere c ρ) (hw : w ∈ ball c ρ) :
    ‖((ρ : ℂ)^2-(z-c)*star (w-c))/((ρ : ℂ)*(z-w))‖ = 1 := by
  have hz' : ‖z-c‖ = ρ := mem_sphere_iff_norm.mp hz
  have hw' : ‖w-c‖ < ρ := mem_ball_iff_norm.mp hw
  have hzw : z ≠ w := by intro h; subst w; exact hw'.ne hz'
  have hn : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hi := diskGreen_norm_identity ρ (z-c) (w-c)
  rw [hz', sub_self, zero_mul, show (z-c)-(w-c) = z-w by ring] at hi
  have hnum : ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ = ρ*‖z-w‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_pos hρ hn).le).mp
    calc
      _ = ρ^2*‖z-w‖^2 := sub_eq_zero.mp hi
      _ = (ρ*‖z-w‖)^2 := by ring
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
    hnum, div_self (mul_ne_zero hρ.ne' hn.ne')]


/-- A scalar Green covariance obeys the disk L² bound without a tensor square root. -/
theorem abs_diskGreenCovariance_self_le_diskL2 (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f : TestFn) :
    |diskGreenCovariance c ρ hρ f f| ≤
      (∫ p : ℂ × ℂ, ‖diskGreenKernel c ρ hρ p.1 p.2‖^2
        ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ)))) ^ (1/2 : ℝ) *
          (∫ z in ball c ρ, ‖f z‖^2) := by
  have h := abs_diskGreenCovariance_le_diskL2 c ρ hρ f f
  have ha : 0 ≤ ∫ z in ball c ρ, ‖f z‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have he : ((∫ z in ball c ρ, ‖f z‖^2)*(∫ z in ball c ρ, ‖f z‖^2)) ^ (1/2 : ℝ) =
      (∫ z in ball c ρ, ‖f z‖^2) := by
    rw [← Real.sqrt_eq_rpow, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  rwa [he] at h


/-- Outer Green-potential pairings of tests are integrable. -/
theorem integrable_diskGreenPotential_test (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    Integrable (fun z => f z*(∫ w in ball c ρ, diskGreenKernel c ρ hρ z w*g w))
      (volume.restrict (ball c ρ)) := by
  have h := (integrable_diskGreenTestPair c ρ hρ f g).integral_prod_left
  convert h using 1
  funext z
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

/-- The literal Green covariance is additive in its first test. -/
theorem diskGreenCovariance_add_left (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g h : TestFn) :
    diskGreenCovariance c ρ hρ (f+g) h =
      diskGreenCovariance c ρ hρ f h+diskGreenCovariance c ρ hρ g h := by
  simp only [diskGreenCovariance, FunLike.coe_add, Pi.add_apply, add_mul]
  exact integral_add (integrable_diskGreenPotential_test c ρ hρ f h)
    (integrable_diskGreenPotential_test c ρ hρ g h)

/-- The literal Green covariance is real-linear in its first test. -/
theorem diskGreenCovariance_smul_left (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (a : ℝ) (f g : TestFn) :
    diskGreenCovariance c ρ hρ (a • f) g = a*diskGreenCovariance c ρ hρ f g := by
  simp only [diskGreenCovariance, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

/-- Global tests vanishing on the disk have zero Green covariance. -/
theorem diskGreenCovariance_eq_zero_of_eqOn_zero (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (f g : TestFn) (hf : EqOn f 0 (ball c ρ)) : diskGreenCovariance c ρ hρ f g = 0 := by
  rw [diskGreenCovariance]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  rw [hf hz]
  exact zero_mul _


/-- Symmetry holds for the literal zero-extended Green kernel. -/
theorem diskGreenKernel_symm (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (z w : ℂ) :
    diskGreenKernel c ρ hρ z w = diskGreenKernel c ρ hρ w z := by
  by_cases h : z ∈ ball c ρ ∧ w ∈ ball c ρ ∧ z ≠ w
  · have h' : w ∈ ball c ρ ∧ z ∈ ball c ρ ∧ w ≠ z := ⟨h.2.1, h.1, h.2.2.symm⟩
    rw [diskGreenKernel, diskGreenKernel, ite_eq_left h, ite_eq_left h', norm_div, norm_div,
      norm_mul, norm_mul, norm_sub_rev w z]
    have he : (ρ : ℂ)^2-(w-c)*star (z-c) =
        star ((ρ : ℂ)^2-(z-c)*star (w-c)) := by
      simp only [Complex.star_def, map_sub, map_pow, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    rw [he, norm_star]
  · have h' : ¬ (w ∈ ball c ρ ∧ z ∈ ball c ρ ∧ w ≠ z) := by
      rintro ⟨hw, hz, hzw⟩
      exact h ⟨hz, hw, hzw.symm⟩
    simp only [diskGreenKernel, h, h', ↓reduceIte]


/-- Fubini and kernel symmetry give symmetry of the literal covariance
`DOZZ.diskGreenCovariance`. -/
theorem diskGreenCovariance_symm (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    diskGreenCovariance c ρ hρ f g = diskGreenCovariance c ρ hρ g f := by
  rw [diskGreenCovariance_eq_product, diskGreenCovariance_eq_product]
  calc
    _ = ∫ p : ℂ × ℂ, g p.2*diskGreenKernel c ρ hρ p.2 p.1*f p.1
        ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by
        dsimp only
        rw [diskGreenKernel_symm c ρ hρ p.1 p.2]
        ring)
    _ = _ := integral_prod_swap (μ := volume.restrict (ball c ρ))
      (ν := volume.restrict (ball c ρ))
      (fun p : ℂ × ℂ => g p.1*diskGreenKernel c ρ hρ p.1 p.2*f p.2)


end DOZZ.Proofs
