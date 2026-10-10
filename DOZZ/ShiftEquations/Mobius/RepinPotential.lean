/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.AffineKernel
import DOZZ.GFFStructure.CirclePotential
import DOZZ.GMC.CirclePotential

/-!
# The potential of the repinning circle

For an affine map `ψ(y) = a y + b`, the field `X ∘ ψ` is repinned by its average `L` over the image
`ψ(S¹)` of the unit circle, the circle of center `b` and radius `|a|`. The covariance of the field
at `x` with `L` is the circle potential
`c(x) = ∫ G(x, u) dσ_{b,|a|}(u)`.
Through `ψ` it is the affine defect plus its unit-circle average: `c(ψ y) = d(y) + κ`, and the
variance of `L` is `2κ`. The potential is Lipschitz and bounded, so its circle averages converge to
it uniformly as the circles shrink.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace DOZZ.Proofs

/-- The potential `c(x) = ∫ G(x,u) dσ_{b,|a|}(u)` of the repinning circle. -/
noncomputable def repinPotential (a b : ℂ) (x : ℂ) : ℝ :=
  ∫ u, gffKernel x u ∂circleMeasure b (-Real.log ‖a‖)

/-- The unit-circle average `κ` of the affine defect. -/
noncomputable def repinKappa (a b : ℂ) : ℝ :=
  ∫ u, affineDefect a b u ∂circleMeasure 0 0

/-- The repinning circle is the affine image of the unit circle. -/
theorem circleMeasure_repin (a b : ℂ) (ha : a ≠ 0) :
    circleMeasure b (-Real.log ‖a‖) = (circleMeasure 0 0).map (fun u => a * u + b) := by
  rw [circleMeasure_map_affine a b ha 0 0]
  simp

/-- The unit circle carries no atoms. -/
theorem circleMeasure_zero_singleton (y : ℂ) : circleMeasure 0 0 {y} = 0 := by
  have hcount : (circleMap 0 (Real.exp (-0)) ⁻¹' {y}).Countable := by
    by_cases hne : (circleMap 0 (Real.exp (-0)) ⁻¹' {y}).Nonempty
    · obtain ⟨θ₀, hθ₀⟩ := hne
      refine (Set.countable_range fun n : ℤ => θ₀ + n * (2 * Real.pi)).mono ?_
      intro θ hθ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, neg_zero, Real.exp_zero,
        circleMap_zero, Complex.ofReal_one, one_mul] at hθ hθ₀
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (hθ.trans hθ₀.symm)
      refine ⟨n, ?_⟩
      have := congrArg Complex.im hn
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.intCast_re,
        Complex.intCast_im, zero_mul, add_zero, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat] at this
      linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.countable_empty
  rw [circleMeasure, Measure.smul_apply, Measure.map_apply (measurable_circleMap _ _)
    (measurableSet_singleton y), Measure.restrict_apply' measurableSet_Ioc,
    measure_mono_null Set.inter_subset_left (hcount.measure_zero _), smul_zero]

/-- The unit circle measure is a probability measure. -/
theorem circleMeasure_zero_zero_isProbability : IsProbabilityMeasure (circleMeasure 0 0) :=
  circleMeasure_isProbability 0 0

/-- Almost every point of the unit circle differs from a given point. -/
theorem ae_ne_circleMeasure_zero (y : ℂ) : ∀ᵐ u ∂circleMeasure 0 0, u ≠ y := by
  rw [ae_iff]
  simpa only [ne_eq, not_not, Set.ofPred_eq_eq_singleton] using circleMeasure_zero_singleton y

/-- The affine defect is integrable on every circle. -/
theorem integrable_affineDefect_circleMeasure (a b : ℂ) (ha : a ≠ 0) (x : ℂ) (r : ℝ) :
    Integrable (affineDefect a b) (circleMeasure x r) := by
  have _ := circleMeasure_isProbability x r
  obtain ⟨C, hC⟩ := exists_abs_affineDefect_le a b ha
  exact Integrable.of_bound (continuous_affineDefect a b).aestronglyMeasurable C
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)

/-- **The repinning potential through the affine map** is the defect plus its unit average. -/
theorem repinPotential_affine (a b : ℂ) (ha : a ≠ 0) (y : ℂ) :
    repinPotential a b (a * y + b) = affineDefect a b y + repinKappa a b := by
  have _ := circleMeasure_zero_zero_isProbability
  have hmeas : Measurable (fun u => gffKernel (a * y + b) u) :=
    CirclePotential.measurable_gffKernel _
  unfold repinPotential
  rw [circleMeasure_repin a b ha, integral_map (by fun_prop) hmeas.aestronglyMeasurable]
  have hae : (fun u => gffKernel (a * y + b) (a * u + b)) =ᵐ[circleMeasure 0 0]
      fun u => gffKernel y u + affineDefect a b y + affineDefect a b u := by
    filter_upwards [ae_ne_circleMeasure_zero y] with u hu
    exact gffKernel_affine a b ha (Ne.symm hu)
  have hG : Integrable (fun u => gffKernel y u) (circleMeasure 0 0) :=
    integrable_gffKernel_circleMeasure 0 y 0
  have hGc : Integrable (fun u => gffKernel y u + affineDefect a b y) (circleMeasure 0 0) :=
    hG.add (integrable_const _)
  rw [integral_congr_ae hae, integral_add hGc (integrable_affineDefect_circleMeasure a b ha 0 0),
    integral_add hG (integrable_const _), integral_gffKernel_circleMeasure_unit, integral_const,
    probReal_univ, one_smul, zero_add]
  rfl

/-- The constant part of the repinning potential. -/
noncomputable def repinConst (a b : ℂ) : ℝ :=
  ∫ w, Real.log (normPlus w) ∂circleMeasure b (-Real.log ‖a‖)

/-- Closed form of the repinning potential. -/
theorem repinPotential_eq (a b : ℂ) (ha : a ≠ 0) (x : ℂ) :
    repinPotential a b x =
      -Real.log (max ‖a‖ ‖b - x‖) + Real.log (normPlus x) + repinConst a b := by
  unfold repinPotential repinConst
  rw [integral_gffKernel_circleMeasure b x (-Real.log ‖a‖), neg_neg,
    Real.exp_log (norm_pos_iff.mpr ha)]

/-- `log ∘ max m` is `1/m`-Lipschitz. -/
theorem abs_log_max_sub_log_max_le {m p q : ℝ} (hm : 0 < m) :
    |Real.log (max m p) - Real.log (max m q)| ≤ |p - q| / m := by
  have key : ∀ p q : ℝ, max m q ≤ max m p →
      |Real.log (max m p) - Real.log (max m q)| ≤ |p - q| / m := by
    intro p q hle
    have ht : 0 < max m q := lt_of_lt_of_le hm (le_max_left _ _)
    have hs : 0 < max m p := lt_of_lt_of_le ht hle
    have hnn : 0 ≤ Real.log (max m p) - Real.log (max m q) :=
      sub_nonneg.mpr (Real.log_le_log ht hle)
    rw [abs_of_nonneg hnn, ← Real.log_div hs.ne' ht.ne']
    have h1 : Real.log (max m p / max m q) ≤ max m p / max m q - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hs ht)
    have h2 : max m p / max m q - 1 = (max m p - max m q) / max m q := by
      field_simp
    have h3 : max m p - max m q ≤ |p - q| := by
      have := abs_max_sub_max_le_abs p q m
      rw [max_comm p m, max_comm q m] at this
      exact (le_abs_self _).trans this
    calc Real.log (max m p / max m q) ≤ (max m p - max m q) / max m q := h1.trans h2.le
      _ ≤ |p - q| / max m q := div_le_div_of_nonneg_right h3 ht.le
      _ ≤ |p - q| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm (le_max_left _ _)
  rcases le_total (max m q) (max m p) with h | h
  · exact key p q h
  · rw [abs_sub_comm, abs_sub_comm p q]
    exact key q p h

/-- The repinning potential is Lipschitz. -/
theorem abs_repinPotential_sub_le (a b : ℂ) (ha : a ≠ 0) (x x' : ℂ) :
    |repinPotential a b x - repinPotential a b x'| ≤ (‖a‖⁻¹ + 1) * ‖x - x'‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [repinPotential_eq a b ha, repinPotential_eq a b ha]
  have h1 := abs_log_max_sub_log_max_le (p := ‖b - x'‖) (q := ‖b - x‖) hapos
  have h2 := abs_log_max_sub_log_max_le (p := ‖x‖) (q := ‖x'‖) one_pos
  have h3 : |‖b - x'‖ - ‖b - x‖| ≤ ‖x - x'‖ := by
    have := abs_norm_sub_norm_le (b - x') (b - x)
    rwa [show b - x' - (b - x) = x - x' by ring] at this
  have h4 : |‖x‖ - ‖x'‖| ≤ ‖x - x'‖ := abs_norm_sub_norm_le x x'
  unfold normPlus
  calc |(-Real.log (max ‖a‖ ‖b - x‖) + Real.log (max 1 ‖x‖) + repinConst a b) -
          (-Real.log (max ‖a‖ ‖b - x'‖) + Real.log (max 1 ‖x'‖) + repinConst a b)|
      = |(Real.log (max ‖a‖ ‖b - x'‖) - Real.log (max ‖a‖ ‖b - x‖)) +
          (Real.log (max 1 ‖x‖) - Real.log (max 1 ‖x'‖))| := by ring_nf
    _ ≤ |Real.log (max ‖a‖ ‖b - x'‖) - Real.log (max ‖a‖ ‖b - x‖)| +
          |Real.log (max 1 ‖x‖) - Real.log (max 1 ‖x'‖)| := abs_add_le _ _
    _ ≤ |‖b - x'‖ - ‖b - x‖| / ‖a‖ + |‖x‖ - ‖x'‖| / 1 := add_le_add h1 h2
    _ ≤ ‖x - x'‖ / ‖a‖ + ‖x - x'‖ / 1 :=
        add_le_add (div_le_div_of_nonneg_right h3 hapos.le)
          (div_le_div_of_nonneg_right h4 one_pos.le)
    _ = (‖a‖⁻¹ + 1) * ‖x - x'‖ := by field_simp

/-- The repinning potential is continuous. -/
theorem continuous_repinPotential (a b : ℂ) (ha : a ≠ 0) : Continuous (repinPotential a b) := by
  have hK : 0 ≤ ‖a‖⁻¹ + 1 := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := ⟨‖a‖⁻¹ + 1, hK⟩) fun x x' => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact abs_repinPotential_sub_le a b ha x x'

/-- The repinning potential is bounded. -/
theorem exists_abs_repinPotential_le (a b : ℂ) (ha : a ≠ 0) :
    ∃ C : ℝ, ∀ x : ℂ, |repinPotential a b x| ≤ C := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set K₁ : ℝ := (1 + ‖b‖) / ‖a‖ + 1 with hK₁
  set K₂ : ℝ := ‖a‖ + ‖b‖ + 1 with hK₂
  have hK₁1 : 1 ≤ K₁ := by
    have : 0 ≤ (1 + ‖b‖) / ‖a‖ := by positivity
    rw [hK₁]
    linarith
  have hK₂1 : 1 ≤ K₂ := by
    have := norm_nonneg b
    have := norm_nonneg a
    rw [hK₂]
    linarith
  refine ⟨Real.log K₁ + Real.log K₂ + |repinConst a b|, fun x => ?_⟩
  rw [repinPotential_eq a b ha]
  set A := max ‖a‖ ‖b - x‖ with hA
  set N := normPlus x with hN
  have hApos : 0 < A := lt_of_lt_of_le hapos (le_max_left _ _)
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hNA : N ≤ K₁ * A := by
    have hx : ‖x‖ ≤ ‖b - x‖ + ‖b‖ := by
      have := norm_sub_le b (b - x)
      rw [show b - (b - x) = x by ring] at this
      linarith
    have h1 : 1 + ‖b‖ ≤ (1 + ‖b‖) / ‖a‖ * A := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hapos]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have h2 : ‖b - x‖ ≤ A := le_max_right _ _
    rw [hN]
    unfold normPlus
    refine max_le ?_ ?_
    · nlinarith [norm_nonneg b, norm_nonneg (b - x)]
    · nlinarith [norm_nonneg b, norm_nonneg (b - x)]
  have hAN : A ≤ K₂ * N := by
    have h1 : ‖a‖ ≤ (‖a‖ + ‖b‖ + 1) * normPlus x := by
      have : 1 ≤ normPlus x := le_max_left _ _
      nlinarith [norm_nonneg a, norm_nonneg b]
    have h2 : ‖b - x‖ ≤ (‖a‖ + ‖b‖ + 1) * normPlus x := by
      have hx : ‖x‖ ≤ normPlus x := le_max_right _ _
      have h1x : 1 ≤ normPlus x := le_max_left _ _
      have := norm_sub_le b x
      nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg x]
    exact max_le h1 h2
  have hl1 : Real.log N - Real.log A ≤ Real.log K₁ := by
    rw [← Real.log_div hNpos.ne' hApos.ne']
    exact Real.log_le_log (div_pos hNpos hApos) ((div_le_iff₀ hApos).mpr hNA)
  have hl2 : Real.log A - Real.log N ≤ Real.log K₂ := by
    rw [← Real.log_div hApos.ne' hNpos.ne']
    exact Real.log_le_log (div_pos hApos hNpos) ((div_le_iff₀ hNpos).mpr hAN)
  have hK₁0 : 0 ≤ Real.log K₁ := Real.log_nonneg hK₁1
  have hK₂0 : 0 ≤ Real.log K₂ := Real.log_nonneg hK₂1
  calc |-Real.log A + Real.log N + repinConst a b|
      ≤ |Real.log N - Real.log A| + |repinConst a b| := by
        rw [show -Real.log A + Real.log N + repinConst a b =
          (Real.log N - Real.log A) + repinConst a b by ring]
        exact abs_add_le _ _
    _ ≤ Real.log K₁ + Real.log K₂ + |repinConst a b| := by
        gcongr
        rw [abs_le]
        constructor <;> linarith

/-- Circle averages of a Lipschitz function are uniformly close to it. -/
theorem abs_integral_circleMeasure_sub_le {g : ℂ → ℝ} {K : ℝ}
    (hg : ∀ u v, |g u - g v| ≤ K * ‖u - v‖) (hcont : Continuous g) (x : ℂ) (r : ℝ) :
    |(∫ u, g u ∂circleMeasure x r) - g x| ≤ K * Real.exp (-r) := by
  have _ := circleMeasure_isProbability x r
  have hint : Integrable g (circleMeasure x r) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable (|g x| + K * Real.exp (-r)) ?_
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with u hu
    rw [Real.norm_eq_abs]
    have := hg u x
    rw [hu] at this
    calc |g u| = |g x + (g u - g x)| := by ring_nf
      _ ≤ |g x| + |g u - g x| := abs_add_le _ _
      _ ≤ |g x| + K * Real.exp (-r) := by linarith
  rw [show (∫ u, g u ∂circleMeasure x r) - g x = ∫ u, (g u - g x) ∂circleMeasure x r by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]]
  calc |∫ u, (g u - g x) ∂circleMeasure x r|
      ≤ ∫ u, |g u - g x| ∂circleMeasure x r := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Real.norm_eq_abs])
    _ ≤ ∫ _u, K * Real.exp (-r) ∂circleMeasure x r := by
        refine integral_mono_ae (hint.sub (integrable_const _)).abs (integrable_const _) ?_
        filter_upwards [ae_norm_sub_center_circleMeasure x r] with u hu
        have := hg u x
        rwa [hu] at this
    _ = K * Real.exp (-r) := by rw [integral_const, probReal_univ, one_smul]

/-- **Uniform convergence** of the circle averages of the repinning potential. -/
theorem tendstoUniformly_repinPotential (a b : ℂ) (ha : a ≠ 0) :
    TendstoUniformly (fun (r : ℝ) (x : ℂ) => ∫ u, repinPotential a b u ∂circleMeasure x r)
      (repinPotential a b) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun r : ℝ => (‖a‖⁻¹ + 1) * Real.exp (-r)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (‖a‖⁻¹ + 1))
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with r hr x
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_integral_circleMeasure_sub_le
    (abs_repinPotential_sub_le a b ha) (continuous_repinPotential a b ha) x r) hr


/-- **The self-energy of the repinning circle** is `2κ`. -/
theorem repin_selfEnergy (a b : ℂ) (ha : a ≠ 0) :
    ∫ u, ∫ v, gffKernel u v ∂circleMeasure b (-Real.log ‖a‖) ∂circleMeasure b (-Real.log ‖a‖) =
      2 * repinKappa a b := by
  have _ := circleMeasure_zero_zero_isProbability
  change ∫ u, repinPotential a b u ∂circleMeasure b (-Real.log ‖a‖) = _
  have hmeas : Measurable (repinPotential a b) := (continuous_repinPotential a b ha).measurable
  rw [circleMeasure_repin a b ha, integral_map (by fun_prop) hmeas.aestronglyMeasurable]
  simp_rw [repinPotential_affine a b ha]
  rw [integral_add (integrable_affineDefect_circleMeasure a b ha 0 0) (integrable_const _),
    integral_const, probReal_univ, one_smul]
  unfold repinKappa
  ring

end DOZZ.Proofs

end
