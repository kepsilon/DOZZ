/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.GreenKernel

/-!
# Uniform angular energy limits for Poisson collars

The radial distance identity gives one integrable unit-circle logarithmic majorant.
Dominated convergence proves the weighted boundary-energy limit. The integral of the
absolute log error controls every bounded angular weight, so Poisson log energies converge
uniformly on compact inner disks. The Poisson angular weights are measurable, integrable
and have mass one. The conversion of literal Cartesian collars to these angular energies
is a separate step.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal InnerProductSpace

namespace DOZZ.Proofs

/-- Circle measure has no atoms: every angular fiber is countable. -/
theorem circleMeasure_noAtoms (x : ℂ) (r : ℝ) : NullSingletonClass (circleMeasure x r) := by
  constructor
  intro z
  rw [circleMeasure, Measure.smul_apply, Measure.map_apply
    (measurable_circleMap x (Real.exp (-r))) (measurableSet_singleton z)]
  have h : (circleMap x (Real.exp (-r)) ⁻¹' {z}).Countable :=
    (Set.countable_singleton z).preimage_circleMap x (Real.exp_ne_zero _)
  rw [h.measure_zero, smul_zero]

/-- Radial separation identity on a unit sphere, in any real Hilbert space. -/
theorem norm_smul_sub_sq_of_norm_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (r s : ℝ) :
    ‖r • u-s • v‖^2 = (r-s)^2+r*s*‖u-v‖^2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, hu, hv, one_pow, mul_one]
  ring

/-- Every collar distance dominates the boundary distance times the inner radius. -/
theorem norm_smul_sub_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ρ r s : ℝ)
    (hρ : 0 < ρ) (hr : ρ ≤ r) (hs : ρ ≤ s) :
    ρ*‖u-v‖ ≤ ‖r • u-s • v‖ := by
  have hi := norm_smul_sub_sq_of_norm_one u v hu hv r s
  have hmul : ρ^2 ≤ r*s := by nlinarith
  have hsquare : (ρ*‖u-v‖)^2 ≤ ‖r • u-s • v‖^2 := by
    have h := mul_le_mul_of_nonneg_right hmul (sq_nonneg ‖u-v‖)
    nlinarith [sq_nonneg (r-s)]
  exact (sq_le_sq₀ (mul_nonneg hρ.le (norm_nonneg _)) (norm_nonneg _)).mp hsquare


/-- Radial collar logarithms admit an angular majorant uniform over both radii. -/
theorem abs_log_norm_smul_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) (ρ B r s : ℝ)
    (hρ : 0 < ρ) (hr : ρ ≤ r) (hs : ρ ≤ s) (hrB : r ≤ B) (hsB : s ≤ B) :
    |Real.log ‖r • u-s • v‖| ≤
      |Real.log (2*B)|+|Real.log ρ|+|Real.log ‖u-v‖| := by
  have hd : 0 < ‖u-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  have hlow := norm_smul_sub_lower u v hu hv ρ r s hρ hr hs
  have hn : 0 < ‖r • u-s • v‖ := (mul_pos hρ hd).trans_le hlow
  have hB : 0 < B := hρ.trans_le (hr.trans hrB)
  have hup : ‖r • u-s • v‖ ≤ 2*B := by
    calc
      _ ≤ ‖r • u‖+‖s • v‖ := norm_sub_le _ _
      _ = r+s := by
        rw [norm_smul, norm_smul, hu, hv, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (hρ.trans_le hr), abs_of_pos (hρ.trans_le hs)]
      _ ≤ 2*B := by linarith
  have hloglow := Real.log_le_log (mul_pos hρ hd) hlow
  rw [Real.log_mul hρ.ne' hd.ne'] at hloglow
  have hlogup := Real.log_le_log hn hup
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs (Real.log ρ), neg_le_abs (Real.log ‖u-v‖), abs_nonneg (Real.log (2*B))]
  · linarith [le_abs_self (Real.log (2*B)), abs_nonneg (Real.log ρ), abs_nonneg (Real.log ‖u-v‖)]

/-- The unit-circle angular logarithm is product integrable, including its diagonal convention. -/
theorem integrable_unitCircle_log_distance :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      ((circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  let μ := circleMeasure (0 : ℂ) 0
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  have hm : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all μ (fun u => by simpa only [norm_sub_rev u] using integrable_log_norm_sub_circleMeasure 0 u 0), ?_⟩
  have hmeas : AEStronglyMeasurable (fun u => ∫ v, ‖Real.log ‖u-v‖‖ ∂μ) μ :=
    hm.norm.aestronglyMeasurable.integral_prod_right'
  apply (integrable_const (2*Real.log 2 : ℝ)).mono' hmeas
  filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
  have hn : ‖u‖ = 1 := by simpa only [sub_zero, neg_zero, Real.exp_zero] using hu
  have h := integral_abs_log_circle_le 0 u 0 1 hn.le
  simp only [Real.norm_eq_abs, norm_zero, neg_zero, Real.exp_zero, one_add_one_eq_two,
    max_eq_right (by norm_num : (1 : ℝ) ≤ 2), add_zero] at h ⊢
  rw [abs_of_nonneg (integral_nonneg (fun v => abs_nonneg (Real.log ‖u-v‖)))]
  exact h

/-- The circle product diagonal is null. -/
theorem ae_unitCircle_pair_ne :
    ∀ᵐ p : ℂ × ℂ ∂(circleMeasure 0 0).prod (circleMeasure 0 0), p.1 ≠ p.2 := by
  let _ := circleMeasure_noAtoms (0 : ℂ) 0
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_fst measurable_snd).compl : MeasurableSet {p : ℂ × ℂ | p.1 ≠ p.2})).mpr
  apply ae_of_all
  intro u
  filter_upwards [(circleMeasure 0 0).ae_ne u] with v hv
  exact hv.symm


/-- Unit-circle pairs satisfy the simultaneous norm and off-diagonal conditions. -/
theorem ae_unitCircle_pair_spec :
    ∀ᵐ p : ℂ × ℂ ∂(circleMeasure 0 0).prod (circleMeasure 0 0),
      ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ p.1 ≠ p.2 := by
  let μ := circleMeasure (0 : ℂ) 0
  have hnorm : ∀ᵐ u ∂μ, ‖u‖ = 1 := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
    simpa only [sub_zero, neg_zero, Real.exp_zero] using hu
  have hpair : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 := by
    apply (Measure.ae_prod_iff_ae_ae (((measurableSet_eq_fun measurable_fst.norm measurable_const).inter (measurableSet_eq_fun measurable_snd.norm measurable_const)) : MeasurableSet {p : ℂ × ℂ | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1})).mpr
    filter_upwards [hnorm] with u hu
    exact hnorm.mono (fun v hv => ⟨hu, hv⟩)
  filter_upwards [hpair, ae_unitCircle_pair_ne] with p hn hne
  exact ⟨hn.1, hn.2, hne⟩

/-- A bounded angular weight preserves collar log-integrability and supplies a common majorant. -/
theorem integrable_weighted_radial_circleLog (F : ℂ × ℂ → ℝ) (hF : Measurable F)
    (M ρ B r s : ℝ) (hM : 0 ≤ M) (hρ : 0 < ρ) (hr : ρ ≤ r) (hs : ρ ≤ s)
    (hrB : r ≤ B) (hsB : s ≤ B)
    (hbound : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |F (u,v)| ≤ M) :
    Integrable (fun p : ℂ × ℂ => F p*Real.log ‖r • p.1-s • p.2‖)
      ((circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  have hmajor : Integrable (fun p : ℂ × ℂ =>
      M*(|Real.log (2*B)|+|Real.log ρ|+|Real.log ‖p.1-p.2‖|))
        ((circleMeasure 0 0).prod (circleMeasure 0 0)) :=
    ((integrable_const _).add integrable_unitCircle_log_distance.norm).const_mul M
  apply hmajor.mono' (hF.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards [ae_unitCircle_pair_spec] with p hp
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hbound p.1 p.2 hp.1 hp.2.1)
    (abs_log_norm_smul_sub_le p.1 p.2 hp.1 hp.2.1 hp.2.2 ρ B r s hρ hr hs hrB hsB)
    (abs_nonneg _) hM


/-- The angular absolute log error vanishes within any fixed radial collar square.
This removes the angular weight from the domination and later gives uniform parameter limits. -/
theorem tendsto_radial_circleLog_error (ρ B : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun a : ℝ × ℝ => ∫ p : ℂ × ℂ,
      |Real.log ‖a.1 • p.1-a.2 • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
      (𝓝[Set.Icc ρ B ×ˢ Set.Icc ρ B] (ρ,ρ)) (𝓝 0) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  let bound (p : ℂ × ℂ) :=
    2*(|Real.log (2*B)|+|Real.log ρ|+|Real.log ‖p.1-p.2‖|)
  have hmajor : Integrable bound ((circleMeasure 0 0).prod (circleMeasure 0 0)) :=
    ((integrable_const _).add integrable_unitCircle_log_distance.norm).const_mul 2
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (circleMeasure 0 0).prod (circleMeasure 0 0))
    (f := fun _ : ℂ × ℂ => (0 : ℝ)) bound
    (Filter.Eventually.of_forall (fun a : ℝ × ℝ => by
      exact (show Measurable (fun p : ℂ × ℂ =>
        |Real.log ‖a.1 • p.1-a.2 • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|) by
          fun_prop).aestronglyMeasurable))
    (l := 𝓝[Set.Icc ρ B ×ˢ Set.Icc ρ B] (ρ,ρ))
  have hbound : ∀ᶠ a : ℝ × ℝ in 𝓝[Set.Icc ρ B ×ˢ Set.Icc ρ B] (ρ,ρ),
      ∀ᵐ p : ℂ × ℂ ∂(circleMeasure 0 0).prod (circleMeasure 0 0),
        ‖|Real.log ‖a.1 • p.1-a.2 • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|‖ ≤ bound p := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards [ae_unitCircle_pair_spec] with p hp
    have hfirst := abs_log_norm_smul_sub_le p.1 p.2 hp.1 hp.2.1 hp.2.2
      ρ B a.1 a.2 hρ ha.1.1 ha.2.1 ha.1.2 ha.2.2
    have hsecond := abs_log_norm_smul_sub_le p.1 p.2 hp.1 hp.2.1 hp.2.2
      ρ B ρ ρ hρ le_rfl le_rfl (ha.1.1.trans ha.1.2) (ha.2.1.trans ha.2.2)
    simp only [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (by dsimp only [bound]; linarith)
  have hpoint : ∀ᵐ p : ℂ × ℂ ∂(circleMeasure 0 0).prod (circleMeasure 0 0),
      Tendsto (fun a : ℝ × ℝ => |Real.log ‖a.1 • p.1-a.2 • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|)
        (𝓝[Set.Icc ρ B ×ˢ Set.Icc ρ B] (ρ,ρ)) (𝓝 0) := by
    filter_upwards [ae_unitCircle_pair_spec] with p hp
    have hraw : Tendsto (fun a : ℝ × ℝ => a.1 • p.1-a.2 • p.2)
        (𝓝[Set.Icc ρ B ×ˢ Set.Icc ρ B] (ρ,ρ)) (𝓝 (ρ • p.1-ρ • p.2)) :=
      (by fun_prop : Continuous (fun a : ℝ × ℝ => a.1 • p.1-a.2 • p.2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hn : ‖ρ • p.1-ρ • p.2‖ ≠ 0 := by
      rw [← smul_sub, norm_smul]
      exact mul_ne_zero (norm_ne_zero_iff.mpr hρ.ne')
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.2.2))
    simpa only [sub_self, abs_zero] using ((hraw.norm.log hn).sub (tendsto_const_nhds (x := Real.log ‖ρ • p.1-ρ • p.2‖))).abs

  simpa only [integral_zero] using hlim hbound hmajor hpoint

/-- The absolute angular log error is integrable at every pair of collar radii. -/
theorem integrable_radial_circleLog_error (ρ B r s : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ r) (hs : ρ ≤ s) (hrB : r ≤ B) (hsB : s ≤ B) :
    Integrable (fun p : ℂ × ℂ =>
      |Real.log ‖r • p.1-s • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|)
      ((circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  have hf := integrable_weighted_radial_circleLog (fun _ => (1 : ℝ)) measurable_const
    1 ρ B r s (by norm_num) hρ hr hs hrB hsB
    (by intros; norm_num)
  have hg := integrable_weighted_radial_circleLog (fun _ => (1 : ℝ)) measurable_const
    1 ρ B ρ ρ (by norm_num) hρ le_rfl le_rfl (hr.trans hrB) (hs.trans hsB)
    (by intros; norm_num)
  simpa only [one_mul, Real.norm_eq_abs, Pi.sub_apply] using (hf.sub hg).norm

/-- All angular weights with the same bound have the same radial error estimate. -/
theorem abs_weighted_radial_circleLog_sub_le (F : ℂ × ℂ → ℝ) (hF : Measurable F)
    (M ρ B r s : ℝ) (hM : 0 ≤ M) (hρ : 0 < ρ) (hr : ρ ≤ r) (hs : ρ ≤ s)
    (hrB : r ≤ B) (hsB : s ≤ B)
    (hbound : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |F (u,v)| ≤ M) :
    |(∫ p : ℂ × ℂ, F p*Real.log ‖r • p.1-s • p.2‖
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0))-
      (∫ p : ℂ × ℂ, F p*Real.log ‖ρ • p.1-ρ • p.2‖
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0))| ≤
      M*(∫ p : ℂ × ℂ, |Real.log ‖r • p.1-s • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  have hf := integrable_weighted_radial_circleLog F hF M ρ B r s hM hρ hr hs hrB hsB hbound
  have hg := integrable_weighted_radial_circleLog F hF M ρ B ρ ρ hM hρ le_rfl le_rfl
    (hr.trans hrB) (hs.trans hsB) hbound
  have he := integrable_radial_circleLog_error ρ B r s hρ hr hs hrB hsB
  rw [← integral_sub hf hg, ← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hf.sub hg).norm (he.const_mul M)
  filter_upwards [ae_unitCircle_pair_spec] with p hp
  simp only [Pi.sub_apply, Real.norm_eq_abs, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbound p.1 p.2 hp.1 hp.2.1) (abs_nonneg _)

/-- The literal Poisson angular weight written on the unit-circle carrier. -/
noncomputable def unitPoissonWeight (c : ℂ) (ρ : ℝ) (z u : ℂ) : ℝ :=
  (ρ^2-‖z-c‖^2)/‖c+ρ • u-z‖^2

/-- The angular Poisson weight is Borel measurable even off the circle. -/
theorem measurable_unitPoissonWeight (c z : ℂ) (ρ : ℝ) :
    Measurable (unitPoissonWeight c ρ z) := by
  unfold unitPoissonWeight
  fun_prop

/-- Unit-circle Poisson weights agree with the literal collar boundary factor. -/
theorem unitPoissonWeight_eq_boundaryWeight (c z u : ℂ) (ρ : ℝ) (hu : ‖u‖ = 1) :
    unitPoissonWeight c ρ z u =
      (ρ^2-‖z-c‖^2)/‖c+(ρ : ℂ)*((c+u)-c)/(‖(c+u)-c‖ : ℂ)-z‖^2 := by
  simp only [unitPoissonWeight, add_sub_cancel_left, hu, Complex.ofReal_one,
    div_one, Complex.real_smul]

/-- Unit-circle Poisson weights are nonnegative at interior parameters. -/
theorem unitPoissonWeight_nonneg (c z u : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) : 0 ≤ unitPoissonWeight c ρ z u := by
  exact div_nonneg (poissonNumerator_pos c z ρ hρ hz).le (sq_nonneg _)

/-- The same deterministic Poisson bound holds uniformly on every compact inner disk. -/
theorem unitPoissonWeight_le (c z u : ℂ) (ρ a : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hu : ‖u‖ = 1) :
    unitPoissonWeight c ρ z u ≤ ρ^2/(ρ-a)^2 := by
  rw [unitPoissonWeight_eq_boundaryWeight c z u ρ hu]
  apply poissonBoundaryWeight_le c z (c+u) ρ a hρ haρ hz
  intro h
  have : u = 0 := add_left_cancel (by simpa only [add_zero] using h : c+u=c+0)
  rw [this, norm_zero] at hu
  norm_num at hu

/-- Products of two inner-disk Poisson weights have one common angular bound. -/
theorem unitPoissonWeight_pair_abs_le (c z w u v : ℂ) (ρ a : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hw : ‖w-c‖ ≤ a)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |unitPoissonWeight c ρ z u*unitPoissonWeight c ρ w v| ≤ (ρ^2/(ρ-a)^2)^2 := by
  have hzD : z ∈ ball c ρ := mem_ball_iff_norm.mpr (hz.trans_lt haρ)
  have hwD : w ∈ ball c ρ := mem_ball_iff_norm.mpr (hw.trans_lt haρ)
  rw [abs_of_nonneg (mul_nonneg (unitPoissonWeight_nonneg c z u ρ hρ hzD)
    (unitPoissonWeight_nonneg c w v ρ hρ hwD)), pow_two]
  exact mul_le_mul (unitPoissonWeight_le c z u ρ a hρ haρ hz hu)
    (unitPoissonWeight_le c w v ρ a hρ haρ hw hv)
    (unitPoissonWeight_nonneg c w v ρ hρ hwD)
    (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The deterministic weighted Poisson boundary covariance exists as a genuine integral. -/
theorem integrable_poisson_radial_circleLog (c z w : ℂ) (ρ a B r s : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hw : ‖w-c‖ ≤ a)
    (hr : ρ ≤ r) (hs : ρ ≤ s) (hrB : r ≤ B) (hsB : s ≤ B) :
    Integrable (fun p : ℂ × ℂ => unitPoissonWeight c ρ z p.1*
      unitPoissonWeight c ρ w p.2*Real.log ‖r • p.1-s • p.2‖)
      ((circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  apply integrable_weighted_radial_circleLog
    (fun p => unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2)
    ((measurable_unitPoissonWeight c z ρ).comp measurable_fst |>.mul
      ((measurable_unitPoissonWeight c w ρ).comp measurable_snd))
    ((ρ^2/(ρ-a)^2)^2) ρ B r s (sq_nonneg _) hρ hr hs hrB hsB
  exact fun u v hu hv => unitPoissonWeight_pair_abs_le c z w u v ρ a hρ haρ hz hw hu hv

/-- Uniform covariance error for all pairs of parameters in a compact inner disk. -/
theorem abs_poisson_radial_circleLog_sub_le (c z w : ℂ) (ρ a B r s : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hw : ‖w-c‖ ≤ a)
    (hr : ρ ≤ r) (hs : ρ ≤ s) (hrB : r ≤ B) (hsB : s ≤ B) :
    |(∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
        Real.log ‖r • p.1-s • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0))-
      (∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
        Real.log ‖ρ • p.1-ρ • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0))| ≤
    (ρ^2/(ρ-a)^2)^2*(∫ p : ℂ × ℂ,
      |Real.log ‖r • p.1-s • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  exact abs_weighted_radial_circleLog_sub_le
    (fun p => unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2)
    ((measurable_unitPoissonWeight c z ρ).comp measurable_fst |>.mul
      ((measurable_unitPoissonWeight c w ρ).comp measurable_snd))
    ((ρ^2/(ρ-a)^2)^2) ρ B r s (sq_nonneg _) hρ hr hs hrB hsB
    (fun u v hu hv => unitPoissonWeight_pair_abs_le c z w u v ρ a hρ haρ hz hw hu hv)


/-- The angular Poisson weight equals Mathlib's kernel on every unit direction. -/
theorem unitPoissonWeight_eq_poissonKernel (c z u : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hu : ‖u‖ = 1) : unitPoissonWeight c ρ z u = poissonKernel c z (c+ρ • u) := by
  rw [unitPoissonWeight, poissonKernel_def]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hu, mul_one]
  congr 2
  congr 1
  ring

/-- Unit-circle Poisson weights are integrable with respect to normalized arclength. -/
theorem integrable_unitPoissonWeight (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) : Integrable (unitPoissonWeight c ρ z) (circleMeasure 0 0) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  have hbound : ∀ᵐ u ∂circleMeasure 0 0,
      ‖unitPoissonWeight c ρ z u‖ ≤ ρ^2/(ρ-‖z-c‖)^2 := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
    have hu' : ‖u‖ = 1 := by simpa only [sub_zero, neg_zero, Real.exp_zero] using hu
    rw [Real.norm_eq_abs, abs_of_nonneg (unitPoissonWeight_nonneg c z u ρ hρ hz)]
    exact unitPoissonWeight_le c z u ρ ‖z-c‖ hρ (mem_ball_iff_norm.mp hz) le_rfl hu'
  exact (integrable_const _).mono' (measurable_unitPoissonWeight c z ρ).aestronglyMeasurable hbound

/-- Angular Poisson probability weights have total mass one. -/
theorem integral_unitPoissonWeight (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) : ∫ u, unitPoissonWeight c ρ z u ∂circleMeasure 0 0 = 1 := by
  rw [integral_circleMeasure_eq_circleAverage _ _ _ (measurable_unitPoissonWeight c z ρ)]
  simp only [neg_zero, Real.exp_zero]
  calc
    _ = Real.circleAverage (poissonKernel c z) c ρ := by
      rw [Real.circleAverage_def, Real.circleAverage_def]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      have hn : ‖circleMap 0 1 θ‖ = 1 := by simp only [norm_circleMap_zero, abs_one]
      rw [unitPoissonWeight_eq_poissonKernel c z (circleMap 0 1 θ) ρ hρ hn]
      congr 1
      simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
    _ = 1 := circleAverage_poissonKernel_eq_one c z ρ hz


end DOZZ.Proofs
