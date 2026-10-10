/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.WeightedGmcBallMoment
public import DOZZ.GMC.SharpMoments.OpenSetScale

/-! # Exact scaling of singular weighted GMC masses

The singular weighted mass `∫_{B(0,r)} |x|^β M(dx)` of an `IsGMCOf` version obeys the same exact
affine scaling as the plain mass. The proof approximates the extended-valued weighted integrand
from below by bounded continuous cutoffs, applies the affine test law to each one, and passes to
the (possibly infinite) monotone limit at the level of laws on `[0, ∞]`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Laws of monotone suprema -/

/-- The strict upper level sets of a pointwise supremum are the union of those of the terms. -/
theorem weightedScale_preimage_iSup {Z : Type*} (c : ℕ → Z → ℝ≥0∞) (t : ℝ≥0∞) :
    (fun z => ⨆ n, c n z) ⁻¹' Ioi t = ⋃ n, c n ⁻¹' Ioi t := by
  ext z
  simp [lt_iSup_iff]

/-- For monotone terms the strict upper level sets increase. -/
theorem weightedScale_preimage_monotone {Z : Type*} (c : ℕ → Z → ℝ≥0∞) (t : ℝ≥0∞)
    (hc : ∀ z, Monotone fun n => c n z) : Monotone fun n => c n ⁻¹' Ioi t :=
  fun _ _ hmn _ hz => lt_of_lt_of_le hz (hc _ hmn)

/-- The mass of a strict upper level set of a monotone supremum is the supremum of the masses of
the level sets of the terms. -/
theorem weightedScale_measure_iSup {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (c : ℕ → Z → ℝ≥0∞) (hc : ∀ z, Monotone fun n => c n z) (t : ℝ≥0∞) :
    μ ((fun z => ⨆ n, c n z) ⁻¹' Ioi t) = ⨆ n, μ (c n ⁻¹' Ioi t) := by
  rw [weightedScale_preimage_iSup, (weightedScale_preimage_monotone c t hc).measure_iUnion]

/-- If two monotone sequences of extended random variables have equal laws for every index, then
their suprema have equal laws. -/
theorem weightedScale_map_iSup_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (a : ℕ → Ω → ℝ≥0∞) (b : ℕ → Ω' → ℝ≥0∞)
    (ha : ∀ n, AEMeasurable (a n) P) (hb : ∀ n, AEMeasurable (b n) Q)
    (hamono : ∀ ω, Monotone fun n => a n ω) (hbmono : ∀ q, Monotone fun n => b n q)
    (hlaw : ∀ n, Measure.map (a n) P = Measure.map (b n) Q) :
    Measure.map (fun ω => ⨆ n, a n ω) P = Measure.map (fun q => ⨆ n, b n q) Q := by
  have haS : AEMeasurable (fun ω => ⨆ n, a n ω) P := AEMeasurable.iSup ha
  have hbS : AEMeasurable (fun q => ⨆ n, b n q) Q := AEMeasurable.iSup hb
  have hIoi (t : ℝ≥0∞) : Measure.map (fun ω => ⨆ n, a n ω) P (Ioi t) =
      Measure.map (fun q => ⨆ n, b n q) Q (Ioi t) := by
    rw [Measure.map_apply_of_aemeasurable haS measurableSet_Ioi,
      Measure.map_apply_of_aemeasurable hbS measurableSet_Ioi,
      weightedScale_measure_iSup a hamono, weightedScale_measure_iSup b hbmono]
    refine iSup_congr fun n => ?_
    rw [← Measure.map_apply_of_aemeasurable (ha n) measurableSet_Ioi,
      ← Measure.map_apply_of_aemeasurable (hb n) measurableSet_Ioi, hlaw n]
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    hIoi t]

/-! ### The truncated radial weight -/

/-- The singular radial weight `|x| ^ β` as an extended nonnegative real; at the center it takes
the value `0 ^ β`, which is infinite for negative `β`. -/
noncomputable def weightedScale_weight (β : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖x‖ ^ β

/-- The radial profile of the weight truncated at height `n`, as a real function. -/
noncomputable def weightedScale_profile (β : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (min (n : ℝ≥0∞) (ENNReal.ofReal t ^ β)).toReal

/-- The truncated profile is finite. -/
theorem weightedScale_profile_ne_top (β : ℝ) (n : ℕ) (t : ℝ) :
    min (n : ℝ≥0∞) (ENNReal.ofReal t ^ β) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_left _ _)

/-- The truncated profile is nonnegative. -/
theorem weightedScale_profile_nonneg (β : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ weightedScale_profile β n t :=
  ENNReal.toReal_nonneg

/-- The truncated profile at height `n` is bounded by `n`. -/
theorem weightedScale_profile_le (β : ℝ) (n : ℕ) (t : ℝ) :
    weightedScale_profile β n t ≤ n := by
  calc weightedScale_profile β n t ≤ (n : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (min_le_left _ _)
    _ = n := ENNReal.toReal_natCast n

/-- The truncated profile is continuous, since the truncation removes the singularity. -/
theorem weightedScale_profile_continuous (β : ℝ) (n : ℕ) :
    Continuous (weightedScale_profile β n) :=
  ENNReal.continuousOn_toReal.comp_continuous
    (continuous_const.min (ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal))
    (weightedScale_profile_ne_top β n)

/-- The truncated profiles increase with the height. -/
theorem weightedScale_profile_mono (β : ℝ) (t : ℝ) {m n : ℕ} (h : m ≤ n) :
    weightedScale_profile β m t ≤ weightedScale_profile β n t :=
  ENNReal.toReal_mono (weightedScale_profile_ne_top β n t)
    (min_le_min_right _ (Nat.cast_le.2 h))

/-- The extended value of the truncated profile is the truncation of the extended weight. -/
theorem weightedScale_ofReal_profile (β : ℝ) (n : ℕ) (t : ℝ) :
    ENNReal.ofReal (weightedScale_profile β n t) = min (n : ℝ≥0∞) (ENNReal.ofReal t ^ β) :=
  ENNReal.ofReal_toReal (weightedScale_profile_ne_top β n t)

/-- The truncated profiles increase to the extended radial weight at every radius. -/
theorem weightedScale_profile_tendsto (β : ℝ) (t : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (weightedScale_profile β n t)) atTop
      (𝓝 (ENNReal.ofReal t ^ β)) := by
  simp_rw [weightedScale_ofReal_profile]
  simpa using ENNReal.tendsto_nat_nhds_top.min (tendsto_const_nhds (x := ENNReal.ofReal t ^ β))

/-! ### Cutoff tests approximating the weight from below -/

/-- The open-ball cutoffs increase with the index. -/
theorem weightedScale_cutoff_mono (U : Set ℂ) (x : ℂ) {m n : ℕ} (h : m ≤ n) :
    openSetApproxFun U m x ≤ openSetApproxFun U n x :=
  min_le_min_left 1 (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) Metric.infDist_nonneg)

/-- At a point of an open set with nonempty complement the cutoffs are eventually equal to one. -/
theorem weightedScale_cutoff_eventually_one {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty)
    {x : ℂ} (hx : x ∈ U) : ∀ᶠ n : ℕ in atTop, openSetApproxFun U n x = 1 := by
  have hpos : 0 < Metric.infDist x Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hx)
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * Metric.infDist x Uᶜ :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hpos).eventually_ge_atTop 1
  exact hev.mono fun n hn => by simp [openSetApproxFun, hn]

/-- The truncated radial weight times the cutoff of the ball `B(0,R)`. -/
noncomputable def weightedScale_fun (β R : ℝ) (n : ℕ) (x : ℂ) : ℝ :=
  weightedScale_profile β n ‖x‖ * openSetApproxFun (Metric.ball 0 R) n x

/-- The truncated weight tests are continuous. -/
theorem weightedScale_fun_continuous (β R : ℝ) (n : ℕ) :
    Continuous (weightedScale_fun β R n) :=
  ((weightedScale_profile_continuous β n).comp continuous_norm).mul
    (openSetApproxFun_continuous _ n)

/-- The truncated weight tests are nonnegative. -/
theorem weightedScale_fun_nonneg (β R : ℝ) (n : ℕ) (x : ℂ) : 0 ≤ weightedScale_fun β R n x :=
  mul_nonneg (weightedScale_profile_nonneg β n _) (openSetApproxFun_bounds _ n x).1

/-- The truncated weight test at height `n` is bounded by `n`. -/
theorem weightedScale_fun_le (β R : ℝ) (n : ℕ) (x : ℂ) : weightedScale_fun β R n x ≤ n := by
  calc weightedScale_fun β R n x ≤ (n : ℝ) * 1 :=
        mul_le_mul (weightedScale_profile_le β n _) (openSetApproxFun_bounds _ n x).2
          (openSetApproxFun_bounds _ n x).1 (Nat.cast_nonneg n)
    _ = n := mul_one _

/-- The truncated weight tests vanish off the ball. -/
theorem weightedScale_fun_eq_zero_of_notMem {β R : ℝ} {x : ℂ} (hx : x ∉ Metric.ball (0 : ℂ) R)
    (n : ℕ) : weightedScale_fun β R n x = 0 := by
  simp [weightedScale_fun, openSetApproxFun_eq_zero_of_notMem hx n]

/-- The truncated weight tests increase with the index. -/
theorem weightedScale_fun_mono (β R : ℝ) (x : ℂ) {m n : ℕ} (h : m ≤ n) :
    weightedScale_fun β R m x ≤ weightedScale_fun β R n x :=
  mul_le_mul (weightedScale_profile_mono β _ h) (weightedScale_cutoff_mono _ x h)
    (openSetApproxFun_bounds _ m x).1 (weightedScale_profile_nonneg β n _)

/-- The truncated weight tests as bounded continuous functions. -/
noncomputable def weightedScale_test (β R : ℝ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (weightedScale_fun β R n)
    (weightedScale_fun_continuous β R n) n (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weightedScale_fun_nonneg β R n x)]
      exact weightedScale_fun_le β R n x)

/-- The bounded continuous test evaluates as the underlying function. -/
theorem weightedScale_test_apply (β R : ℝ) (n : ℕ) (x : ℂ) :
    weightedScale_test β R n x = weightedScale_fun β R n x := rfl

/-- The truncated weight tests are supported in the closed ball. -/
theorem weightedScale_test_tsupport_subset (β R : ℝ) (n : ℕ) :
    tsupport (weightedScale_test β R n : ℂ → ℝ) ⊆ Metric.closedBall 0 R := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  by_contra hxc
  exact hx (weightedScale_fun_eq_zero_of_notMem
    (fun hxb => hxc (Metric.ball_subset_closedBall hxb)) n)

/-- The cutoff tests increase pointwise to the indicator of the ball times the weight. -/
theorem weightedScale_fun_tendsto (β R : ℝ) (x : ℂ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (weightedScale_fun β R n x)) atTop
      (𝓝 ((Metric.ball (0 : ℂ) R).indicator (weightedScale_weight β) x)) := by
  by_cases hx : x ∈ Metric.ball (0 : ℂ) R
  · have hev := weightedScale_cutoff_eventually_one Metric.isOpen_ball
      (openSetScale_compl_nonempty Metric.ball_subset_closedBall) hx
    rw [Set.indicator_of_mem hx]
    refine (weightedScale_profile_tendsto β ‖x‖).congr' ?_
    filter_upwards [hev] with n hn
    simp [weightedScale_fun, hn]
  · rw [Set.indicator_of_notMem hx]
    simp [weightedScale_fun_eq_zero_of_notMem hx]

/-! ### Monotone limits of test integrals -/

/-- Monotone bounded continuous nonnegative tests whose extended values converge pointwise have
integrals increasing to the extended integral of the pointwise limit. -/
theorem weightedScale_iSup_integral {μ : Measure ℂ} [IsFiniteMeasure μ]
    (h : ℕ → BoundedContinuousFunction ℂ ℝ) (hnn : ∀ n x, 0 ≤ h n x)
    (hmono : ∀ x, Monotone fun n => h n x) {F : ℂ → ℝ≥0∞}
    (hlim : ∀ x, Tendsto (fun n => ENNReal.ofReal (h n x)) atTop (𝓝 (F x))) :
    ⨆ n, ENNReal.ofReal (∫ x, h n x ∂μ) = ∫⁻ x, F x ∂μ := by
  have hint (n : ℕ) : ENNReal.ofReal (∫ x, h n x ∂μ) = ∫⁻ x, ENNReal.ofReal (h n x) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal ((h n).integrable μ) (ae_of_all _ (hnn n))
  have hmeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (h n x)) μ :=
    (ENNReal.measurable_ofReal.comp (h n).continuous.measurable).aemeasurable
  have hlint : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (h n x) ∂μ) atTop
      (𝓝 (∫⁻ x, F x ∂μ)) :=
    lintegral_tendsto_of_tendsto_of_monotone hmeas
      (ae_of_all _ fun x _ _ hmn => ENNReal.ofReal_le_ofReal (hmono x hmn))
      (ae_of_all _ hlim)
  have hlmono : Monotone fun n => ∫⁻ x, ENNReal.ofReal (h n x) ∂μ :=
    fun _ _ hmn => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hmono x hmn)
  simp_rw [hint]
  exact tendsto_nhds_unique (tendsto_atTop_iSup hlmono) hlint

/-- The weighted ball mass is the extended integral of the indicator of the ball times the
weight. -/
theorem weightedScale_mass_eq_lintegral (γ α r : ℝ) (μ : Measure ℂ) :
    weightedGmcBallMass γ μ α 0 r =
      ∫⁻ x, (Metric.ball (0 : ℂ) r).indicator (weightedScale_weight (-γ * α)) x ∂μ := by
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet]
  simp [weightedGmcBallMass, weightedScale_weight]

/-- The integrals of the cutoff tests increase to the weighted ball mass of a finite measure. -/
theorem weightedScale_iSup_test_integral (γ α r : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    ⨆ n, ENNReal.ofReal (∫ x, weightedScale_test (-γ * α) r n x ∂μ) =
      weightedGmcBallMass γ μ α 0 r := by
  rw [weightedScale_mass_eq_lintegral]
  exact weightedScale_iSup_integral (fun n => weightedScale_test (-γ * α) r n)
    (fun n x => weightedScale_fun_nonneg _ r n x)
    (fun x _ _ hmn => weightedScale_fun_mono _ r x hmn)
    (fun x => weightedScale_fun_tendsto _ r x)

/-! ### Dilated tests -/

/-- Scaling the weight by a dilation: `c ^ β * |c⁻¹ x| ^ β = |x| ^ β`. -/
theorem weightedScale_weight_smul {c : ℝ} (hc : 0 < c) (β : ℝ) (x : ℂ) :
    ENNReal.ofReal (c ^ β) * weightedScale_weight β (c⁻¹ • x) = weightedScale_weight β x := by
  have hc' : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  unfold weightedScale_weight
  rw [norm_smul, Real.norm_of_nonneg hc', ENNReal.ofReal_mul hc',
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos (inv_pos.2 hc), ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le β), ← Real.mul_rpow hc.le hc',
    mul_inv_cancel₀ hc.ne', Real.one_rpow, ENNReal.ofReal_one, one_mul]

/-- A dilated point lies in the ball of radius `R` exactly when the original point lies in the ball
of radius `c * R`. -/
theorem weightedScale_smul_mem_ball_iff {c : ℝ} (hc : 0 < c) (R : ℝ) (x : ℂ) :
    c⁻¹ • x ∈ Metric.ball (0 : ℂ) R ↔ x ∈ Metric.ball (0 : ℂ) (c * R) := by
  simp only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  exact inv_mul_lt_iff₀ hc

/-- The target tests `x ↦ c ^ β * g_n (c⁻¹ • x)`. -/
noncomputable def weightedScale_scaled (β c R : ℝ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (c ^ β) • (weightedScale_test β R n).compContinuous ⟨fun x : ℂ => c⁻¹ • x, by fun_prop⟩

/-- The dilated test evaluates as the scaled composition. -/
theorem weightedScale_scaled_apply (β c R : ℝ) (n : ℕ) (x : ℂ) :
    weightedScale_scaled β c R n x = c ^ β * weightedScale_fun β R n (c⁻¹ • x) := rfl

/-- The dilated tests are nonnegative. -/
theorem weightedScale_scaled_nonneg {c : ℝ} (hc : 0 < c) (β R : ℝ) (n : ℕ) (x : ℂ) :
    0 ≤ weightedScale_scaled β c R n x :=
  mul_nonneg (Real.rpow_nonneg hc.le β) (weightedScale_fun_nonneg β R n _)

/-- The dilated tests increase with the index. -/
theorem weightedScale_scaled_mono {c : ℝ} (hc : 0 < c) (β R : ℝ) (x : ℂ) {m n : ℕ} (h : m ≤ n) :
    weightedScale_scaled β c R m x ≤ weightedScale_scaled β c R n x :=
  mul_le_mul_of_nonneg_left (weightedScale_fun_mono β R _ h) (Real.rpow_nonneg hc.le β)

/-- The dilated tests are supported in the dilated closed ball. -/
theorem weightedScale_scaled_tsupport_subset {c : ℝ} (hc : 0 < c) (β R : ℝ) (n : ℕ) :
    tsupport (weightedScale_scaled β c R n : ℂ → ℝ) ⊆ Metric.closedBall 0 (c * R) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  by_contra hxc
  apply hx
  have hnot : c⁻¹ • x ∉ Metric.ball (0 : ℂ) R := fun hmem =>
    hxc (Metric.ball_subset_closedBall ((weightedScale_smul_mem_ball_iff hc R x).1 hmem))
  rw [weightedScale_scaled_apply, weightedScale_fun_eq_zero_of_notMem hnot, mul_zero]

/-- Composing the dilated test with the dilation recovers the source test, up to the factor
`c ^ β`. -/
theorem weightedScale_scaled_comp {c : ℝ} (hc : 0 < c) (β R : ℝ) (n : ℕ) (y : ℂ) :
    weightedScale_scaled β c R n (0 + c • y) = c ^ β * weightedScale_test β R n y := by
  simp [weightedScale_scaled_apply, hc.ne', weightedScale_test_apply]

/-- The dilated tests increase pointwise to the indicator of the smaller ball times the weight. -/
theorem weightedScale_scaled_tendsto {c : ℝ} (hc : 0 < c) (β R : ℝ) (x : ℂ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (weightedScale_scaled β c R n x)) atTop
      (𝓝 ((Metric.ball (0 : ℂ) (c * R)).indicator (weightedScale_weight β) x)) := by
  have h := ENNReal.Tendsto.const_mul (weightedScale_fun_tendsto β R (c⁻¹ • x))
    (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (c ^ β))
  have hfun : (fun n : ℕ => ENNReal.ofReal (weightedScale_scaled β c R n x)) =
      fun n => ENNReal.ofReal (c ^ β) * ENNReal.ofReal (weightedScale_fun β R n (c⁻¹ • x)) := by
    funext n
    rw [weightedScale_scaled_apply, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le β)]
  rw [hfun]
  convert h using 2
  by_cases hx : x ∈ Metric.ball (0 : ℂ) (c * R)
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem ((weightedScale_smul_mem_ball_iff hc R x).2 hx),
      weightedScale_weight_smul hc]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (mt (weightedScale_smul_mem_ball_iff hc R x).1 hx), mul_zero]

/-- The integrals of the dilated tests increase to the weighted mass of the smaller ball. -/
theorem weightedScale_iSup_scaled_integral {c : ℝ} (hc : 0 < c) (γ α R : ℝ) (μ : Measure ℂ)
    [IsFiniteMeasure μ] :
    ⨆ n, ENNReal.ofReal (∫ x, weightedScale_scaled (-γ * α) c R n x ∂μ) =
      weightedGmcBallMass γ μ α 0 (c * R) := by
  rw [weightedScale_mass_eq_lintegral]
  exact weightedScale_iSup_integral (fun n => weightedScale_scaled (-γ * α) c R n)
    (fun n x => weightedScale_scaled_nonneg hc _ R n x)
    (fun x _ _ hmn => weightedScale_scaled_mono hc _ R x hmn)
    (fun x => weightedScale_scaled_tendsto hc _ R x)

/-! ### Measurability of the test integrals and weighted masses -/

/-- Test integrals of bounded continuous functions supported in a closed ball inside the unit disk
are a.e. measurable. -/
theorem weightedScale_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {r : ℝ} (hr : r ≤ 1)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hf : tsupport (f : ℂ → ℝ) ⊆ Metric.closedBall 0 r) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P :=
  openSetScale_test_integral_aemeasurable P X hX γ M hM (Metric.closedBall 0 r)
    Metric.isClosed_closedBall.measurableSet
    (fun x hx => (by simpa using hx : ‖x‖ ≤ r).trans hr) f
    (boundedContinuousFunction_eq_zero_off_tsupport_subset f _ hf)

/-- The weighted mass of a ball inside the unit disk is a.e. measurable, as a supremum of
a.e. measurable test integrals. -/
theorem weightedScale_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α : ℝ) {r : ℝ} (hr : r ≤ 1) :
    AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) α 0 r) P := by
  have h : (fun ω => weightedGmcBallMass γ (M ω) α 0 r) = fun ω =>
      ⨆ n, ENNReal.ofReal (∫ x, weightedScale_test (-γ * α) r n x ∂M ω) := by
    funext ω
    have := hM.1 ω
    exact (weightedScale_iSup_test_integral γ α r (M ω)).symm
  rw [h]
  exact AEMeasurable.iSup fun n => ENNReal.measurable_ofReal.comp_aemeasurable
    (weightedScale_integral_aemeasurable P X hX γ M hM hr _
      (weightedScale_test_tsupport_subset _ r n))

/-! ### From laws of one-coordinate vectors to laws of extended values -/

/-- Equal laws of one-coordinate real vectors give equal laws of the corresponding extended values
`ENNReal.ofReal`. -/
theorem weightedScale_map_ofReal_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {x : Ω → ℝ} {y : Ω' → ℝ} (hx : AEMeasurable x P) (hy : AEMeasurable y Q)
    (h : Measure.map (fun ω (_ : Fin 1) => x ω) P = Measure.map (fun q (_ : Fin 1) => y q) Q) :
    Measure.map (fun ω => ENNReal.ofReal (x ω)) P =
      Measure.map (fun q => ENNReal.ofReal (y q)) Q := by
  have hΦ : Measurable (fun v : Fin 1 → ℝ => ENNReal.ofReal (v 0)) :=
    ENNReal.measurable_ofReal.comp (measurable_pi_apply 0)
  have hx' : AEMeasurable (fun ω (_ : Fin 1) => x ω) P := aemeasurable_pi_iff.2 fun _ => hx
  have hy' : AEMeasurable (fun q (_ : Fin 1) => y q) Q := aemeasurable_pi_iff.2 fun _ => hy
  calc Measure.map (fun ω => ENNReal.ofReal (x ω)) P
      = Measure.map (fun v : Fin 1 → ℝ => ENNReal.ofReal (v 0))
          (Measure.map (fun ω (_ : Fin 1) => x ω) P) :=
        (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hx').symm
    _ = Measure.map (fun v : Fin 1 → ℝ => ENNReal.ofReal (v 0))
          (Measure.map (fun q (_ : Fin 1) => y q) Q) := by rw [h]
    _ = Measure.map (fun q => ENNReal.ofReal (y q)) Q :=
        AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hy'

/-! ### The law of the weighted mass -/

/-- The integral of a nonnegative bounded continuous test against a finite measure is monotone in
the test. -/
theorem weightedScale_ofReal_integral_mono {μ : Measure ℂ} [IsFiniteMeasure μ]
    {h h' : BoundedContinuousFunction ℂ ℝ} (hle : ∀ x, h x ≤ h' x) :
    ENNReal.ofReal (∫ x, h x ∂μ) ≤ ENNReal.ofReal (∫ x, h' x ∂μ) :=
  ENNReal.ofReal_le_ofReal (integral_mono (h.integrable μ) (h'.integrable μ) hle)

/-- Integrating the dilated test composed with the dilation recovers the source test integral up
to the constant `c ^ β`. -/
theorem weightedScale_integral_scaled_comp {c : ℝ} (hc : 0 < c) (β R : ℝ) (n : ℕ)
    (μ : Measure ℂ) :
    ∫ x, weightedScale_scaled β c R n (0 + c • x) ∂μ =
      c ^ β * ∫ x, weightedScale_test β R n x ∂μ := by
  simp_rw [weightedScale_scaled_comp hc]
  exact integral_const_mul _ _

/-- Passing the exact test laws to the monotone limit gives the law of the weighted mass. -/
theorem weightedScale_mass_law_of_test_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α : ℝ)
    {c R : ℝ} (hc : 0 < c) (hR1 : R ≤ 1) (hcR1 : c * R ≤ 1)
    {G : Measure ℝ} [IsProbabilityMeasure G] {s : ℝ → ℝ} (hs : Measurable s)
    (hs0 : ∀ w, 0 ≤ s w)
    (hvec : ∀ n : ℕ, Measure.map (fun ω (_ : Fin 1) =>
        ∫ x, weightedScale_scaled (-γ * α) c R n x ∂M ω) P =
      Measure.map (fun q : Ω × ℝ => fun _ : Fin 1 =>
        s q.2 * ∫ x, weightedScale_scaled (-γ * α) c R n (0 + c • x) ∂M q.1) (P.prod G)) :
    Measure.map (fun ω => weightedGmcBallMass γ (M ω) α 0 (c * R)) P =
      Measure.map (fun q : Ω × ℝ => ENNReal.ofReal (s q.2) *
        (ENNReal.ofReal (c ^ (-γ * α)) * weightedGmcBallMass γ (M q.1) α 0 R)) (P.prod G) := by
  have : IsProbabilityMeasure P := hX.1
  have hκ : 0 ≤ c ^ (-γ * α) := Real.rpow_nonneg hc.le _
  have hfint (n : ℕ) : AEMeasurable (fun ω => ∫ x, weightedScale_scaled (-γ * α) c R n x ∂M ω) P :=
    weightedScale_integral_aemeasurable P X hX γ M hM hcR1 _
      (weightedScale_scaled_tsupport_subset hc _ R n)
  have hgint (n : ℕ) : AEMeasurable (fun ω => ∫ x, weightedScale_test (-γ * α) R n x ∂M ω) P :=
    weightedScale_integral_aemeasurable P X hX γ M hM hR1 _
      (weightedScale_test_tsupport_subset _ R n)
  have hgintQ (n : ℕ) : AEMeasurable
      (fun q : Ω × ℝ => ∫ x, weightedScale_test (-γ * α) R n x ∂M q.1) (P.prod G) :=
    (hgint n).comp_fst
  have hlaw (n : ℕ) : Measure.map (fun ω => ENNReal.ofReal
        (∫ x, weightedScale_scaled (-γ * α) c R n x ∂M ω)) P =
      Measure.map (fun q : Ω × ℝ => ENNReal.ofReal (s q.2) * (ENNReal.ofReal (c ^ (-γ * α)) *
        ENNReal.ofReal (∫ x, weightedScale_test (-γ * α) R n x ∂M q.1))) (P.prod G) := by
    have hy : AEMeasurable (fun q : Ω × ℝ => s q.2 * (c ^ (-γ * α) *
        ∫ x, weightedScale_test (-γ * α) R n x ∂M q.1)) (P.prod G) :=
      (hs.comp measurable_snd).aemeasurable.mul (aemeasurable_const.mul (hgintQ n))
    have h := weightedScale_map_ofReal_eq (hfint n) hy (by
      rw [hvec n]
      refine congrArg (fun F => Measure.map F (P.prod G)) ?_
      funext q j
      rw [weightedScale_integral_scaled_comp hc])
    rw [h]
    refine congrArg (fun F => Measure.map F (P.prod G)) ?_
    funext q
    rw [ENNReal.ofReal_mul (hs0 _), ENNReal.ofReal_mul hκ]
  have key := weightedScale_map_iSup_eq
    (fun n ω => ENNReal.ofReal (∫ x, weightedScale_scaled (-γ * α) c R n x ∂M ω))
    (fun n (q : Ω × ℝ) => ENNReal.ofReal (s q.2) * (ENNReal.ofReal (c ^ (-γ * α)) *
      ENNReal.ofReal (∫ x, weightedScale_test (-γ * α) R n x ∂M q.1)))
    (fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hfint n))
    (fun n => (ENNReal.measurable_ofReal.comp (hs.comp measurable_snd)).aemeasurable.mul
      (aemeasurable_const.mul (ENNReal.measurable_ofReal.comp_aemeasurable (hgintQ n))))
    (fun ω m n hmn => by
      have := hM.1 ω
      exact weightedScale_ofReal_integral_mono fun x => weightedScale_scaled_mono hc _ R x hmn)
    (fun q m n hmn => by
      have := hM.1 q.1
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (weightedScale_ofReal_integral_mono
        fun x => weightedScale_fun_mono _ R x hmn)))
    hlaw
  have hA : (fun ω => ⨆ n, ENNReal.ofReal
      (∫ x, weightedScale_scaled (-γ * α) c R n x ∂M ω)) =
      fun ω => weightedGmcBallMass γ (M ω) α 0 (c * R) := by
    funext ω
    have := hM.1 ω
    exact weightedScale_iSup_scaled_integral hc γ α R (M ω)
  have hB : (fun q : Ω × ℝ => ⨆ n, ENNReal.ofReal (s q.2) * (ENNReal.ofReal (c ^ (-γ * α)) *
      ENNReal.ofReal (∫ x, weightedScale_test (-γ * α) R n x ∂M q.1))) =
      fun q => ENNReal.ofReal (s q.2) * (ENNReal.ofReal (c ^ (-γ * α)) *
        weightedGmcBallMass γ (M q.1) α 0 R) := by
    funext q
    have := hM.1 q.1
    rw [← weightedScale_iSup_test_integral γ α R (M q.1), ENNReal.mul_iSup, ENNReal.mul_iSup]
  rw [hA, hB] at key
  exact key

/-- Exact affine law of the singular weighted mass: the weighted mass of `B(0, c R)` has the law of
the weighted mass of `B(0, R)` multiplied by `c ^ (-γ α)` and by the independent Gaussian factor
`c ^ 2 * exp (γ w - γ ^ 2 / 2 * (-log c))`. -/
theorem weightedScale_mass_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α : ℝ)
    {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R) (hRsmall : R < 1) :
    Measure.map (fun ω => weightedGmcBallMass γ (M ω) α 0 (c * R)) P =
      Measure.map (fun q : Ω × ℝ => ENNReal.ofReal
          (c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c))) *
        (ENNReal.ofReal (c ^ (-γ * α)) * weightedGmcBallMass γ (M q.1) α 0 R))
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  have : IsProbabilityMeasure (gaussianReal 0 ⟨-Real.log c,
      neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩) :=
    instIsProbabilityMeasureGaussianReal 0 _
  have hcR : c * R ≤ R := mul_le_of_le_one_left hR.le hc1
  have hTsmall : ‖(0 : ℂ)‖ + c * R < 1 := by
    rw [norm_zero, zero_add]
    exact lt_of_le_of_lt hcR hRsmall
  refine weightedScale_mass_law_of_test_law P X hX γ M hM α hc hRsmall.le
    (hcR.trans hRsmall.le)
    (s := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))) (by fun_prop)
    (fun w => by positivity) fun n => ?_
  exact gmc_affine_test_vector_law P X hX γ M hM (a := 0) hc hc1 hR hRsmall hTsmall
    (fun _ : Fin 1 => weightedScale_scaled (-γ * α) c R n)
    (fun _ x => weightedScale_scaled_nonneg hc _ R n x)
    (fun _ => weightedScale_scaled_tsupport_subset hc _ R n)

/-! ### Moment scaling -/

/-- A finite nonzero factor splits off a real power from a product. -/
theorem weightedScale_mul_rpow {x : ℝ≥0∞} (hx0 : x ≠ 0) (hxt : x ≠ ⊤) (y : ℝ≥0∞) (p : ℝ) :
    (x * y) ^ p = x ^ p * y ^ p := by
  simp [ENNReal.mul_rpow_eq_ite, hx0, hxt]

/-- Transfer of `p`th moments through a law identity of extended masses with an independent
positive finite scale factor. -/
theorem weightedScale_moment_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Measure ℝ} [IsProbabilityMeasure G] {A : ℝ → ℝ≥0∞} (hA : Measurable A)
    (hA0 : ∀ w, A w ≠ 0) (hAt : ∀ w, A w ≠ ⊤) {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤)
    {Wt WR : Ω → ℝ≥0∞} (hWt : AEMeasurable Wt P) (hWR : AEMeasurable WR P)
    (hlaw : Measure.map Wt P =
      Measure.map (fun q : Ω × ℝ => A q.2 * (K * WR q.1)) (P.prod G)) (p : ℝ) :
    ∫⁻ ω, Wt ω ^ p ∂P = (K ^ p * ∫⁻ ω, WR ω ^ p ∂P) * ∫⁻ w, A w ^ p ∂G := by
  have hψ : Measurable (fun x : ℝ≥0∞ => x ^ p) := ENNReal.continuous_rpow_const.measurable
  have hWs : AEMeasurable (fun q : Ω × ℝ => A q.2 * (K * WR q.1)) (P.prod G) :=
    (hA.comp measurable_snd).aemeasurable.mul (aemeasurable_const.mul hWR.comp_fst)
  have hpow : AEMeasurable (fun ω => WR ω ^ p) P := hψ.comp_aemeasurable hWR
  calc ∫⁻ ω, Wt ω ^ p ∂P = ∫⁻ x, x ^ p ∂Measure.map Wt P :=
        (lintegral_map' hψ.aemeasurable hWt).symm
    _ = ∫⁻ x, x ^ p ∂Measure.map (fun q : Ω × ℝ => A q.2 * (K * WR q.1)) (P.prod G) := by
        rw [hlaw]
    _ = ∫⁻ q, (A q.2 * (K * WR q.1)) ^ p ∂P.prod G := lintegral_map' hψ.aemeasurable hWs
    _ = ∫⁻ q, (K ^ p * WR q.1 ^ p) * A q.2 ^ p ∂P.prod G := by
        refine lintegral_congr fun q => ?_
        rw [weightedScale_mul_rpow (hA0 _) (hAt _), weightedScale_mul_rpow hK0 hKt, mul_comm]
    _ = (∫⁻ ω, K ^ p * WR ω ^ p ∂P) * ∫⁻ w, A w ^ p ∂G :=
        lintegral_prod_mul (f := fun ω => K ^ p * WR ω ^ p) (g := fun w => A w ^ p)
          (aemeasurable_const.mul hpow) ((hψ.comp hA).aemeasurable)
    _ = (K ^ p * ∫⁻ ω, WR ω ^ p ∂P) * ∫⁻ w, A w ^ p ∂G := by
        rw [lintegral_const_mul'' _ hpow]

/-- The weight factor `c ^ β` raised to the order `p` combines with a further power of `c` into one
power of `c`. -/
theorem weightedScale_factor_pow {c : ℝ} (hc : 0 < c) (β p ξ : ℝ) :
    ENNReal.ofReal (c ^ β) ^ p * ENNReal.ofReal (c ^ ξ) = ENNReal.ofReal (c ^ (β * p + ξ)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hc β), ← Real.rpow_mul hc.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← Real.rpow_add hc]

/-- Exact scaling of the `p`th moment of the singular weighted mass about the center `0` of the
logarithmic chart, for every `IsGMCOf` version and every real order. The weighted mass may be
infinite, and the extended-power conventions are retained. -/
theorem gmc_weighted_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α : ℝ)
    {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R) (hRsmall : R < 1) (p : ℝ) :
    weightedGmcBallMoment P M γ α 0 (c * R) p =
      ENNReal.ofReal (c ^ ((2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        weightedGmcBallMoment P M γ α 0 R p := by
  have : IsProbabilityMeasure P := hX.1
  have : IsProbabilityMeasure (gaussianReal 0 ⟨-Real.log c,
      neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩) :=
    instIsProbabilityMeasureGaussianReal 0 _
  have hcR : c * R ≤ R := mul_le_of_le_one_left hR.le hc1
  have hκ0 : ENNReal.ofReal (c ^ (-γ * α)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hc _)).ne'
  have hmom := weightedScale_moment_transfer
    (A := fun w => ENNReal.ofReal (c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))))
    (by fun_prop) (fun w => (ENNReal.ofReal_pos.2 (by positivity)).ne')
    (fun w => ENNReal.ofReal_ne_top) hκ0 ENNReal.ofReal_ne_top
    (weightedScale_mass_aemeasurable P X hX γ M hM α (hcR.trans hRsmall.le))
    (weightedScale_mass_aemeasurable P X hX γ M hM α hRsmall.le)
    (weightedScale_mass_law P X hX γ M hM α hc hc1 hR hRsmall) p
  have hgauss := gaussianScaleFactor_rpow_integral γ c p hc hc1
  unfold weightedGmcBallMoment
  simp only [ENNReal.rpow_eq_pow] at hgauss ⊢
  have hexp : -γ * α * p + (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) =
      (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by ring
  rw [hmom, hgauss, mul_right_comm, weightedScale_factor_pow hc, hexp]

end DOZZ.Proofs
