/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.WirtingerZ
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Derivatives of limits, Wirtinger derivatives, and a `C²` criterion

* `bpz_hasFDerivAt_of_tendsto_deriv`: a pointwise limit of differentiable maps `f n` of one
  complex (= two real) variable whose derivatives `f' n` converge pointwise, with locally
  uniform bounds, to a continuous limit `g'`, is differentiable with derivative `g'`. The
  proof integrates along segments: `f n (z + h) - f n z = ∫₀¹ f' n (z + t h) h dt`, passes to the
  limit by dominated convergence, and then uses continuity of `g'`. No continuity of the
  individual `f' n` is needed (only that they are derivatives, hence measurable and bounded).
* `bpz_wirtingerZ_ofReal`, `bpz_wirtingerZ_wirtingerZ_ofReal`: the first and second Wirtinger
  derivatives `∂_z` of a real function, in terms of its real derivatives.
* `bpz_contDiffOn_two_of`: a `C²` criterion on an open set. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-! ### Segments -/

/-- The point `z + t h` of a segment lies in the ball of radius `r` about `z` for `t ∈ [0, 1]`
when `‖h‖ < r`. -/
theorem bpz_segment_mem_ball {z h : ℂ} {r t : ℝ} (hh : ‖h‖ < r) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    z + t • h ∈ Metric.ball z r := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  calc t * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg h)
    _ < r := by rwa [one_mul]

/-- The derivative of `t ↦ f (z + t h)` along a segment inside a ball of differentiability. -/
theorem bpz_hasDerivAt_segment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {f' : ℂ → ℂ →L[ℝ] F} {z h : ℂ} {r : ℝ}
    (hf : ∀ w ∈ Metric.ball z r, HasFDerivAt f (f' w) w) (hh : ‖h‖ < r) {t : ℝ}
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => f (z + s • h)) (f' (z + t • h) h) t := by
  have hγ : HasDerivAt (fun s : ℝ => z + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add z
  exact (hf _ (bpz_segment_mem_ball hh ht)).comp_hasDerivAt t hγ

/-- Along a segment the derivative of a differentiable function is a.e. strongly measurable. -/
theorem bpz_aestronglyMeasurable_segment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℂ → F} {f' : ℂ → ℂ →L[ℝ] F} {z h : ℂ} {r : ℝ}
    (hf : ∀ w ∈ Metric.ball z r, HasFDerivAt f (f' w) w) (hh : ‖h‖ < r) :
    AEStronglyMeasurable (fun t : ℝ => f' (z + t • h) h)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
  refine ((stronglyMeasurable_deriv (fun s : ℝ => f (z + s • h))).aestronglyMeasurable).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun t ht => ?_
  exact (bpz_hasDerivAt_segment hf hh (Set.uIoc_subset_uIcc ht)).deriv

/-- A bounded derivative along a segment is interval integrable. -/
theorem bpz_intervalIntegrable_segment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℂ → F} {f' : ℂ → ℂ →L[ℝ] F} {z h : ℂ} {r C : ℝ}
    (hf : ∀ w ∈ Metric.ball z r, HasFDerivAt f (f' w) w)
    (hC : ∀ w ∈ Metric.ball z r, ‖f' w‖ ≤ C) (hh : ‖h‖ < r) :
    IntervalIntegrable (fun t : ℝ => f' (z + t • h) h) volume 0 1 := by
  rw [intervalIntegrable_iff]
  refine Integrable.mono' (g := fun _ => C * ‖h‖) ?_ (bpz_aestronglyMeasurable_segment hf hh) ?_
  · exact integrableOn_const (by simp)
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun t ht => ?_
    have hmem := bpz_segment_mem_ball (z := z) hh (Set.uIoc_subset_uIcc ht)
    calc ‖f' (z + t • h) h‖ ≤ ‖f' (z + t • h)‖ * ‖h‖ := (f' (z + t • h)).le_opNorm h
      _ ≤ C * ‖h‖ := mul_le_mul_of_nonneg_right (hC _ hmem) (norm_nonneg h)

/-- The fundamental theorem of calculus along a segment, for a function that is differentiable
with bounded (not necessarily continuous) derivative on a ball. -/
theorem bpz_segment_ftc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℂ → F} {f' : ℂ → ℂ →L[ℝ] F} {z h : ℂ} {r C : ℝ}
    (hf : ∀ w ∈ Metric.ball z r, HasFDerivAt f (f' w) w)
    (hC : ∀ w ∈ Metric.ball z r, ‖f' w‖ ≤ C) (hh : ‖h‖ < r) :
    f (z + h) - f z = ∫ t in (0 : ℝ)..1, f' (z + t • h) h := by
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => bpz_hasDerivAt_segment hf hh ht) (bpz_intervalIntegrable_segment hf hC hh)
  simpa using h1.symm

/-! ### Passing to the limit -/

/-- The segment formula for the limit: if `f n` are differentiable with derivatives `f' n`
bounded by `C` on a ball inside `U`, `f n → g` and `f' n → g'` pointwise on `U`, then
`g (z + h) - g z = ∫₀¹ g' (z + t h) h dt`. -/
theorem bpz_sub_eq_integral_of_tendsto_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℕ → ℂ → F} {f' : ℕ → ℂ → (ℂ →L[ℝ] F)} {g : ℂ → F}
    {g' : ℂ → (ℂ →L[ℝ] F)} {U : Set ℂ} {z h : ℂ} {r C : ℝ}
    (hf : ∀ n, ∀ w ∈ U, HasFDerivAt (f n) (f' n w) w)
    (hlim : ∀ w ∈ U, Tendsto (fun n => f n w) atTop (𝓝 (g w)))
    (hlim' : ∀ w ∈ U, Tendsto (fun n => f' n w) atTop (𝓝 (g' w)))
    (hrU : Metric.ball z r ⊆ U) (hC : ∀ n, ∀ w ∈ Metric.ball z r, ‖f' n w‖ ≤ C)
    (hh : ‖h‖ < r) :
    g (z + h) - g z = ∫ t in (0 : ℝ)..1, g' (z + t • h) h := by
  have hfb : ∀ n, ∀ w ∈ Metric.ball z r, HasFDerivAt (f n) (f' n w) w :=
    fun n w hw => hf n w (hrU hw)
  have hz : z ∈ U := hrU (Metric.mem_ball_self (lt_of_le_of_lt (norm_nonneg h) hh))
  have hzh : z + h ∈ U := by
    refine hrU ?_
    simpa using bpz_segment_mem_ball (z := z) (t := 1) hh (by simp)
  have hL1 : Tendsto (fun n => ∫ t in (0 : ℝ)..1, f' n (z + t • h) h) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g' (z + t • h) h)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => C * ‖h‖) (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
      intervalIntegrable_const (Eventually.of_forall fun t ht => ?_)
    · exact bpz_aestronglyMeasurable_segment (hfb n) hh
    · refine Eventually.of_forall fun t ht => ?_
      have hmem := bpz_segment_mem_ball (z := z) hh (Set.uIoc_subset_uIcc ht)
      calc ‖f' n (z + t • h) h‖ ≤ ‖f' n (z + t • h)‖ * ‖h‖ := (f' n (z + t • h)).le_opNorm h
        _ ≤ C * ‖h‖ := mul_le_mul_of_nonneg_right (hC n _ hmem) (norm_nonneg h)
    · have hmem := bpz_segment_mem_ball (z := z) hh (Set.uIoc_subset_uIcc ht)
      exact ((ContinuousLinearMap.apply ℝ F h).continuous.tendsto _).comp (hlim' _ (hrU hmem))
  have hL2 : Tendsto (fun n => ∫ t in (0 : ℝ)..1, f' n (z + t • h) h) atTop
      (𝓝 (g (z + h) - g z)) := by
    refine ((hlim _ hzh).sub (hlim _ hz)).congr fun n => ?_
    exact bpz_segment_ftc (hfb n) (hC n) hh
  exact tendsto_nhds_unique hL2 hL1

/-- A pointwise limit of differentiable functions whose derivatives converge pointwise, with
local uniform bounds, to a continuous limit, is differentiable with the limit derivative. -/
theorem bpz_hasFDerivAt_of_tendsto_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℕ → ℂ → F} {f' : ℕ → ℂ → (ℂ →L[ℝ] F)} {g : ℂ → F}
    {g' : ℂ → (ℂ →L[ℝ] F)} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ n, ∀ z ∈ U, HasFDerivAt (f n) (f' n z) z)
    (hlim : ∀ z ∈ U, Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (hlim' : ∀ z ∈ U, Tendsto (fun n => f' n z) atTop (𝓝 (g' z)))
    (hbd : ∀ z ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ n, ∀ w ∈ Metric.ball z r, ‖f' n w‖ ≤ C)
    (hcont : ContinuousOn g' U) :
    ∀ z ∈ U, HasFDerivAt g (g' z) z := by
  intro z hz
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨r₁, hr₁, C, hC⟩ := hbd z hz
  set r : ℝ := min r₀ r₁ with hr
  have hrpos : 0 < r := lt_min hr₀ hr₁
  have hrU : Metric.ball z r ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hr₀U
  have hrC : ∀ n, ∀ w ∈ Metric.ball z r, ‖f' n w‖ ≤ C := fun n w hw =>
    hC n w (Metric.ball_subset_ball (min_le_right _ _) hw)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ρ hρ
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (hU.mem_nhds hz)) ρ hρ
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min hδ hrpos)] with h hh
  rw [mem_ball_zero_iff, lt_min_iff] at hh
  obtain ⟨hhδ, hhr⟩ := hh
  have hseg : ∀ t ∈ Set.uIcc (0 : ℝ) 1, z + t • h ∈ U := fun t ht =>
    hrU (bpz_segment_mem_ball hhr ht)
  have hform := bpz_sub_eq_integral_of_tendsto_deriv hf hlim hlim' hrU hrC hhr
  have hcts : ContinuousOn (fun t : ℝ => g' (z + t • h) h) (Set.uIcc (0 : ℝ) 1) := by
    have hγ : Continuous fun t : ℝ => z + t • h := by fun_prop
    exact (ContinuousLinearMap.apply ℝ F h).continuous.comp_continuousOn
      (hcont.comp hγ.continuousOn hseg)
  have hint : g (z + h) - g z - g' z h =
      ∫ t in (0 : ℝ)..1, (g' (z + t • h) h - g' z h) := by
    rw [intervalIntegral.integral_sub (hcts.intervalIntegrable) intervalIntegrable_const,
      intervalIntegral.integral_const, ← hform]
    simp
  rw [hint]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖g' (z + t • h) h - g' z h‖ ≤ ρ * ‖h‖ := by
    intro t ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc ht
    have hdist : dist (z + t • h) z < δ := by
      have := bpz_segment_mem_ball (z := z) (r := δ) hhδ ht'
      rwa [Metric.mem_ball] at this
    have hg := hδg hdist
    rw [dist_eq_norm] at hg
    calc ‖g' (z + t • h) h - g' z h‖ = ‖(g' (z + t • h) - g' z) h‖ := by
          rw [sub_apply]
      _ ≤ ‖g' (z + t • h) - g' z‖ * ‖h‖ := (g' (z + t • h) - g' z).le_opNorm h
      _ ≤ ρ * ‖h‖ := mul_le_mul_of_nonneg_right hg.le (norm_nonneg h)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa using this

/-! ### Wirtinger derivatives of real functions -/

/-- The Wirtinger derivative of a real differentiable function. -/
theorem bpz_wirtingerZ_ofReal {T : ℂ → ℝ} {DT : ℂ →L[ℝ] ℝ} {z : ℂ} (h : HasFDerivAt T DT z) :
    wirtingerZ (fun w => (T w : ℂ)) z = ((DT 1 : ℂ) - Complex.I * (DT Complex.I : ℂ)) / 2 := by
  have h' : HasFDerivAt (fun w => (T w : ℂ)) (Complex.ofRealCLM.comp DT) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h
  rw [wirtingerZ, h'.fderiv]
  simp

/-- The second Wirtinger derivative of a real twice differentiable function. -/
theorem bpz_wirtingerZ_wirtingerZ_ofReal {T : ℂ → ℝ} {DT : ℂ → ℂ →L[ℝ] ℝ}
    {D2T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ} {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (h1 : ∀ w ∈ U, HasFDerivAt T (DT w) w) (h2 : HasFDerivAt DT D2T z) :
    wirtingerZ (wirtingerZ (fun w => (T w : ℂ))) z =
      ((D2T 1 1 : ℂ) - Complex.I * (D2T 1 Complex.I : ℂ) - Complex.I * (D2T Complex.I 1 : ℂ) -
        (D2T Complex.I Complex.I : ℂ)) / 4 := by
  have hev : wirtingerZ (fun w => (T w : ℂ)) =ᶠ[𝓝 z]
      fun w => ((DT w 1 : ℂ) - Complex.I * (DT w Complex.I : ℂ)) / 2 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact bpz_wirtingerZ_ofReal (h1 w hw)
  have hA : ∀ v : ℂ, HasFDerivAt (fun w => ((DT w v : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ v).comp D2T)) z := fun v =>
    Complex.ofRealCLM.hasFDerivAt.comp z ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z h2)
  have hG := ((hA 1).sub ((hA Complex.I).const_mul Complex.I)).const_mul (2⁻¹ : ℂ)
  have hG' : HasFDerivAt (fun w => ((DT w 1 : ℂ) - Complex.I * (DT w Complex.I : ℂ)) / 2)
      ((2⁻¹ : ℂ) • (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).comp D2T) -
        Complex.I • Complex.ofRealCLM.comp
          ((ContinuousLinearMap.apply ℝ ℝ Complex.I).comp D2T))) z := by
    convert hG using 2 with w
    simp [div_eq_inv_mul]
  rw [wirtingerZ, hev.fderiv_eq, hG'.fderiv]
  simp
  linear_combination (((D2T Complex.I Complex.I : ℝ) : ℂ) / 4) * Complex.I_sq

/-! ### A `C²` criterion -/

/-- A C² criterion on an open set. -/
theorem bpz_contDiffOn_two_of {T : ℂ → ℝ} {DT : ℂ → ℂ →L[ℝ] ℝ}
    {D2T : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ} {U : Set ℂ} (hU : IsOpen U)
    (h1 : ∀ w ∈ U, HasFDerivAt T (DT w) w) (h2 : ∀ w ∈ U, HasFDerivAt DT (D2T w) w)
    (h3 : ContinuousOn D2T U) : ContDiffOn ℝ 2 T U := by
  have hev : ∀ w ∈ U, fderiv ℝ T =ᶠ[𝓝 w] DT := fun w hw => by
    filter_upwards [hU.mem_nhds hw] with y hy using (h1 y hy).fderiv
  have hd2 : ∀ w ∈ U, HasFDerivAt (fderiv ℝ T) (D2T w) w := fun w hw =>
    (h2 w hw).congr_of_eventuallyEq (hev w hw)
  have hC1 : ContDiffOn ℝ 1 (fderiv ℝ T) U := by
    have h0 : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (fderiv ℝ T) U := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun w hw => (hd2 w hw).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      rw [contDiffOn_zero]
      exact h3.congr fun w hw => (hd2 w hw).fderiv
    simpa using h0
  have h2' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) T U := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨fun w hw => (h1 w hw).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), hC1⟩
  simpa [one_add_one_eq_two] using h2'

end DOZZ.Proofs
