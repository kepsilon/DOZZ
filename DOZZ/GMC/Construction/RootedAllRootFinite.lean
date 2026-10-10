/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCRootedMeasureFinite
public import DOZZ.GMC.SharpMoments.BallScaling
public import DOZZ.GMC.Construction.RootedSmallBallMoment

/-! All-root finiteness from sharp small-ball bounds, including the unit-circle boundary. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

private theorem rooted_density_le_local_weighted_bound
    (γ : ℝ) (hγ : 0 < γ) (u : ℂ) (r : ℝ) (hr : 0 < r)
    (x : ℂ) :
    ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) ≤
      ENNReal.ofReal ((normPlus u * (1 + ‖u‖ + r)) ^ (γ ^ 2)) *
      (Metric.ball u r).indicator
        (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x +
      ENNReal.ofReal
        ((normPlus u * (1 + (1 + ‖u‖) / r)) ^ (γ ^ 2)) := by
  let K : ℝ := normPlus u * (1 + (1 + ‖u‖) / r)
  have huPlus : 0 < normPlus u := by
    unfold normPlus
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  by_cases hxBall : x ∈ Metric.ball u r
  · rw [Set.indicator_of_mem hxBall]
    by_cases hxu : x = u
    · subst x
      simp [ENNReal.zero_rpow_of_neg, show -γ ^ 2 < 0 by nlinarith,
        ENNReal.mul_top, ENNReal.ofReal_eq_zero, Real.rpow_pos_of_pos,
        show 0 < normPlus u * (1 + ‖u‖ + r) by positivity]
    · have hd : 0 < ‖x - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu)
      have hx : normPlus x ≤ 1 + ‖u‖ + r := by
        unfold normPlus
        apply max_le
        · linarith [norm_nonneg u]
        · have ht := norm_add_le (x - u) u
          rw [sub_add_cancel] at ht
          have hb : ‖x - u‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hxBall
          linarith
      have hxpos : 0 < normPlus x := by unfold normPlus; positivity
      have heq : Real.exp (γ ^ 2 * gffKernel u x) =
          (normPlus u * normPlus x) ^ (γ ^ 2) * ‖x - u‖ ^ (-γ ^ 2) := by
        rw [Real.rpow_def_of_pos (mul_pos huPlus hxpos), Real.rpow_def_of_pos hd,
          ← Real.exp_add, gffKernel, Real.log_mul huPlus.ne' hxpos.ne', norm_sub_rev]
        congr 1
        ring
      rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← ENNReal.ofReal_rpow_of_pos hd]
      apply le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left hx huPlus.le) (sq_nonneg γ))) le_rfl)
      exact le_add_right le_rfl
  · have hdist : r ≤ ‖x - u‖ := by
      have hnot : ¬ dist x u < r := by simpa [Metric.mem_ball] using hxBall
      exact le_of_not_gt (by simpa [dist_eq_norm] using hnot)
    have hnormX : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
      calc
        ‖x‖ = ‖(x - u) + u‖ := by congr 1; abel
        _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
        _ = ‖u‖ + ‖x - u‖ := by ring
    have hplusX : normPlus x ≤ 1 + ‖u‖ + ‖x - u‖ := by
      unfold normPlus
      apply max_le
      · linarith [norm_nonneg u, norm_nonneg (x - u)]
      · linarith [norm_nonneg u, norm_nonneg (x - u), hnormX]
    have hratioOne : 1 ≤ ‖x - u‖ / r := (one_le_div hr).2 hdist
    have hfactor : 1 + ‖u‖ ≤ (‖x - u‖ / r) * (1 + ‖u‖) := by
      calc
        1 + ‖u‖ = 1 * (1 + ‖u‖) := by ring
        _ ≤ (‖x - u‖ / r) * (1 + ‖u‖) :=
          mul_le_mul_of_nonneg_right hratioOne (by positivity)
    have hplusBound : normPlus x ≤ ‖x - u‖ * (1 + (1 + ‖u‖) / r) := by
      calc
        normPlus x ≤ 1 + ‖u‖ + ‖x - u‖ := hplusX
        _ ≤ ‖x - u‖ + (‖x - u‖ / r) * (1 + ‖u‖) := by linarith
        _ = ‖x - u‖ * (1 + (1 + ‖u‖) / r) := by ring
    have hratio : normPlus u * normPlus x / ‖x - u‖ ≤ K := by
      have hdistPos : 0 < ‖x - u‖ := lt_of_lt_of_le hr hdist
      apply (div_le_iff₀ hdistPos).2
      calc
        normPlus u * normPlus x ≤
            normPlus u * (‖x - u‖ * (1 + (1 + ‖u‖) / r)) :=
          mul_le_mul_of_nonneg_left hplusBound huPlus.le
        _ = K * ‖x - u‖ := by dsimp [K]; ring
    have hdistPos : 0 < ‖x - u‖ := lt_of_lt_of_le hr hdist
    have hratioPos : 0 < normPlus u * normPlus x / ‖x - u‖ :=
      div_pos (mul_pos huPlus (by unfold normPlus; positivity)) hdistPos
    have hkernel : gffKernel u x =
        Real.log (normPlus u * normPlus x / ‖x - u‖) := by
      have hu0 : normPlus u ≠ 0 := huPlus.ne'
      have hx0 : normPlus x ≠ 0 := by
        unfold normPlus
        positivity
      have hd0 : ‖x - u‖ ≠ 0 := hdistPos.ne'
      rw [gffKernel, show ‖u - x‖ = ‖x - u‖ by simp [norm_sub_rev]]
      calc
        -Real.log ‖x - u‖ + Real.log (normPlus u) + Real.log (normPlus x) =
            Real.log (normPlus u) + Real.log (normPlus x) - Real.log ‖x - u‖ := by ring
        _ = Real.log (normPlus u * normPlus x) - Real.log ‖x - u‖ := by
          rw [← Real.log_mul hu0 hx0]
        _ = Real.log (normPlus u * normPlus x / ‖x - u‖) :=
          (Real.log_div (mul_ne_zero hu0 hx0) hd0).symm
    have hlog : Real.log (normPlus u * normPlus x / ‖x - u‖) ≤ Real.log K :=
      Real.log_le_log hratioPos hratio
    have hkernelBound : gffKernel u x ≤ Real.log K := by rw [hkernel]; exact hlog
    have hexpBound : Real.exp (γ ^ 2 * gffKernel u x) ≤ K ^ (γ ^ 2) := by
      calc
        Real.exp (γ ^ 2 * gffKernel u x) ≤ Real.exp (γ ^ 2 * Real.log K) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkernelBound (sq_nonneg γ))
        _ = K ^ (γ ^ 2) := by
          rw [show γ ^ 2 * Real.log K = Real.log K * γ ^ 2 by ring,
            ← Real.rpow_def_of_pos hK]
    simpa [hxBall] using ENNReal.ofReal_le_ofReal hexpBound


/-- Local insertion control implies finite rooted mass at an arbitrary root. -/
theorem isFiniteMeasure_rooted_of_local_mass_any_root
    (γ : ℝ) (hγ : 0 < γ) (u : ℂ) (r : ℝ) (hr : 0 < r)
    (μ : Measure ℂ) (hμ : IsFiniteMeasure μ)
    (hlocal : weightedGmcBallMass γ μ γ u r < ⊤) :
    IsFiniteMeasure (gmcRootedMeasure γ u μ) := by
  have hinsertionBase : Measurable (fun x : ℂ => ENNReal.ofReal ‖x - u‖) := by
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hinsertion : Measurable (fun x : ℂ =>
      ENNReal.rpow (ENNReal.ofReal ‖x - u‖) (-γ ^ 2)) :=
    ENNReal.continuous_rpow_const.measurable.comp hinsertionBase
  have hinsertionLocal : Measurable (fun x : ℂ =>
      (Metric.ball u r).indicator
        (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x) :=
    hinsertion.indicator Metric.isOpen_ball.measurableSet
  let C : ℝ≥0∞ := ENNReal.ofReal
    ((normPlus u * (1 + (1 + ‖u‖) / r)) ^ (γ ^ 2))
  let A : ℝ≥0∞ := ENNReal.ofReal ((normPlus u * (1 + ‖u‖ + r)) ^ (γ ^ 2))
  have htotalBound :
      ∫⁻ x, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) ∂μ ≤
        A * weightedGmcBallMass γ μ γ u r + C * μ Set.univ := by
    calc
      _ ≤ ∫⁻ x, A * (Metric.ball u r).indicator
              (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x + C ∂μ :=
        lintegral_mono fun x => by
          simpa [A, C] using rooted_density_le_local_weighted_bound γ hγ u r hr x
      _ = A * weightedGmcBallMass γ μ γ u r + C * μ Set.univ := by
        rw [lintegral_add_left (show Measurable (fun x : ℂ => A * (Metric.ball u r).indicator
            (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x) from
            measurable_const.mul hinsertionLocal),
          lintegral_const_mul _ hinsertionLocal, lintegral_indicator
          Metric.isOpen_ball.measurableSet, lintegral_const, weightedGmcBallMass]
        congr 2
        apply lintegral_congr
        intro x
        rw [show -γ ^ 2 = -γ * γ by ring]
  have hconstant : C * μ Set.univ < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ.measure_univ_lt_top
  have htotalFinite :
      (∫⁻ x, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) ∂μ) < ⊤ :=
    lt_of_le_of_lt htotalBound (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlocal, hconstant⟩)
  rw [gmcRootedMeasure]
  exact isFiniteMeasure_withDensity htotalFinite.ne


/-- Every root has a finite local insertion mass, including roots on the unit circle. -/
theorem ae_weighted_mass_finite_at_every_root
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (u : ℂ) :
    ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) γ u (1 / 8) < ⊤ := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨p, hp, hp1, hpRange⟩ := exists_subunit_order_below_gamma_insertion hγ hγ2
  let ξ : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  have he : 0 < ξ - γ * γ * p := by
    have hs := weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange
    have hid : γ * (Q γ - γ) * p - γ ^ 2 * p ^ 2 / 2 = ξ - γ * γ * p := by
      dsimp [ξ, Q]
      field_simp [ne_of_gt hγ]
      ring
    rwa [hid] at hs
  obtain ⟨C, hC, hball⟩ := gmc_ball_moment_sharp_upper_center P X hX γ hγ hγ2 M hM u p
    (lt_of_lt_of_le hpRange (min_le_left _ _))
  have hmoment := rooted_local_moment_of_ball_upper P M
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM)
    γ γ p ξ C (1 / 8) u hγ hγ hp (by norm_num) hp1 (by norm_num) he hball
  let f : ℂ → ℝ≥0∞ := (Metric.ball u (1 / 8)).indicator
    (fun x => ENNReal.rpow (ENNReal.ofReal ‖x - u‖) (-γ * γ))
  have hf : Measurable f := by
    apply Measurable.indicator
    · exact ENNReal.continuous_rpow_const.measurable.comp
        (ENNReal.measurable_ofReal.comp (by fun_prop))
    · exact Metric.isOpen_ball.measurableSet
  obtain ⟨N, hN, _, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hmeas : AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) γ u (1 / 8)) P := by
    apply ((Measure.measurable_lintegral hf).comp hN).aemeasurable.congr
    filter_upwards [hMN] with ω hω
    rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet, hω]
    rfl
  have hae := ae_lt_top' (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmeas)
    hmoment.ne
  filter_upwards [hae] with ω hω
  by_contra hn
  have ht : weightedGmcBallMass γ (M ω) γ u (1 / 8) = ⊤ := top_unique (not_lt.mp hn)
  change weightedGmcBallMass γ (M ω) γ u (1 / 8) ^ p < ⊤ at hω
  rw [ht, ENNReal.top_rpow_of_pos hp] at hω
  exact (lt_self_iff_false _).mp hω

/-- The inserted chaos measure is almost surely finite for every deterministic root. -/
theorem equatorGFF_rooted_measure_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (u : ℂ) :
    ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)) := by
  filter_upwards [ae_weighted_mass_finite_at_every_root P X hX γ hγ hγ2 M hM u] with ω hω
  exact isFiniteMeasure_rooted_of_local_mass_any_root γ hγ u (1 / 8) (by norm_num)
    (M ω) (hM.1 ω) hω

end DOZZ.Proofs
