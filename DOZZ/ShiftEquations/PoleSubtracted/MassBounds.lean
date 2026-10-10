/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.Masses
public import DOZZ.GMC.SharpMoments.SeibergWeight

/-!
# Pointwise bounds on the pole-subtracted masses

Deterministic comparisons used by the moment estimates of [KRV, §10.2]: off the poles the pole
weight is the two-point Coulomb weight; it is bounded off the two balls and on the unit disk; the
zero tilt is at most `e^{γ a⁺ n}` on `C_n`; the regular part and the annular increment of the cutoff
tilted mass are controlled by the total mass and by the mass of `B(0, e^{-n})`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Elementary helpers -/

private theorem one_le_norm_sub_two_aux {x : ℂ} (hx : ‖x‖ ≤ 1) : 1 ≤ ‖x - 2‖ := by
  have h := norm_sub_le x (x - 2)
  rw [sub_sub_cancel] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  linarith

private theorem one_le_norm_add_two_aux {x : ℂ} (hx : ‖x‖ ≤ 1) : 1 ≤ ‖x + 2‖ := by
  have h := norm_sub_le (x + 2) x
  rw [add_sub_cancel_left] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  linarith

private theorem ofReal_div_le_one_aux {t u : ℝ} (hu : 0 < u) (h : t ≤ u) :
    ENNReal.ofReal t / ENNReal.ofReal u ≤ 1 := by
  rw [← ENNReal.ofReal_div_of_pos hu]
  exact ENNReal.ofReal_le_one.mpr ((div_le_one₀ hu).mpr h)

private theorem exp_neg_natCast_le_one_aux (n : ℕ) : Real.exp (-(n : ℝ)) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))

/-- A set integral of a product of two pointwise-bounded factors is at most the product of the
bounds times the measure of the set. -/
private theorem setLIntegral_mul_le_aux {s : Set ℂ} {f g : ℂ → ℝ≥0∞} {c d : ℝ≥0∞}
    (μ : Measure ℂ) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x ≤ c) (hg : ∀ x ∈ s, g x ≤ d) :
    ∫⁻ x in s, f x * g x ∂μ ≤ c * d * μ s := by
  calc ∫⁻ x in s, f x * g x ∂μ ≤ ∫⁻ _ in s, c * d ∂μ :=
        setLIntegral_mono' hs fun x hx => mul_le_mul' (hf x hx) (hg x hx)
    _ = c * d * μ s := setLIntegral_const _ _

/-- The integral of the pole weight over any set is at most the total mass at zero charge. -/
private theorem setLIntegral_poleWeight_le_aux (γ η : ℝ) (s : Set ℂ) (μ : Measure ℂ) :
    ∫⁻ x in s, poleWeight γ η x ∂μ ≤
      poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ := by
  rw [poleTotalMass_eq]
  simp_rw [zeroTilt_zero, one_mul]
  exact setLIntegral_le_lintegral _ _

/-- A uniform bound `c` for the zero tilt on `C_n` bounds the cutoff tilted mass by `c` times the
total mass at zero charge. -/
private theorem cutoffTiltedMass_le_mul_total_aux {γ η a : ℝ} {c : ℝ≥0∞} (n : ℕ)
    (μ : Measure ℂ) (h : ∀ x ∈ cutoffRegion n, zeroTilt γ a x ≤ c) :
    cutoffTiltedMass γ η a n μ ≤
      c * poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ := by
  unfold cutoffTiltedMass
  calc ∫⁻ x in cutoffRegion n, zeroTilt γ a x * poleWeight γ η x ∂μ
      ≤ ∫⁻ x in cutoffRegion n, c * poleWeight γ η x ∂μ :=
        setLIntegral_mono' (measurableSet_cutoffRegion n) fun x hx => mul_le_mul' (h x hx) le_rfl
    _ = c * ∫⁻ x in cutoffRegion n, poleWeight γ η x ∂μ :=
        lintegral_const_mul _ (measurable_poleWeight γ η)
    _ ≤ c * poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ :=
        mul_le_mul' le_rfl (setLIntegral_poleWeight_le_aux γ η _ μ)

/-- On the closed unit disk the pole weight is at most `1`. -/
theorem poleWeight_le_one_of_norm_le_one {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hηγ : η ≤ 2 / γ) {x : ℂ} (hx : ‖x‖ ≤ 1) : poleWeight γ η x ≤ 1 := by
  have hnp : normPlus x = 1 := max_eq_left hx
  have h1 := one_le_norm_sub_two_aux hx
  have h2 := one_le_norm_add_two_aux hx
  have hr1 : ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x - 2‖ ≤ 1 :=
    ofReal_div_le_one_aux (by linarith) (by rw [hnp]; exact h1)
  have hr2 : ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x + 2‖ ≤ 1 :=
    ofReal_div_le_one_aux (by linarith) (by rw [hnp]; exact h2)
  have he1 : 0 ≤ γ * (2 / γ + η) :=
    mul_nonneg hγ.le (add_nonneg (div_nonneg two_pos.le hγ.le) hη)
  have he2 : 0 ≤ γ * (2 / γ - η) := mul_nonneg hγ.le (sub_nonneg.mpr hηγ)
  unfold poleWeight
  calc _ ≤ (1 : ℝ≥0∞) * 1 :=
        mul_le_mul' (ENNReal.rpow_le_one hr1 he1) (ENNReal.rpow_le_one hr2 he2)
    _ = 1 := mul_one 1

/-- On `C_n` the zero tilt is at most `e^{γ a⁺ n}`. -/
theorem zeroTilt_le_exp_max {γ a : ℝ} (hγ : 0 < γ) {n : ℕ} {x : ℂ}
    (hx : x ∈ cutoffRegion n) : zeroTilt γ a x ≤ ENNReal.ofReal (Real.exp (γ * max a 0 * n)) := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    refine (zeroTilt_le_one hγ ha x).trans ?_
    simp
  · rw [max_eq_left ha]
    exact zeroTilt_le_of_mem_cutoffRegion hγ ha hx

/-- Off the poles the pole weight is the two-point Coulomb weight. -/
theorem poleWeight_eq_coulombWeight (γ η : ℝ) {x : ℂ} (hx2 : x ≠ 2) (hx2' : x ≠ -2) :
    poleWeight γ η x = coulombWeight γ ![2 / γ + η, 2 / γ - η] ![2, -2] 0 x := by
  have h1 : 0 < ‖x - 2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx2)
  have h2 : 0 < ‖x + 2‖ := norm_pos_iff.mpr fun h => hx2' (add_eq_zero_iff_eq_neg.mp h)
  unfold poleWeight coulombWeight
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, mul_zero,
    ENNReal.rpow_eq_pow, ENNReal.rpow_zero, mul_one, ENNReal.ofReal_div_of_pos h1,
    ENNReal.ofReal_div_of_pos h2]

/-- Without atoms at the poles, the total mass at zero charge is a Coulomb mass. -/
theorem totalMass_zero_eq_coulombMass (γ η : ℝ) (μ : Measure ℂ) (h2 : μ {2} = 0)
    (h2' : μ {-2} = 0) :
    poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ =
      coulombMass γ μ ![2 / γ + η, 2 / γ - η] ![2, -2] 0 := by
  rw [poleTotalMass_eq, coulombMass_eq_lintegral_coulombWeight]
  have e1 : ∀ᵐ x ∂μ, x ≠ 2 := by
    rw [ae_iff]
    simpa using h2
  have e2 : ∀ᵐ x ∂μ, x ≠ -2 := by
    rw [ae_iff]
    simpa using h2'
  refine lintegral_congr_ae ?_
  filter_upwards [e1, e2] with x hx1 hx2
  rw [zeroTilt_zero, one_mul]
  exact poleWeight_eq_coulombWeight γ η hx1 hx2

/-- The total mass of a measure is the Coulomb mass with no roots. -/
theorem measure_univ_eq_coulombMass (γ : ℝ) (μ : Measure ℂ) :
    μ univ = coulombMass γ μ (![] : Fin 0 → ℝ) (![] : Fin 0 → ℂ) 0 := by
  rw [coulombMass_eq_lintegral_coulombWeight, ← lintegral_one]
  refine lintegral_congr fun x => ?_
  unfold coulombWeight
  simp

/-- The local mass is at most the total mass at zero charge. -/
theorem localMass_le_totalMass (γ η : ℝ) (μ : Measure ℂ) :
    poleLocalMass γ (2 / γ + η) (2 / γ - η) μ ≤
      poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ := by
  rw [poleLocalMass_eq]
  exact setLIntegral_poleWeight_le_aux γ η _ μ

/-- The local mass dominates a ninth of the mass of `B(2, 1/2)`. -/
theorem ball_le_localMass {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ)
    (μ : Measure ℂ) :
    (1 / 9 : ℝ≥0∞) * μ (Metric.ball 2 (1 / 2)) ≤
      poleLocalMass γ (2 / γ + η) (2 / γ - η) μ := by
  rw [poleLocalMass_eq]
  have hsub : Metric.ball (2 : ℂ) (1 / 2) ⊆ poleBalls := fun x hx =>
    Or.inl (Metric.ball_subset_ball (by norm_num) hx)
  calc (1 / 9 : ℝ≥0∞) * μ (Metric.ball 2 (1 / 2))
      = ∫⁻ _ in Metric.ball (2 : ℂ) (1 / 2), (1 / 9 : ℝ≥0∞) ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Metric.ball (2 : ℂ) (1 / 2), poleWeight γ η x ∂μ :=
        setLIntegral_mono (measurable_poleWeight γ η) fun x hx =>
          poleWeight_ge_of_mem_ball_two hγ hη hηγ hx
    _ ≤ ∫⁻ x in poleBalls, poleWeight γ η x ∂μ := lintegral_mono_set hsub

/-- A nonpositive zero charge does not increase the mass. -/
theorem cutoffTiltedMass_le_totalMass_zero {γ η a : ℝ} (hγ : 0 < γ) (ha : a ≤ 0) (n : ℕ)
    (μ : Measure ℂ) :
    cutoffTiltedMass γ η a n μ ≤ poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ := by
  have h := cutoffTiltedMass_le_mul_total_aux (η := η) n μ
    (fun x _ => zeroTilt_le_one hγ ha x)
  rwa [one_mul] at h

/-- Every cutoff tilted mass is at most `e^{γ a⁺ n}` times the total mass at zero charge. -/
theorem cutoffTiltedMass_le_exp_mul_totalMass_zero {γ η : ℝ} (a : ℝ) (hγ : 0 < γ) (n : ℕ)
    (μ : Measure ℂ) :
    cutoffTiltedMass γ η a n μ ≤
      ENNReal.ofReal (Real.exp (γ * max a 0 * n)) *
        poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ :=
  cutoffTiltedMass_le_mul_total_aux n μ fun _ hx => zeroTilt_le_exp_max hγ hx

/-- The regular part of the cutoff tilted mass is at most `81 e^{γ a⁺ n} μ(ℂ)`. -/
theorem regularMass_le {γ η : ℝ} (a : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ) (n : ℕ)
    (μ : Measure ℂ) :
    ∫⁻ x in cutoffRegion n \ poleBalls, zeroTilt γ a x * poleWeight γ η x ∂μ ≤
      81 * ENNReal.ofReal (Real.exp (γ * max a 0 * n)) * μ univ := by
  have h := setLIntegral_mul_le_aux μ
    ((measurableSet_cutoffRegion n).diff measurableSet_poleBalls)
    (fun x hx => zeroTilt_le_exp_max (a := a) hγ hx.1)
    (fun x hx => poleWeight_le_of_notMem_poleBalls hγ hη hηγ hx.2)
  refine h.trans ?_
  rw [mul_comm (ENNReal.ofReal _) 81]
  exact mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))

/-- The annular increment is at most `e^{γ a⁺ (n+1)} μ(B(0, e^{-n}))`. -/
theorem annulusMass_le {γ η : ℝ} (a : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ) (n : ℕ)
    (μ : Measure ℂ) :
    ∫⁻ x in cutoffRegion (n + 1) \ cutoffRegion n, zeroTilt γ a x * poleWeight γ η x ∂μ ≤
      ENNReal.ofReal (Real.exp (γ * max a 0 * (n + 1))) *
        μ (Metric.ball 0 (Real.exp (-(n : ℝ)))) := by
  have hf : ∀ x ∈ cutoffRegion (n + 1) \ cutoffRegion n,
      zeroTilt γ a x ≤ ENNReal.ofReal (Real.exp (γ * max a 0 * (n + 1))) := by
    intro x hx
    have h := zeroTilt_le_exp_max (a := a) hγ hx.1
    push_cast at h
    exact h
  have hg : ∀ x ∈ cutoffRegion (n + 1) \ cutoffRegion n, poleWeight γ η x ≤ 1 := by
    intro x hx
    have hx2 : ¬ Real.exp (-(n : ℝ)) ≤ ‖x‖ := hx.2
    exact poleWeight_le_one_of_norm_le_one hγ hη hηγ
      ((not_le.mp hx2).le.trans (exp_neg_natCast_le_one_aux n))
  have h := setLIntegral_mul_le_aux μ
    ((measurableSet_cutoffRegion (n + 1)).diff (measurableSet_cutoffRegion n)) hf hg
  refine h.trans ?_
  rw [mul_one]
  refine mul_le_mul' le_rfl (measure_mono fun x hx => ?_)
  have hx2 : ¬ Real.exp (-(n : ℝ)) ≤ ‖x‖ := hx.2
  rw [Metric.mem_ball, dist_zero_right]
  exact not_le.mp hx2

end DOZZ.Proofs

end
