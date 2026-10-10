/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.Masses
public import DOZZ.Statements.Correlations.LocalSingularMass
public import DOZZ.Statements.Correlations.UniformPositiveC1Family

/-!
# The local mass as two local singular masses

On `B(2,1)` the two-pole weight is `F₂(x) |x - 2|^{-γα₂}` with the smooth positive factor
`F₂(x) = |x|^{γα₂} (|x|/|x+2|)^{γα₃}`, and symmetrically at `-2`. Clamping `|x|` and `|x ± 2|`
outside the balls makes the factors globally bounded without changing them near the poles, so they
form the uniform positive `C¹` families required by the tail estimates. Their values at the poles
are `F₂(2) = 2^{2γη}` and `F₃(-2) = 2^{-2γη}`; these are the separated-insertion position factors
that cancel in the two residues (erratum K26, see docs/ERRATA-AND-DEVIATIONS.md).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The smooth factor of the local mass at the pole `2`, clamped to be globally bounded. -/
noncomputable def poleFactorTwo (γ η : ℝ) (x : ℂ) : ℝ :=
  min ‖x‖ 3 ^ (γ * (2 / γ + η)) * (min ‖x‖ 3 / max ‖x + 2‖ 1) ^ (γ * (2 / γ - η))

/-- The smooth factor of the local mass at the pole `-2`, clamped to be globally bounded. -/
noncomputable def poleFactorNegTwo (γ η : ℝ) (x : ℂ) : ℝ :=
  min ‖x‖ 3 ^ (γ * (2 / γ - η)) * (min ‖x‖ 3 / max ‖x - 2‖ 1) ^ (γ * (2 / γ + η))

/-! ### Exponent arithmetic -/

private theorem mul_two_div_add {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    γ * (2 / γ + η) = 2 + γ * η := by
  field_simp

private theorem mul_two_div_sub {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    γ * (2 / γ - η) = 2 - γ * η := by
  field_simp

private theorem mul_le_two_of_le_two_div {γ η : ℝ} (hγ : 0 < γ) (hηγ : η ≤ 2 / γ) :
    γ * η ≤ 2 := by
  have h := mul_le_mul_of_nonneg_left hηγ hγ.le
  rwa [mul_div_cancel₀ _ hγ.ne'] at h

private theorem exponent_add_nonneg {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) :
    0 ≤ γ * (2 / γ + η) := by
  rw [mul_two_div_add hγ]
  linarith [mul_nonneg hγ.le hη]

private theorem exponent_sub_nonneg {γ η : ℝ} (hγ : 0 < γ) (hηγ : η ≤ 2 / γ) :
    0 ≤ γ * (2 / γ - η) := by
  rw [mul_two_div_sub hγ]
  linarith [mul_le_two_of_le_two_div hγ hηγ]

/-! ### The values at the poles -/

private theorem two_rpow_mul_half_rpow (a b : ℝ) : (2 : ℝ) ^ a * (2 / 4) ^ b = 2 ^ (a - b) := by
  have h : (2 / 4 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [h, Real.inv_rpow (by norm_num), Real.rpow_sub (by norm_num), div_eq_mul_inv]

theorem poleFactorTwo_two {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    poleFactorTwo γ η 2 = 2 ^ (2 * γ * η) := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h4 : ‖(2 : ℂ) + 2‖ = 4 := by norm_num
  unfold poleFactorTwo
  rw [h2, h4, min_eq_left (by norm_num : (2 : ℝ) ≤ 3),
    max_eq_left (by norm_num : (1 : ℝ) ≤ 4), mul_two_div_add hγ, mul_two_div_sub hγ,
    two_rpow_mul_half_rpow]
  congr 1
  ring

theorem poleFactorNegTwo_negTwo {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    poleFactorNegTwo γ η (-2) = 2 ^ (-(2 * γ * η)) := by
  have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  have h4 : ‖(-2 : ℂ) - 2‖ = 4 := by norm_num
  unfold poleFactorNegTwo
  rw [h2, h4, min_eq_left (by norm_num : (2 : ℝ) ≤ 3),
    max_eq_left (by norm_num : (1 : ℝ) ≤ 4), mul_two_div_add hγ, mul_two_div_sub hγ,
    two_rpow_mul_half_rpow]
  congr 1
  ring

/-! ### The pointwise identity near a pole -/

private theorem ennrpow_pole_eq {p r s a b : ℝ} (hp : 0 < p) (hr : 0 ≤ r) (hs : 0 < s)
    (ha : 0 ≤ a) :
    ENNReal.rpow (ENNReal.ofReal p / ENNReal.ofReal r) a *
        ENNReal.rpow (ENNReal.ofReal p / ENNReal.ofReal s) b =
      ENNReal.ofReal (p ^ a * (p / s) ^ b) * ENNReal.rpow (ENNReal.ofReal r) (-a) := by
  have hps : 0 < p / s := div_pos hp hs
  have hfin : ENNReal.rpow (ENNReal.ofReal p / ENNReal.ofReal s) b =
      ENNReal.ofReal ((p / s) ^ b) := by
    rw [ENNReal.rpow_eq_pow, ← ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_rpow_of_pos hps]
  rw [hfin]
  rcases hr.eq_or_lt with hr0 | hrpos
  · subst hr0
    rcases ha.eq_or_lt with ha0 | hapos
    · subst ha0
      simp [ENNReal.rpow_eq_pow]
    · have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
      have hq0 : ENNReal.ofReal ((p / s) ^ b) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hps b)).ne'
      have hX : ENNReal.ofReal (p ^ a * (p / s) ^ b) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos hp a)
          (Real.rpow_pos_of_pos hps b))).ne'
      rw [ENNReal.ofReal_zero, ENNReal.div_zero hp0, ENNReal.rpow_eq_pow,
        ENNReal.top_rpow_of_pos hapos, ENNReal.rpow_eq_pow,
        ENNReal.zero_rpow_of_neg (neg_neg_of_pos hapos), ENNReal.top_mul hq0,
        ENNReal.mul_top hX]
  · have hpr : 0 < p / r := div_pos hp hrpos
    rw [ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow, ← ENNReal.ofReal_div_of_pos hrpos,
      ENNReal.ofReal_rpow_of_pos hpr, ENNReal.ofReal_rpow_of_pos hrpos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hpr.le a),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hp.le a) (Real.rpow_nonneg hps.le b))]
    congr 1
    rw [Real.div_rpow hp.le hrpos.le, Real.rpow_neg hrpos.le]
    ring

private theorem norm_bounds {z x : ℂ} (hz : ‖z‖ = 2) {r : ℝ} (hx : ‖x - z‖ < r) :
    2 - r < ‖x‖ ∧ ‖x‖ < 2 + r ∧ 4 - r < ‖x + z‖ := by
  have h1 := norm_sub_norm_le z x
  have h2 := norm_sub_norm_le x z
  have h3 : ‖(x + z) - (x - z)‖ ≤ ‖x + z‖ + ‖x - z‖ := norm_sub_le _ _
  have e : (x + z) - (x - z) = 2 * z := by ring
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [e, norm_mul, hz, h2'] at h3
  rw [norm_sub_rev, hz] at h1
  rw [hz] at h2
  refine ⟨by linarith, by linarith, by linarith⟩

private theorem localSingularMass_eq_setLIntegral {Ω : Type*} (M : Ω → Measure ℂ) (F : ℂ → ℝ)
    (z : ℂ) (γ α : ℝ) (ω : Ω) :
    localSingularMass M F z γ α ω =
      ∫⁻ x in Metric.ball z 1,
        ENNReal.ofReal (F x) * ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) ∂(M ω) := by
  unfold localSingularMass
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Metric.ball z 1
  · simp [hx]
  · simp [hx]

private theorem poleWeight_eq_of_mem_ball_two {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    {x : ℂ} (hx : x ∈ Metric.ball (2 : ℂ) 1) :
    poleWeight γ η x = ENNReal.ofReal (poleFactorTwo γ η x) *
      ENNReal.rpow (ENNReal.ofReal ‖x - 2‖) (-γ * (2 / γ + η)) := by
  have hx' : ‖x - 2‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  obtain ⟨h1, h2, h3⟩ := norm_bounds (z := 2) (by norm_num) hx'
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith)
  have hmin : min ‖x‖ 3 = ‖x‖ := min_eq_left (by linarith)
  have hmax : max ‖x + 2‖ 1 = ‖x + 2‖ := max_eq_left (by linarith)
  unfold poleWeight poleFactorTwo
  rw [hnp, hmin, hmax, neg_mul]
  exact ennrpow_pole_eq (by linarith) (norm_nonneg _) (by linarith) (exponent_add_nonneg hγ hη)

private theorem poleWeight_eq_of_mem_ball_neg_two {γ η : ℝ} (hγ : 0 < γ)
    (hηγ : η ≤ 2 / γ) {x : ℂ} (hx : x ∈ Metric.ball (-2 : ℂ) 1) :
    poleWeight γ η x = ENNReal.ofReal (poleFactorNegTwo γ η x) *
      ENNReal.rpow (ENNReal.ofReal ‖x - -2‖) (-γ * (2 / γ - η)) := by
  have hx' : ‖x - -2‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  obtain ⟨h1, h2, h3⟩ := norm_bounds (z := -2) (by norm_num) hx'
  have e : x + -2 = x - 2 := by ring
  have e' : x - -2 = x + 2 := by ring
  rw [e] at h3
  rw [e'] at hx' ⊢
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith)
  have hmin : min ‖x‖ 3 = ‖x‖ := min_eq_left (by linarith)
  have hmax : max ‖x - 2‖ 1 = ‖x - 2‖ := max_eq_left (by linarith)
  unfold poleWeight poleFactorNegTwo
  rw [hnp, hmin, hmax, neg_mul, mul_comm]
  exact ennrpow_pole_eq (by linarith) (norm_nonneg _) (by linarith) (exponent_sub_nonneg hγ hηγ)

private theorem disjoint_balls : Disjoint (Metric.ball (2 : ℂ) 1) (Metric.ball (-2 : ℂ) 1) := by
  refine Metric.ball_disjoint_ball ?_
  rw [dist_eq_norm]
  have e : (2 : ℂ) - -2 = 4 := by ring
  rw [e]
  norm_num

/-- **The local mass is the sum of the two local singular masses.** -/
theorem poleLocalMass_eq_localSingularMass {Ω : Type*} (M : Ω → Measure ℂ) {γ η : ℝ}
    (hγ : 0 < γ) (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ) (ω : Ω) :
    poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) =
      localSingularMass M (poleFactorTwo γ η) 2 γ (2 / γ + η) ω +
        localSingularMass M (poleFactorNegTwo γ η) (-2) γ (2 / γ - η) ω := by
  rw [poleLocalMass_eq, poleBalls, lintegral_union Metric.isOpen_ball.measurableSet
    disjoint_balls, localSingularMass_eq_setLIntegral, localSingularMass_eq_setLIntegral]
  congr 1
  · exact setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
      fun x hx => poleWeight_eq_of_mem_ball_two hγ hη hx
  · exact setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
      fun x hx => poleWeight_eq_of_mem_ball_neg_two hγ hηγ hx

/-! ### The uniform positive `C¹` families -/

private theorem exists_fderiv_bound {F : ℂ → ℝ} {z : ℂ}
    (hF : ContDiffOn ℝ 1 F (Metric.ball z (1 / 2))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w ∈ Metric.closedBall z (1 / 4), ‖fderiv ℝ F w‖ ≤ D := by
  have hcont : ContinuousOn (fderiv ℝ F) (Metric.ball z (1 / 2)) :=
    hF.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl
  have hsub : Metric.closedBall z (1 / 4) ⊆ Metric.ball z (1 / 2) :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall z (1 / 4)).exists_bound_of_continuousOn (hcont.mono hsub)
  exact ⟨max C 0, le_max_right _ _, fun w hw => (hC w hw).trans (le_max_left _ _)⟩

private theorem clamp_nonneg (a b : ℝ) (z x : ℂ) :
    0 ≤ min ‖x‖ 3 ^ a * (min ‖x‖ 3 / max ‖x + z‖ 1) ^ b := by
  have h0 : 0 ≤ min ‖x‖ 3 := le_min (norm_nonneg x) (by norm_num)
  have h1 : 0 < max ‖x + z‖ 1 := lt_max_of_lt_right one_pos
  exact mul_nonneg (Real.rpow_nonneg h0 a) (Real.rpow_nonneg (div_nonneg h0 h1.le) b)

private theorem clamp_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z x : ℂ) :
    min ‖x‖ 3 ^ a * (min ‖x‖ 3 / max ‖x + z‖ 1) ^ b ≤ 3 ^ (a + b) := by
  have h0 : 0 ≤ min ‖x‖ 3 := le_min (norm_nonneg x) (by norm_num)
  have h1 : 1 ≤ max ‖x + z‖ 1 := le_max_right _ _
  have h3 : min ‖x‖ 3 ≤ 3 := min_le_right _ _
  have h4 : min ‖x‖ 3 / max ‖x + z‖ 1 ≤ 3 := (div_le_self h0 h1).trans h3
  have h5 : 0 ≤ min ‖x‖ 3 / max ‖x + z‖ 1 := div_nonneg h0 (zero_le_one.trans h1)
  rw [Real.rpow_add (by norm_num)]
  exact mul_le_mul (Real.rpow_le_rpow h0 h3 ha) (Real.rpow_le_rpow h5 h4 hb)
    (Real.rpow_nonneg h5 b) (Real.rpow_nonneg (by norm_num) a)

private theorem contDiffOn_clamp (a b : ℝ) {z : ℂ} (hz : ‖z‖ = 2) :
    ContDiffOn ℝ 1 (fun x : ℂ => min ‖x‖ 3 ^ a * (min ‖x‖ 3 / max ‖x + z‖ 1) ^ b)
      (Metric.ball z (1 / 2)) := by
  have hx : ∀ x ∈ Metric.ball z (1 / 2), 3 / 2 < ‖x‖ ∧ ‖x‖ < 5 / 2 ∧ 7 / 2 < ‖x + z‖ := by
    intro x hx
    have hx' : ‖x - z‖ < 1 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    obtain ⟨h1, h2, h3⟩ := norm_bounds hz hx'
    refine ⟨by linarith, by linarith, by linarith⟩
  have hcongr : ∀ x ∈ Metric.ball z (1 / 2),
      min ‖x‖ 3 ^ a * (min ‖x‖ 3 / max ‖x + z‖ 1) ^ b = ‖x‖ ^ a * (‖x‖ / ‖x + z‖) ^ b := by
    intro x hxb
    obtain ⟨h1, h2, h3⟩ := hx x hxb
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  refine ContDiffOn.congr ?_ hcongr
  intro x hxb
  obtain ⟨h1, h2, h3⟩ := hx x hxb
  have hn1 : ContDiffAt ℝ 1 (fun y : ℂ => ‖y‖) x :=
    contDiffAt_norm ℝ (norm_pos_iff.mp (by linarith))
  have hxz : x + z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn2 : ContDiffAt ℝ 1 (fun y : ℂ => ‖y + z‖) x :=
    (contDiffAt_id.add contDiffAt_const).norm ℝ hxz
  have hne1 : ‖x‖ ≠ 0 := by linarith
  have hne2 : ‖x + z‖ ≠ 0 := by linarith
  have hq : ContDiffAt ℝ 1 (fun y : ℂ => ‖y‖ / ‖y + z‖) x := hn1.fun_div hn2 hne2
  exact ((hn1.rpow_const_of_ne hne1).mul
    (hq.rpow_const_of_ne (div_ne_zero hne1 hne2))).contDiffWithinAt

private theorem uniform_of_clamp {a b : ℝ} {z : ℂ} {F : ℂ → ℝ}
    (hF : F = fun x : ℂ => min ‖x‖ 3 ^ a * (min ‖x‖ 3 / max ‖x + z‖ 1) ^ b)
    (hz : ‖z‖ = 2) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 4) (hlow : 1 / 16 ≤ F z)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ w ∈ Metric.closedBall z (1 / 4), ‖fderiv ℝ F w‖ ≤ D) :
    UniformPositiveC1Family {z} (fun _ => {F}) (1 / 4) 81 D (1 / 16) := by
  subst hF
  refine ⟨by norm_num, by norm_num, hD0, by norm_num, ?_⟩
  intro z' hz' F' hF'
  have hz'' : z' = z := hz'
  have hF'' : F' = fun x : ℂ => min ‖x‖ 3 ^ a * (min ‖x‖ 3 / max ‖x + z‖ 1) ^ b := hF'
  rw [hz'', hF'']
  refine ⟨by fun_prop, fun x => ⟨clamp_nonneg a b z x, ?_⟩, hlow, ?_, hD⟩
  · rw [abs_of_nonneg (clamp_nonneg a b z x)]
    calc _ ≤ (3 : ℝ) ^ (a + b) := clamp_le ha hb z x
      _ = 81 := by rw [hab]; norm_num
  · have e : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
    rw [e]
    exact contDiffOn_clamp a b hz

/-- **The two smooth factors form uniform positive `C¹` families** at the two poles, with
common constants. -/
theorem exists_uniformPositiveC1Family_poleFactors {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hηγ : η ≤ 2 / γ) :
    ∃ radius supBound derivBound lowerBound : ℝ,
      UniformPositiveC1Family {2} (fun _ => {poleFactorTwo γ η}) radius supBound derivBound
          lowerBound ∧
        UniformPositiveC1Family {-2} (fun _ => {poleFactorNegTwo γ η}) radius supBound
          derivBound lowerBound := by
  have ha := exponent_add_nonneg hγ hη
  have hb := exponent_sub_nonneg hγ hηγ
  have hab : γ * (2 / γ + η) + γ * (2 / γ - η) = 4 := by
    rw [mul_two_div_add hγ, mul_two_div_sub hγ]; ring
  have hF2 : poleFactorTwo γ η = fun x : ℂ => min ‖x‖ 3 ^ (γ * (2 / γ + η)) *
      (min ‖x‖ 3 / max ‖x + 2‖ 1) ^ (γ * (2 / γ - η)) := rfl
  have hF3 : poleFactorNegTwo γ η = fun x : ℂ => min ‖x‖ 3 ^ (γ * (2 / γ - η)) *
      (min ‖x‖ 3 / max ‖x + -2‖ 1) ^ (γ * (2 / γ + η)) := by
    funext x
    unfold poleFactorNegTwo
    rw [← sub_eq_add_neg]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hn3 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  have hsm2 : ContDiffOn ℝ 1 (poleFactorTwo γ η) (Metric.ball 2 (1 / 2)) := by
    rw [hF2]; exact contDiffOn_clamp _ _ hn2
  have hsm3 : ContDiffOn ℝ 1 (poleFactorNegTwo γ η) (Metric.ball (-2) (1 / 2)) := by
    rw [hF3]; exact contDiffOn_clamp _ _ hn3
  obtain ⟨D₂, hD₂0, hD₂⟩ := exists_fderiv_bound hsm2
  obtain ⟨D₃, hD₃0, hD₃⟩ := exists_fderiv_bound hsm3
  have hlow2 : 1 / 16 ≤ poleFactorTwo γ η 2 := by
    rw [poleFactorTwo_two hγ]
    exact (by norm_num : (1 / 16 : ℝ) ≤ 1).trans (Real.one_le_rpow (by norm_num) (by positivity))
  have hlow3 : 1 / 16 ≤ poleFactorNegTwo γ η (-2) := by
    rw [poleFactorNegTwo_negTwo hγ]
    calc (1 / 16 : ℝ) = 2 ^ (-4 : ℝ) := by norm_num
      _ ≤ 2 ^ (-(2 * γ * η)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine ⟨1 / 4, 81, max D₂ D₃, 1 / 16, ?_, ?_⟩
  · exact uniform_of_clamp hF2 hn2 ha hb hab hlow2 (le_max_of_le_left hD₂0)
      (fun w hw => (hD₂ w hw).trans (le_max_left _ _))
  · exact uniform_of_clamp hF3 hn3 hb ha (by linarith) hlow3 (le_max_of_le_right hD₃0)
      (fun w hw => (hD₃ w hw).trans (le_max_right _ _))

end DOZZ.Proofs

end
