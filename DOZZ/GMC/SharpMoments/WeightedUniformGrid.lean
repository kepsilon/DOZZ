/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency

/-! # Weighted local moments at the chart center, uniformly over compact parameter ranges

On disks of radius at most one the weighted mass is monotone in the charge, and a positive power
is controlled by one plus any larger power, so the moment at a given charge and order is at most
one plus the moment at a larger charge and order. A finite grid of charges, with spacing
proportional to the slack below the two thresholds, then reduces a bound uniform over a compact
charge range and over orders with that slack to finitely many finite moments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- On a disk of radius at most one the weighted mass increases with the charge. -/
theorem weightedGmcBallMass_mono_charge (μ : Measure ℂ) {γ : ℝ} (hγ : 0 ≤ γ) (z : ℂ) {ρ : ℝ}
    (hρ1 : ρ ≤ 1) {α α' : ℝ} (hαα' : α ≤ α') :
    weightedGmcBallMass γ μ α z ρ ≤ weightedGmcBallMass γ μ α' z ρ := by
  have hexp : -γ * α' ≤ -γ * α := by
    have := mul_le_mul_of_nonneg_left hαα' hγ
    linarith
  unfold weightedGmcBallMass
  apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hx1 : ENNReal.ofReal ‖x - z‖ ≤ 1 := ENNReal.ofReal_le_one.mpr (hx.le.trans hρ1)
  rw [ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx1 hexp

/-- A positive power is at most one plus any larger power. The name carries the prefix because
`DOZZ.Proofs.ennreal_rpow_le_one_add_rpow` is already declared in
`DOZZ/Brownian/Reflection/MassBlocks.lean`, with the weaker hypothesis `0 ≤ t`. -/
theorem weightedGrid_ennreal_rpow_le_one_add_rpow (x : ℝ≥0∞) {t t' : ℝ} (ht : 0 < t)
    (htt' : t ≤ t') : x ^ t ≤ 1 + x ^ t' := by
  rcases le_or_gt x 1 with hx | hx
  · exact (ENNReal.rpow_le_one hx ht.le).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le hx.le htt').trans le_add_self

/-- The moment at a smaller charge and order is at most one plus the moment at a larger charge
and order. -/
theorem weightedGrid_moment_le_one_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 ≤ γ) (z : ℂ) {ρ : ℝ}
    (hρ1 : ρ ≤ 1) {α α' t t' : ℝ} (hαα' : α ≤ α') (ht : 0 < t) (htt' : t ≤ t') :
    weightedGmcBallMoment P M γ α z ρ t ≤ 1 + weightedGmcBallMoment P M γ α' z ρ t' := by
  unfold weightedGmcBallMoment
  calc ∫⁻ ω, ENNReal.rpow (weightedGmcBallMass γ (M ω) α z ρ) t ∂P
      ≤ ∫⁻ ω, (1 + ENNReal.rpow (weightedGmcBallMass γ (M ω) α' z ρ) t') ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow]
        exact (ENNReal.rpow_le_rpow (weightedGmcBallMass_mono_charge (M ω) hγ z hρ1 hαα')
          ht.le).trans (weightedGrid_ennreal_rpow_le_one_add_rpow _ ht htt')
    _ = 1 + ∫⁻ ω, ENNReal.rpow (weightedGmcBallMass γ (M ω) α' z ρ) t' ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- The order kept at charge `b` below both thresholds, after reserving half of the slack `g`. -/
noncomputable def weightedGrid_order (γ g b : ℝ) : ℝ :=
  min (4 / γ ^ 2) (2 / γ * (Q γ - b)) - g / 2

/-- The kept order lies strictly below both thresholds. -/
theorem weightedGrid_order_lt {γ g : ℝ} (hg : 0 < g) (b : ℝ) :
    weightedGrid_order γ g b < min (4 / γ ^ 2) (2 / γ * (Q γ - b)) := by
  unfold weightedGrid_order
  linarith

/-- An order with slack `g` below both thresholds at the charge `α` stays below the kept order at
every charge `a'` less than `g * γ / 8` above `α`. -/
theorem weightedGrid_le_order {γ g α a' t : ℝ} (hγ : 0 < γ) (hg : 0 < g)
    (ha' : a' < α + g * γ / 8) (hbulk : t + g ≤ 4 / γ ^ 2)
    (hins : t + g ≤ 2 / γ * (Q γ - α)) : t ≤ weightedGrid_order γ g a' := by
  unfold weightedGrid_order
  have hγ0 : γ ≠ 0 := hγ.ne'
  have h2γ : 0 < 2 / γ := by positivity
  have hstep : 2 / γ * (Q γ - α) ≤ 2 / γ * (Q γ - a') + g / 4 := by
    have h1 : 2 / γ * (Q γ - α) ≤ 2 / γ * (Q γ - a' + g * γ / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) h2γ.le
    have h2 : 2 / γ * (Q γ - a' + g * γ / 8) = 2 / γ * (Q γ - a') + g / 4 := by
      field_simp
      ring
    linarith
  have hmin : t + g / 2 ≤ min (4 / γ ^ 2) (2 / γ * (Q γ - a')) :=
    le_min (by linarith) (by linarith)
  linarith

/-- Rounding up to the grid of mesh `h` moves a real number up by less than `h`. -/
theorem weightedGrid_ceil_mul_bounds {h : ℝ} (hh : 0 < h) (α : ℝ) :
    α ≤ (⌈α / h⌉ : ℝ) * h ∧ (⌈α / h⌉ : ℝ) * h < α + h := by
  have h1 : α / h ≤ (⌈α / h⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈α / h⌉ : ℝ) < α / h + 1 := Int.ceil_lt_add_one _
  have h3 : α / h * h = α := div_mul_cancel₀ α hh.ne'
  constructor
  · calc α = α / h * h := h3.symm
      _ ≤ (⌈α / h⌉ : ℝ) * h := mul_le_mul_of_nonneg_right h1 hh.le
  · calc (⌈α / h⌉ : ℝ) * h < (α / h + 1) * h := mul_lt_mul_of_pos_right h2 hh
      _ = α + h := by rw [add_mul, h3, one_mul]

/-- The grid index of a charge of absolute value at most `A` lies in a fixed finite range. -/
theorem weightedGrid_ceil_mem_Icc {h A α : ℝ} {n₀ : ℕ} (hh : 0 < h) (hn₀ : A / h + 1 ≤ n₀)
    (hα : |α| ≤ A) : ⌈α / h⌉ ∈ Finset.Icc (-(n₀ : ℤ)) n₀ := by
  obtain ⟨hαl, hαu⟩ := abs_le.mp hα
  have hu : α / h ≤ A / h := div_le_div_of_nonneg_right hαu hh.le
  have hl : -(A / h) ≤ α / h := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right hαl hh.le
  have h1 : α / h ≤ (⌈α / h⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈α / h⌉ : ℝ) < α / h + 1 := Int.ceil_lt_add_one _
  rw [Finset.mem_Icc]
  constructor
  · have : -(n₀ : ℝ) ≤ (⌈α / h⌉ : ℝ) := by linarith
    exact_mod_cast this
  · have : (⌈α / h⌉ : ℝ) ≤ (n₀ : ℝ) := by linarith
    exact_mod_cast this

/-- The grid summand: the center moment at charge `b` and the kept order when that order is
positive, and zero otherwise. -/
noncomputable def weightedGrid_term {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ ρ g b : ℝ) : ℝ≥0∞ :=
  if 0 < weightedGrid_order γ g b then
    weightedGmcBallMoment P M γ b 0 ρ (weightedGrid_order γ g b) else 0

/-- Every grid summand is finite. -/
theorem weightedGrid_term_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {ρ : ℝ} (hρ : 0 < ρ) {g : ℝ} (hg : 0 < g) (b : ℝ) :
    weightedGrid_term P M γ ρ g b < ⊤ := by
  unfold weightedGrid_term
  split_ifs with h
  · exact weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM b 0 ρ hρ _ h
      (weightedGrid_order_lt hg b)
  · exact ENNReal.zero_lt_top

/-- A center moment is at most one plus the grid summand at any charge within `g * γ / 8` above
it. -/
theorem weightedGrid_moment_le_term {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 < γ) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    {g : ℝ} (hg : 0 < g) {α a' t : ℝ} (hαa : α ≤ a') (ha' : a' < α + g * γ / 8) (ht : 0 < t)
    (hbulk : t + g ≤ 4 / γ ^ 2) (hins : t + g ≤ 2 / γ * (Q γ - α)) :
    weightedGmcBallMoment P M γ α 0 ρ t ≤ 1 + weightedGrid_term P M γ ρ g a' := by
  have hto : t ≤ weightedGrid_order γ g a' := weightedGrid_le_order hγ hg ha' hbulk hins
  have hpos : 0 < weightedGrid_order γ g a' := ht.trans_le hto
  unfold weightedGrid_term
  rw [ite_eq_left hpos]
  exact weightedGrid_moment_le_one_add P M hγ.le 0 hρ1 hαa ht hto

/-- Uniform bound for weighted local moments at the chart center over charges `|α| ≤ A` and
positive orders with a fixed slack `g` below both thresholds. -/
theorem weightedGmcBallMoment_uniform_center
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (A g : ℝ) (hg : 0 < g) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ α t : ℝ, |α| ≤ A → 0 < t → t + g ≤ 4 / γ ^ 2 →
      t + g ≤ 2 / γ * (Q γ - α) → weightedGmcBallMoment P M γ α 0 ρ t ≤ K := by
  let _ : IsProbabilityMeasure P := hX.1
  have hh : 0 < g * γ / 8 := by positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (A / (g * γ / 8) + 1)
  refine ⟨1 + ∑ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, weightedGrid_term P M γ ρ g ((n : ℝ) * (g * γ / 8)),
    ?_, ?_⟩
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.sum_lt_top.mpr fun n _ =>
      weightedGrid_term_lt_top P X hX γ hγ hγ2 M hM hρ hg _⟩
  · intro α t hα ht hbulk hins
    obtain ⟨h1, h2⟩ := weightedGrid_ceil_mul_bounds hh α
    have hmem := weightedGrid_ceil_mem_Icc hh hn₀ hα
    calc weightedGmcBallMoment P M γ α 0 ρ t
        ≤ 1 + weightedGrid_term P M γ ρ g ((⌈α / (g * γ / 8)⌉ : ℝ) * (g * γ / 8)) :=
          weightedGrid_moment_le_term P M hγ hρ1 hg h1 h2 ht hbulk hins
      _ ≤ _ := add_le_add le_rfl (Finset.single_le_sum
          (f := fun n : ℤ => weightedGrid_term P M γ ρ g ((n : ℝ) * (g * γ / 8)))
          (fun _ _ => zero_le) hmem)

end DOZZ.Proofs
