/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Paley–Zygmund for nonnegative extended random variables

A lower bound on the mean and an upper bound on the `p`-th moment of a nonnegative extended random
variable `Z` give a quantitative lower bound on the probability that `Z` exceeds `θ` times the
mean bound. The proof splits `Z` at the level `θ m` and applies Hölder's inequality to the part of
`Z` above the level. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Pointwise splitting at a level `c`: `Z ≤ c + Z · 1_{c < Z}`. -/
theorem paleyZygmund_le_add_indicator {Ω : Type*} (Z : Ω → ℝ≥0∞) (c : ℝ≥0∞) (ω : Ω) :
    Z ω ≤ c + {ω | c < Z ω}.indicator Z ω := by
  by_cases h : c < Z ω
  · simp [h]
  · simpa [h] using not_lt.1 h

/-- The mean of `Z` is at most the splitting level plus the integral of the part above it. -/
theorem paleyZygmund_lintegral_le_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ ω, Z ω ∂P ≤ c + ∫⁻ ω, {ω | c < Z ω}.indicator Z ω ∂P := by
  calc ∫⁻ ω, Z ω ∂P ≤ ∫⁻ ω, (c + {ω | c < Z ω}.indicator Z ω) ∂P :=
        lintegral_mono fun ω => paleyZygmund_le_add_indicator Z c ω
    _ = c + ∫⁻ ω, {ω | c < Z ω}.indicator Z ω ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- The strict superlevel set of an a.e. measurable function is null measurable. -/
theorem paleyZygmund_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ≥0∞) (hZ : AEMeasurable Z P) (c : ℝ≥0∞) :
    NullMeasurableSet {ω | c < Z ω} P :=
  nullMeasurableSet_lt aemeasurable_const hZ

/-- Hölder's inequality for the part of `Z` above a level. -/
theorem paleyZygmund_holder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ≥0∞) (hZ : AEMeasurable Z P) {p q : ℝ} (hpq : p.HolderConjugate q) (c : ℝ≥0∞) :
    ∫⁻ ω, {ω | c < Z ω}.indicator Z ω ∂P ≤
      (∫⁻ ω, Z ω ^ p ∂P) ^ (1 / p) * (P {ω | c < Z ω}) ^ (1 / q) := by
  have hAm := paleyZygmund_nullMeasurableSet P Z hZ c
  have hg : AEMeasurable ({ω | c < Z ω}.indicator fun _ => (1 : ℝ≥0∞)) P :=
    aemeasurable_const.indicator₀ hAm
  have hmul : {ω | c < Z ω}.indicator Z = Z * {ω | c < Z ω}.indicator fun _ => (1 : ℝ≥0∞) := by
    funext ω
    by_cases h : c < Z ω <;> simp [h]
  have hpow : ∀ ω, ({ω | c < Z ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ q =
      {ω | c < Z ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    by_cases h : c < Z ω
    · simp [h]
    · simp [h, hpq.symm.pos]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hZ hg
  simp_rw [hpow, lintegral_indicator_fun_one₀ hAm] at hHolder
  rwa [hmul]

/-- From `m ≤ θ m + X` conclude `(1 - θ) m ≤ X` in `ℝ≥0∞`. -/
theorem paleyZygmund_sub_le {θ m : ℝ} (hθ1 : θ < 1) (hθ0 : 0 ≤ θ) (hm : 0 < m) {X : ℝ≥0∞}
    (h : ENNReal.ofReal m ≤ ENNReal.ofReal (θ * m) + X) :
    ENNReal.ofReal ((1 - θ) * m) ≤ X := by
  have hsplit : ENNReal.ofReal m =
      ENNReal.ofReal (θ * m) + ENNReal.ofReal ((1 - θ) * m) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hθ0 hm.le) (mul_nonneg (sub_nonneg.2 hθ1.le) hm.le)]
    congr 1
    ring
  rw [hsplit] at h
  exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 h

/-- Raise the Hölder-type bound `a ≤ K^(1/p) y^(1/q)` to the conjugate power `q = p / (p - 1)`. -/
theorem paleyZygmund_rpow_step {p a K : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hK : 0 ≤ K) {y : ℝ≥0∞}
    (h : ENNReal.ofReal a ≤ (ENNReal.ofReal K) ^ (1 / p) * y ^ (1 / (p / (p - 1)))) :
    ENNReal.ofReal (a ^ (p / (p - 1))) ≤ ENNReal.ofReal (K ^ (1 / (p - 1))) * y := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := sub_pos.2 hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hp1
  have e1 : 1 / p * (p / (p - 1)) = 1 / (p - 1) := by
    field_simp
  have e2 : 1 / (p / (p - 1)) * (p / (p - 1)) = 1 := by
    field_simp
  have h1 := ENNReal.rpow_le_rpow h hq.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, e1, e2,
    ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg hK (one_div_nonneg.2 hp1.le),
    ENNReal.ofReal_rpow_of_nonneg ha hq.le] at h1
  exact h1

/-- Paley–Zygmund with a `p`-th moment: a lower bound `m` on the mean and an upper bound `K` on the
`p`-th moment give a quantitative lower bound on the probability of exceeding `θ m`. -/
theorem paley_zygmund_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ≥0∞) (hZ : AEMeasurable Z P) (p θ m K : ℝ) (hp : 1 < p)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hm : 0 < m) (hK : 0 < K)
    (hmZ : ENNReal.ofReal m ≤ ∫⁻ ω, Z ω ∂P)
    (hKZ : ∫⁻ ω, Z ω ^ p ∂P ≤ ENNReal.ofReal K) :
    ENNReal.ofReal (((1 - θ) * m) ^ (p / (p - 1)) / K ^ (1 / (p - 1))) ≤
      P {ω | ENNReal.ofReal (θ * m) < Z ω} := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have h3 : ENNReal.ofReal m ≤ ENNReal.ofReal (θ * m) +
      ∫⁻ ω, {ω | ENNReal.ofReal (θ * m) < Z ω}.indicator Z ω ∂P :=
    hmZ.trans (paleyZygmund_lintegral_le_add P Z (ENNReal.ofReal (θ * m)))
  have h4 := paleyZygmund_sub_le hθ1 hθ0 hm h3
  have h5 : ENNReal.ofReal ((1 - θ) * m) ≤ (ENNReal.ofReal K) ^ (1 / p) *
      (P {ω | ENNReal.ofReal (θ * m) < Z ω}) ^ (1 / (p / (p - 1))) := by
    refine h4.trans ((paleyZygmund_holder P Z hZ hpq (ENNReal.ofReal (θ * m))).trans ?_)
    exact mul_le_mul_left (ENNReal.rpow_le_rpow hKZ (one_div_nonneg.2 hp0.le)) _
  have h6 := paleyZygmund_rpow_step hp (mul_nonneg (sub_nonneg.2 hθ1.le) hm.le) hK.le h5
  have hKpos : 0 < K ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hK _
  rw [ENNReal.ofReal_div_of_pos hKpos]
  exact ENNReal.div_le_of_le_mul' h6

end DOZZ.Proofs
