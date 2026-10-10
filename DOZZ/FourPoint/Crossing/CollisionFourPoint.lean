/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.CollisionExpectation
public import DOZZ.FourPoint.FourPointTZeroEqStructureConstant
import Mathlib.Tactic

/-! # The normalized zero-channel coefficient

This is the probabilistic part of the zero-channel statement. It holds on the whole strict
four-point Seiberg domain, independently of hypergeometric nonresonance or diagonal
classification hypotheses.
-/

public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The zero-channel constant is the fused structure constant for every first
charge below Q, with no restriction to the unreflected interval. -/
theorem gammaHalf_fourPoint_collision_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ a b c : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (hs : 2 * Q γ < a + b + c - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto (fourPointT P M γ μ (-γ / 2) a b c) (𝓝 0)
      (𝓝 (structureConstant P M γ μ (a - γ / 2) b c)) := by
  have haF : a - γ / 2 < Q γ := by linarith only [ha, hγ]
  rw [← fourPointT_zero_eq_structureConstant P X M γ μ (γ / 2) a b c
    hγ hγ2 hμ haF hb hc hs hX hM]
  have hp : 0 < fourPointSExp γ (-γ / 2) a b c := by
    unfold fourPointSExp
    apply div_pos _ hγ
    linarith only [hs]
  have ht := crossing_collision_inverse_expectation P X hX γ hγ hγ2 M hM a b c
    ha hb hc (-fourPointSExp γ (-γ / 2) a b c) (neg_neg_of_pos hp)
  obtain ⟨C, hC, hbound⟩ := crossing_collision_inverse_uniform P X hX γ hγ hγ2 M hM
    a b c (-fourPointSExp γ (-γ / 2) a b c) (neg_nonpos.mpr hp.le)
  have hfin : (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, a, b] ![0, 0, 1] c ^
      (-fourPointSExp γ (-γ / 2) a b c) ∂P) ≠ ⊤ :=
    (lt_of_le_of_lt (hbound 0 (by simp)) hC).ne
  have hr := (ENNReal.continuousAt_toReal hfin).tendsto.comp ht
  unfold fourPointT
  simpa only [ENNReal.rpow_eq_pow, neg_div, Function.comp_def] using
    hr.const_mul (2 * μ ^ (-fourPointSExp γ (-γ / 2) a b c) / γ *
      Real.Gamma (fourPointSExp γ (-γ / 2) a b c))

end DOZZ.Proofs
