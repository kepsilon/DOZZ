/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedLocalRange
public import DOZZ.GMC.SharpMoments.WeightedScale

/-! The sharp supplied-GMC weighted small-radius estimate used by intermediate Taylor fusion. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The constant is chosen before the radius; the exponent is the exact sharp weighted one. -/
theorem weighted_ball_moment_small_radius_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α p : ℝ) (hα : α < Q γ) (hp : 0 < p)
    (hrange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      weightedGmcBallMoment P M γ α 0 r p ≤
        ENNReal.ofReal (C * r ^ (γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2)) := by
  let m : ℝ≥0∞ := weightedGmcBallMoment P M γ α 0 (1 / 2) p
  have hm : m < ⊤ := (equatorGFF_GMC_weighted_local_moment_range P X hX γ hγ hγ2 M hM
    α hα p hp 0 (1 / 2) (by norm_num)).mpr hrange
  let E : ℝ := γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2
  let C : ℝ := (2 : ℝ) ^ E * (m.toReal + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have he : (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 = E := by
    dsimp only [E]
    unfold Q
    field_simp
    ring
  refine ⟨C, hC, ?_⟩
  intro r hr hr2
  have hscale := gmc_weighted_ball_moment_scale P X hX γ M hM α
    (c := 2 * r) (R := 1 / 2) (by positivity) (by linarith only [hr2])
    (by norm_num) (by norm_num) p
  rw [show (2 * r) * (1 / 2) = r by ring, he] at hscale
  rw [hscale]
  have hmle : m ≤ ENNReal.ofReal (m.toReal + 1) := by
    calc
      m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal hm.ne).symm
      _ ≤ ENNReal.ofReal (m.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  have hpow : 0 ≤ (2 * r) ^ E := (Real.rpow_pos_of_pos (by positivity) _).le
  calc
    ENNReal.ofReal ((2 * r) ^ E) * m ≤
        ENNReal.ofReal ((2 * r) ^ E) * ENNReal.ofReal (m.toReal + 1) := mul_le_mul' le_rfl hmle
    _ = ENNReal.ofReal (C * r ^ E) := by
      rw [← ENNReal.ofReal_mul hpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
      congr 1
      dsimp only [C]
      ring

end DOZZ.Proofs
