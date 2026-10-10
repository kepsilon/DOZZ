/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CoulombInsertionDecay

/-! The insertion at infinity has the same small-moment decay after inversion. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Uniform polynomial decay of the Coulomb mass outside a growing disk. The inversion law
`DOZZ.equatorGFF_GMC_inversion_law` transfers the exterior power integral to a shrinking weighted
disk. -/
theorem coulomb_exterior_moment_decay
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (A a gap m : ℝ) (hgap : 0 < gap)
    (ha : a + gap < Q γ) (hm : 0 < m)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap)))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (α : Fin N → ℝ) (αinf : ℝ),
      (∀ i, |α i| ≤ A) → αinf ≤ a → ∀ R : ℝ, 1 ≤ R →
      (∀ i, 2 * ‖z i‖ ≤ R) →
      (∫⁻ ω, (∫⁻ x in {x : ℂ | R < ‖x‖}, coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) ≤
        ENNReal.ofReal ((1 / R) ^ (γ * gap * m)) * C := by
  obtain ⟨C, hC, hdec⟩ := weighted_small_ball_moment_decay
    P X hX γ hγ hγ2 M hM a gap hgap ha 0 1 (by norm_num) m hm hms
  let B := ENNReal.ofReal ((2 : ℝ) ^ (N * (γ * A)))
  refine ⟨B ^ m * C, ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hm.le ENNReal.ofReal_ne_top) hC, ?_⟩
  intro α αinf hα hi R hR hz
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hb : ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) ≤ B := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      _ ≤ ∑ j : Fin N, γ * A := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul, abs_of_pos hγ]
        exact mul_le_mul_of_nonneg_left (hα j) hγ.le)
      _ = _ := by simp
  let W (ω : Ω) := ∫⁻ x in {x : ℂ | R < ‖x‖},
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂M ω
  have hg : Measurable (fun x : ℂ => ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf)) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp measurable_norm)
  have hE : MeasurableSet {x : ℂ | R < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hw : AEMeasurable W P :=
    gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ hg _ hE
  have hpt (ω : Ω) :
      (∫⁻ x in {x : ℂ | R < ‖x‖}, coulombWeight γ α z αinf x ∂M ω) ≤ B * W ω := by
    dsimp only [W]
    rw [← lintegral_const_mul _ hg]
    apply setLIntegral_mono' hE
    intro x hx
    exact (coulombWeight_le_exterior γ α z αinf hR hz hx).trans (mul_le_mul_left hb _)
  calc
    _ ≤ ∫⁻ ω, (B * W ω) ^ m ∂P :=
      lintegral_mono (fun ω => ENNReal.rpow_le_rpow (hpt ω) hm.le)
    _ = B ^ m * ∫⁻ ω, W ω ^ m ∂P := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hm.le]
      exact lintegral_const_mul'' _ (hw.pow_const m)
    _ ≤ B ^ m * weightedGmcBallMoment P M γ αinf 0 (1 / R) m :=
      mul_le_mul_right (gmc_exterior_moment_le_weighted P X hX γ hγ hγ2 M hM αinf hR0 m hm.le) _
    _ ≤ B ^ m * (ENNReal.ofReal ((1 / R) ^ (γ * gap * m)) * C) := by
      apply mul_le_mul_right
      apply hdec αinf hi (1 / R) (one_div_pos.mpr hR0)
      simpa only [min_self, div_one] using (one_div_le_one_div_of_le zero_lt_one hR)
    _ = _ := by ring

end DOZZ.Proofs
