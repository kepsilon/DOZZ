/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedComplementDecay
public import DOZZ.Correlations.Analytic.CutoffGeometry

/-! Exponential cutoff-time decay of the omitted-mass small moment. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- A power of the doubled cutoff radius has the exact exponential rate. -/
theorem scaled_exp_radius_power (r k : ℝ) :
    (2 * Real.exp (-r)) ^ k = (2 : ℝ) ^ k * Real.exp (-k * r) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_nonneg _), ← Real.exp_mul]
  congr 1
  ring_nf

/-- The complete excluded Coulomb mass has a uniform exponentially decaying small moment
on every bounded charge box with a strict upper charge gap. -/
theorem complement_exponential_moment
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ k j, j ≠ k → 2 * δ ≤ ‖z j - z k‖)
    (A a gap m : ℝ) (hgap : 0 < gap) (ha : a + gap < Q γ)
    (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap)))) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (α : Fin N → ℝ) (αinf : ℝ), (∀ i, |α i| ≤ A) → |αinf| ≤ A →
        (∀ i, α i ≤ a) → αinf ≤ a →
        (∫⁻ ω, (∫⁻ x in (retainedRegion z (n : ℝ))ᶜ,
          coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) ≤
          ENNReal.ofReal (Real.exp (-(γ * gap * m) * n)) * K := by
  obtain ⟨C, hC, hb⟩ := retained_complement_moment_decay
    P X hX γ hγ hγ2 M hM z δ hδ hδ1 hsep A a gap m hgap ha hm hm1 hms
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ (γ * gap * m)) * C,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC, ?_⟩
  filter_upwards [retained_cutoff_geometry_eventually z δ 1 hδ] with n hn
  intro α αinf hα hinf hαup hinfup
  have he := hb α αinf hα hinf hαup hinfup (n : ℝ) hn.1 hn.2.1 hn.2.2.1
  rw [scaled_exp_radius_power,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at he
  simpa only [mul_assoc, mul_comm, mul_left_comm] using he

end DOZZ.Proofs
