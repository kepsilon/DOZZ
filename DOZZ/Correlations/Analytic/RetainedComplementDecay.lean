/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedComplement

/-! Uniform decay of the full omitted Coulomb mass. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Finite-root decay and inversion give one uniform small-moment bound for the complete
complement of the retained region. The charge bound stays strictly below `Q`. -/
theorem retained_complement_moment_decay
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ k j, j ≠ k → 2 * δ ≤ ‖z j - z k‖)
    (A a gap m : ℝ) (hgap : 0 < gap) (ha : a + gap < Q γ)
    (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap)))) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (α : Fin N → ℝ) (αinf : ℝ),
      (∀ i, |α i| ≤ A) → |αinf| ≤ A → (∀ i, α i ≤ a) → αinf ≤ a →
      ∀ r : ℝ, 2 * Real.exp (-r) ≤ δ → 1 ≤ Real.exp r / 2 →
      (∀ i, 2 * ‖z i‖ ≤ Real.exp r / 2) →
      (∫⁻ ω, (∫⁻ x in (retainedRegion z r)ᶜ,
        coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) ≤
        ENNReal.ofReal ((2 * Real.exp (-r)) ^ (γ * gap * m)) * K := by
  classical
  have hroot (k : Fin N) := coulomb_insertion_moment_decay
    P X hX γ hγ hγ2 M hM z k δ hδ hδ1 (hsep k) A a gap m hgap ha hm hms
  choose C hC hroot using hroot
  obtain ⟨D, hD, hext⟩ := coulomb_exterior_moment_decay
    P X hX γ hγ hγ2 M hM z A a gap m hgap ha hm hms
  refine ⟨(∑ i, C i) + D, ENNReal.add_lt_top.mpr
    ⟨ENNReal.sum_lt_top.mpr (fun i _ => hC i), hD⟩, ?_⟩
  intro α αinf hα hinf hαup hinfup r hsmall hlarge hz
  have hrho : 0 < 2 * Real.exp (-r) := mul_pos (by norm_num) (Real.exp_pos _)
  have hrecip : 1 / (Real.exp r / 2) = 2 * Real.exp (-r) := by
    rw [Real.exp_neg]
    field_simp
  have hi := hext α αinf hα hinfup (Real.exp r / 2) hlarge hz
  rw [hrecip] at hi
  calc
    _ ≤ (∑ i, ∫⁻ ω, (∫⁻ x in Metric.ball (z i) (2 * Real.exp (-r)),
        coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) +
        ∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp r / 2 < ‖x‖},
          coulombWeight γ α z αinf x ∂M ω) ^ m ∂P :=
      retained_complement_moment_le P X hX γ hγ hγ2 M hM α z αinf r m hm hm1
    _ ≤ (∑ i, ENNReal.ofReal ((2 * Real.exp (-r)) ^ (γ * gap * m)) * C i) +
        ENNReal.ofReal ((2 * Real.exp (-r)) ^ (γ * gap * m)) * D :=
      add_le_add (Finset.sum_le_sum (fun i _ =>
        hroot i α αinf hα hinf (hαup i) _ hrho hsmall)) hi
    _ = _ := by rw [← Finset.mul_sum, mul_add]

end DOZZ.Proofs
