/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliSeparated

/-! Retaining two correlated cluster masses while decoupling a separated fixed disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The first two retained masses keep their joint law. Only the third, spatially separated
piece is replaced by an independent copy, with the common covariance factor given by the Kahane
comparison. -/
theorem retained_cluster_disk_inverse_compare
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (hA : MeasurableSet A) (ν : Measure S) [IsFiniteMeasure ν]
    (h₀ h₁ h₂ : S → ℝ≥0) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁) (hm₂ : Measurable h₂)
    (hb₀ : ∃ c : ℝ≥0, ∀ x, h₀ x ≤ c) (hb₁ : ∃ c : ℝ≥0, ∀ x, h₁ x ≤ c)
    (hb₂ : ∃ c : ℝ≥0, ∀ x, h₂ x ≤ c)
    (hs₀ : ∀ x, x ∉ A → h₀ x = 0) (hs₁ : ∀ x, x ∉ A → h₁ x = 0)
    (hs₂ : ∀ x, x ∈ A → h₂ x = 0)
    (γ C a b v : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (hcross : ∀ᵐ xy ∂ν.prod ν,
      (xy.1 ∈ A ↔ xy.2 ∉ A) → (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤ C) :
    (∫⁻ ω, fieldChaosMass P Φ ν h₀ γ ω ^ (-a) * fieldChaosMass P Φ ν h₁ γ ω ^ (-b) *
      fieldChaosMass P Φ ν h₂ γ ω ^ (-v) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * ((a + b + v) ^ 2 + a + b + v))) *
        (∫⁻ ω, fieldChaosMass P Φ ν h₀ γ ω ^ (-a) * fieldChaosMass P Φ ν h₁ γ ω ^ (-b) ∂P) *
          ∫⁻ ω, fieldChaosMass P Φ ν h₂ γ ω ^ (-v) ∂P := by
  classical
  have : IsProbabilityMeasure P := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let Ψ := independent_piece_field Φ A
  have hΨ := independent_piece_field_gaussian P Φ hΦ A hA
  have hcov : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤
        (∫ w, Ψ w xy.1 * Ψ w xy.2 ∂P.prod P) + C := by
    filter_upwards [hcross] with xy hxy
    rw [independent_piece_field_covariance P Φ hΦ A xy.1 xy.2]
    by_cases hx : xy.1 ∈ A <;> by_cases hy : xy.2 ∈ A
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        Set.indicator_of_notMem (show xy.1 ∉ Aᶜ from fun h => h hx),
        Set.indicator_of_notMem (show xy.2 ∉ Aᶜ from fun h => h hy), zero_mul, integral_zero,
        add_zero]
      exact le_add_of_nonneg_right hC
    · simpa only [Set.indicator_of_mem hx, Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show xy.1 ∉ Aᶜ from fun h => h hx),
        mul_zero, zero_mul, integral_zero, zero_add] using hxy ⟨fun _ => hy, fun _ => hx⟩
    · simpa only [Set.indicator_of_notMem hx, Set.indicator_of_mem hy,
        Set.indicator_of_notMem (show xy.2 ∉ Aᶜ from fun h => h hy),
        zero_mul, mul_zero, integral_zero, zero_add] using hxy ⟨fun h => False.elim (hx h), fun h => False.elim (h hy)⟩
    · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy,
        Set.indicator_of_mem (show xy.1 ∈ Aᶜ from hx),
        Set.indicator_of_mem (show xy.2 ∈ Aᶜ from hy), zero_mul, integral_zero, zero_add]
      exact le_add_of_nonneg_right hC
  have hdiag : ∀ᵐ x ∂ν, (∫ ω, Φ ω x ^ 2 ∂P) ≤ (∫ w, Ψ w x ^ 2 ∂P.prod P) + C := by
    filter_upwards [] with x
    rw [independent_piece_field_variance P Φ hΦ A x]
    exact le_add_of_nonneg_right hC
  have hk := retained_fields_multi_negative_compare P (P.prod P) Φ Ψ hΦ hΨ ν
    ![h₀, h₁, h₂] (by intro k; fin_cases k <;> assumption)
    (by intro k; fin_cases k <;> assumption) γ C hC ![a, b, v]
    (by intro k; fin_cases k <;> assumption) hcov hdiag
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hk
  have hm0 : AEMeasurable (fun ω => fieldChaosMass P Φ ν h₀ γ ω ^ (-a)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₀ hm₀ γ).aemeasurable.pow_const _
  have hm1 : AEMeasurable (fun ω => fieldChaosMass P Φ ν h₁ γ ω ^ (-b)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₁ hm₁ γ).aemeasurable.pow_const _
  have hm2 : AEMeasurable (fun ω => fieldChaosMass P Φ ν h₂ γ ω ^ (-v)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₂ hm₂ γ).aemeasurable.pow_const _
  have hrhs : (∫⁻ w : Ω × Ω, fieldChaosMass (P.prod P) Ψ ν h₀ γ w ^ (-a) *
      fieldChaosMass (P.prod P) Ψ ν h₁ γ w ^ (-b) *
      fieldChaosMass (P.prod P) Ψ ν h₂ γ w ^ (-v) ∂P.prod P) =
        (∫⁻ ω, fieldChaosMass P Φ ν h₀ γ ω ^ (-a) * fieldChaosMass P Φ ν h₁ γ ω ^ (-b) ∂P) *
          ∫⁻ ω, fieldChaosMass P Φ ν h₂ γ ω ^ (-v) ∂P := by
    dsimp only [Ψ]
    simp_rw [piece_field_mass_first P Φ hΦ A ν h₀ hs₀,
      piece_field_mass_first P Φ hΦ A ν h₁ hs₁,
      piece_field_mass_second P Φ hΦ A ν h₂ hs₂]
    exact lintegral_prod_mul (hm0.mul hm1) hm2
  rw [hrhs] at hk
  simpa only [mul_assoc, add_assoc] using hk

end DOZZ.Proofs
