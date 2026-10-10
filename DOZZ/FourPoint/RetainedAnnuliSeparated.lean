/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliComparison
public import DOZZ.GMC.SharpMoments.GluedFieldGaussian

/-! Independent reference pieces for spatially separated retained masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Two independent versions of a field, chosen according to a spatial partition. -/
noncomputable def independent_piece_field {Ω S : Type*}
    (Φ : Ω → S → ℝ) (A : Set S) (w : Ω × Ω) (x : S) : ℝ :=
  A.indicator (Φ w.1) x + Aᶜ.indicator (Φ w.2) x

/-- Independent copies on the two pieces preserve the centered Gaussian field predicate. -/
theorem independent_piece_field_gaussian
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (hA : MeasurableSet A) :
    IsCenteredGaussianField (P.prod P) (independent_piece_field Φ A) := by
  refine ⟨?_, ?_⟩
  · have h1 : Measurable (fun w : (Ω × Ω) × S => Φ w.1.1 w.2) :=
      hΦ.1.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable (fun w : (Ω × Ω) × S => Φ w.1.2 w.2) :=
      hΦ.1.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (h1.indicator (measurable_snd hA)).add (h2.indicator (measurable_snd hA.compl))
  · intro n x
    have h1 := isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x)
      (fun i => A.indicator (fun _ => (1 : ℝ)) (x i))
    have h2 := isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x)
      (fun i => Aᶜ.indicator (fun _ => (1 : ℝ)) (x i))
    have h := isCenteredJointlyGaussian_prod_add P P _ _ h1 h2
    have he : (fun (w : Ω × Ω) (i : Fin n) => independent_piece_field Φ A w (x i)) =
        fun w i => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ w.1 (x i) +
          Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Φ w.2 (x i) := by
      funext w i
      rw [independent_piece_field, gluedField_indicator_eq_mul A,
        gluedField_indicator_eq_mul Aᶜ]
    rw [he]
    exact h

/-- The within-piece covariance is unchanged and the cross-piece covariance is zero. -/
theorem independent_piece_field_covariance
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (x y : S) :
    (∫ w, independent_piece_field Φ A w x * independent_piece_field Φ A w y
      ∂P.prod P) =
      (∫ ω, A.indicator (Φ ω) x * A.indicator (Φ ω) y ∂P) +
        (∫ ω, Aᶜ.indicator (Φ ω) x * Aᶜ.indicator (Φ ω) y ∂P) := by
  have : IsProbabilityMeasure P := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  exact gaussianCovariance_prod_add P P _ _ _ _
    (gluedField_memLp_indicator hΦ A x) (gluedField_memLp_indicator hΦ A y)
    (gluedField_memLp_indicator hΦ Aᶜ x) (gluedField_memLp_indicator hΦ Aᶜ y)
    (gluedField_integral_indicator hΦ A x) (gluedField_integral_indicator hΦ A y)

/-- Splitting copies across a partition keeps every diagonal variance. -/
theorem independent_piece_field_variance
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (x : S) :
    (∫ w, independent_piece_field Φ A w x ^ 2 ∂P.prod P) =
      ∫ ω, Φ ω x ^ 2 ∂P := by
  simp only [pow_two]
  rw [independent_piece_field_covariance P Φ hΦ A x x]
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx), zero_mul, integral_zero, add_zero]
  · simp only [Set.indicator_of_notMem hx,
      Set.indicator_of_mem (show x ∈ Aᶜ from hx), zero_mul, integral_zero, zero_add]

/-- A retained weight supported in the first piece uses precisely the first independent copy. -/
theorem piece_field_mass_first
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (ν : Measure S) (h : S → ℝ≥0) (hs : ∀ x, x ∉ A → h x = 0)
    (γ : ℝ) (w : Ω × Ω) :
    fieldChaosMass (P.prod P) (independent_piece_field Φ A) ν h γ w =
      fieldChaosMass P Φ ν h γ w.1 := by
  unfold fieldChaosMass
  apply lintegral_congr
  intro x
  rw [independent_piece_field_variance P Φ hΦ A x]
  by_cases hx : x ∈ A
  · simp only [independent_piece_field, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx), add_zero]
  · simp only [hs x hx, ENNReal.coe_zero, zero_mul]

/-- A retained weight supported in the second piece uses precisely the second independent copy. -/
theorem piece_field_mass_second
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (ν : Measure S) (h : S → ℝ≥0) (hs : ∀ x, x ∈ A → h x = 0)
    (γ : ℝ) (w : Ω × Ω) :
    fieldChaosMass (P.prod P) (independent_piece_field Φ A) ν h γ w =
      fieldChaosMass P Φ ν h γ w.2 := by
  unfold fieldChaosMass
  apply lintegral_congr
  intro x
  rw [independent_piece_field_variance P Φ hΦ A x]
  by_cases hx : x ∈ A
  · simp only [hs x hx, ENNReal.coe_zero, zero_mul]
  · simp only [independent_piece_field, Set.indicator_of_notMem hx,
      Set.indicator_of_mem (show x ∈ Aᶜ from hx), zero_add]

/-- A bounded cross-piece covariance gives an upper product bound by independent masses.
The within-piece laws and the common scalar factor appear explicitly. -/
theorem two_retained_blocks_inverse_compare
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (hA : MeasurableSet A) (ν : Measure S) [IsFiniteMeasure ν]
    (h₀ h₁ : S → ℝ≥0) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁)
    (hb₀ : ∃ c : ℝ≥0, ∀ x, h₀ x ≤ c) (hb₁ : ∃ c : ℝ≥0, ∀ x, h₁ x ≤ c)
    (hs₀ : ∀ x, x ∉ A → h₀ x = 0) (hs₁ : ∀ x, x ∈ A → h₁ x = 0)
    (γ C a b : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcross : ∀ᵐ xy ∂ν.prod ν,
      (xy.1 ∈ A ↔ xy.2 ∉ A) → (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤ C) :
    (∫⁻ ω, (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a) *
      (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * ((a + b) ^ 2 + a + b))) *
        (∫⁻ ω, (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a) ∂P) *
          (∫⁻ ω, (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b) ∂P) := by
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
    ![h₀, h₁] (by intro k; fin_cases k <;> assumption)
    (by intro k; fin_cases k <;> assumption) γ C hC ![a, b]
    (by intro k; fin_cases k <;> assumption) hcov hdiag
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hk
  have hm0 : AEMeasurable (fun ω => (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₀ hm₀ γ).aemeasurable.pow_const _
  have hm1 : AEMeasurable (fun ω => (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₁ hm₁ γ).aemeasurable.pow_const _
  have hrhs : (∫⁻ w : Ω × Ω, (fieldChaosMass (P.prod P) Ψ ν h₀ γ w) ^ (-a) *
      (fieldChaosMass (P.prod P) Ψ ν h₁ γ w) ^ (-b) ∂P.prod P) =
        (∫⁻ ω, (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a) ∂P) *
          (∫⁻ ω, (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b) ∂P) := by
    dsimp only [Ψ]
    simp_rw [piece_field_mass_first P Φ hΦ A ν h₀ hs₀,
      piece_field_mass_second P Φ hΦ A ν h₁ hs₁]
    exact lintegral_prod_mul hm0 hm1
  rw [hrhs] at hk
  simpa only [mul_assoc, add_assoc] using hk

end DOZZ.Proofs
