/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.GluedFieldGaussian

/-! # The actual independent-copy field on the two fusion regions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal

namespace DOZZ.Proofs

/-- Use the first field copy on `A` and the second independent copy on its complement. -/
noncomputable def reflected_decoupled_field {Ω S : Type*} (Φ : Ω → S → ℝ) (A : Set S)
    (ω : Ω × Ω) (x : S) : ℝ := A.indicator (Φ ω.1) x + Aᶜ.indicator (Φ ω.2) x

/-- The independent-copy field is a jointly measurable centered Gaussian field. -/
theorem reflected_decoupled_field_gaussian {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : IsCenteredGaussianField P Φ) (A : Set S) (hA : MeasurableSet A) :
    IsCenteredGaussianField (P.prod P) (reflected_decoupled_field Φ A) := by
  constructor
  · have h1 : Measurable (fun p : (Ω × Ω) × S => Φ p.1.1 p.2) :=
      hΦ.1.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable (fun p : (Ω × Ω) × S => Φ p.1.2 p.2) :=
      hΦ.1.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (h1.indicator (measurable_snd hA)).add (h2.indicator (measurable_snd hA.compl))
  · intro n x
    have h1 := isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x)
      (fun i => A.indicator (fun _ => (1 : ℝ)) (x i))
    have h2 := isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x)
      (fun i => Aᶜ.indicator (fun _ => (1 : ℝ)) (x i))
    have h := isCenteredJointlyGaussian_prod_add P P _ _ h1 h2
    have he : (fun ω i => reflected_decoupled_field Φ A ω (x i)) =
        fun ω i => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ ω.1 (x i) +
          Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Φ ω.2 (x i) := by
      funext ω i
      unfold reflected_decoupled_field
      rw [gluedField_indicator_eq_mul A, gluedField_indicator_eq_mul Aᶜ]
    rw [he]
    exact h

/-- Within either region the covariance is unchanged; across the regions it is zero. -/
theorem reflected_decoupled_field_covariance {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : IsCenteredGaussianField P Φ) (A : Set S) (x y : S) :
    gaussianCovariance (P.prod P) (fun ω => reflected_decoupled_field Φ A ω x)
      (fun ω => reflected_decoupled_field Φ A ω y) =
      if (x ∈ A ↔ y ∈ A) then gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y)
        else 0 := by
  classical
  let _ : IsProbabilityMeasure P := (hΦ.2 0 (fun i => Fin.elim0 i)).1
  have h := gaussianCovariance_prod_add P P
    (fun ω => A.indicator (Φ ω) x) (fun ω => A.indicator (Φ ω) y)
    (fun ω => Aᶜ.indicator (Φ ω) x) (fun ω => Aᶜ.indicator (Φ ω) y)
    (gluedField_memLp_indicator hΦ A x) (gluedField_memLp_indicator hΦ A y)
    (gluedField_memLp_indicator hΦ Aᶜ x) (gluedField_memLp_indicator hΦ Aᶜ y)
    (gluedField_integral_indicator hΦ A x) (gluedField_integral_indicator hΦ A y)
  change gaussianCovariance (P.prod P)
    (fun ω => A.indicator (Φ ω.1) x + Aᶜ.indicator (Φ ω.2) x)
    (fun ω => A.indicator (Φ ω.1) y + Aᶜ.indicator (Φ ω.2) y) = _
  rw [h]
  unfold gaussianCovariance
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
    simp only [hx, hy, mem_compl_iff, Set.indicator_of_mem, Set.indicator_of_notMem,
      iff_self, iff_false, false_iff, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, zero_mul, mul_zero, integral_zero, add_zero, zero_add]

/-- The independent-copy Wick mass is the sum of the two independent regional masses. -/
theorem reflected_decoupled_field_mass {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : IsCenteredGaussianField P Φ) (A : Set S) (hA : MeasurableSet A)
    (ν : Measure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω × Ω) :
    fieldChaosMass (P.prod P) (reflected_decoupled_field Φ A) ν h γ ω =
      fieldChaosMass P Φ (ν.restrict A) h γ ω.1 +
        fieldChaosMass P Φ (ν.restrict Aᶜ) h γ ω.2 := by
  have hvar (x : S) : (∫ q, (reflected_decoupled_field Φ A q x) ^ 2 ∂P.prod P) =
      ∫ q, (Φ q x) ^ 2 ∂P := by
    have hc := reflected_decoupled_field_covariance P Φ hΦ A x x
    simpa only [iff_self, ite_true, gaussianCovariance, pow_two] using hc
  unfold fieldChaosMass
  refine (lintegral_add_compl _ hA).symm.trans ?_
  congr 1
  · apply setLIntegral_congr_fun hA
    intro x hx
    dsimp only
    rw [hvar, reflected_decoupled_field, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun hn => hn hx), add_zero]
  · apply setLIntegral_congr_fun hA.compl
    intro x hx
    dsimp only
    rw [hvar, reflected_decoupled_field, Set.indicator_of_notMem (show x ∉ A from hx),
      Set.indicator_of_mem hx, zero_add]

end DOZZ.Proofs
