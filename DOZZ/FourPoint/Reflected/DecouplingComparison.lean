/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.DecoupledField
public import DOZZ.GMC.FieldGaussianCommonScalar
public import DOZZ.Statements.GMC.KahaneFieldPowerConvex
import Mathlib.Tactic

/-! # Two-sided negative-moment comparison after lateral decoupling

The independent-copy field preserves covariance within each region. A common
independent Gaussian of variance `c²` absorbs the absolute cross-covariance
on either side. Its exact Wick moment is kept in the two bounds.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical

namespace DOZZ.Proofs

/-- The original and independent-copy covariances differ only across the partition. -/
theorem reflected_decoupled_covariance_sandwich {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : IsCenteredGaussianField P Φ) (A : Set S) (c : ℝ)
    (hcross : ∀ x y, ¬(x ∈ A ↔ y ∈ A) →
      |gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y)| ≤ c ^ 2) (x y : S) :
    gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y) ≤
      gaussianCovariance (P.prod P) (fun ω => reflected_decoupled_field Φ A ω x)
        (fun ω => reflected_decoupled_field Φ A ω y) + c ^ 2 ∧
    gaussianCovariance (P.prod P) (fun ω => reflected_decoupled_field Φ A ω x)
        (fun ω => reflected_decoupled_field Φ A ω y) ≤
      gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y) + c ^ 2 := by
  rw [reflected_decoupled_field_covariance P Φ hΦ A x y]
  by_cases he : x ∈ A ↔ y ∈ A
  · rw [ite_eq_left he]
    exact ⟨le_add_of_nonneg_right (sq_nonneg c), le_add_of_nonneg_right (sq_nonneg c)⟩
  · rw [ite_eq_right he]
    obtain ⟨hl, hu⟩ := abs_le.mp (hcross x y he)
    constructor <;> linarith only [hl, hu]

/-- The finite-cutoff negative moment changes by at most one exact Gaussian Wick factor. -/
theorem reflected_kahane_decoupling {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : IsCenteredGaussianField P Φ) (A : Set S) (hA : MeasurableSet A)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ b : ℝ≥0, ∀ x, h x ≤ b) (γ q c : ℝ) (hq : 0 ≤ q)
    (hcross : ∀ x y, ¬(x ∈ A ↔ y ∈ A) →
      |gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y)| ≤ c ^ 2) :
    let m := ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * ((-q) ^ 2 - (-q))))
    (∫⁻ ω, fieldChaosMass P Φ ν h γ ω ^ (-q) ∂P) ≤
      m * (∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ A) ν h γ ω ^ (-q)
        ∂P.prod P) ∧
    (∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ A) ν h γ ω ^ (-q)
        ∂P.prod P) ≤ m * (∫⁻ ω, fieldChaosMass P Φ ν h γ ω ^ (-q) ∂P) := by
  let Ψ := reflected_decoupled_field Φ A
  have hΨ := reflected_decoupled_field_gaussian P Φ hΦ A hA
  have hupper : ∀ x y,
      gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y) ≤
      gaussianCovariance ((P.prod P).prod (gaussianReal 0 1))
        (fun ω => Ψ ω.1 x + c * ω.2) (fun ω => Ψ ω.1 y + c * ω.2) := by
    intro x y
    rw [gaussianCovariance_field_independent_common_scalar_add (P.prod P) Ψ hΨ c x y]
    exact (reflected_decoupled_covariance_sandwich P Φ hΦ A c hcross x y).1
  have hlower : ∀ x y,
      gaussianCovariance (P.prod P) (fun ω => Ψ ω x) (fun ω => Ψ ω y) ≤
      gaussianCovariance (P.prod (gaussianReal 0 1))
        (fun ω => Φ ω.1 x + c * ω.2) (fun ω => Φ ω.1 y + c * ω.2) := by
    intro x y
    rw [gaussianCovariance_field_independent_common_scalar_add P Φ hΦ c x y]
    exact (reflected_decoupled_covariance_sandwich P Φ hΦ A c hcross x y).2
  have hup := DOZZ.kahane_field_power_convex P ((P.prod P).prod (gaussianReal 0 1))
    Φ (fun ω x => Ψ ω.1 x + c * ω.2) hΦ
    (independent_common_scalar_add_isCenteredGaussianField (P.prod P) Ψ hΨ c)
    ν h hh hhb γ (-q) (Or.inl (neg_nonpos.mpr hq))
    (Filter.Eventually.of_forall (fun xy => hupper xy.1 xy.2))
    (Filter.Eventually.of_forall (fun x => by simpa only [gaussianCovariance, pow_two] using hupper x x))
  have hlo := DOZZ.kahane_field_power_convex (P.prod P) (P.prod (gaussianReal 0 1))
    Ψ (fun ω x => Φ ω.1 x + c * ω.2) hΨ
    (independent_common_scalar_add_isCenteredGaussianField P Φ hΦ c)
    ν h hh hhb γ (-q) (Or.inl (neg_nonpos.mpr hq))
    (Filter.Eventually.of_forall (fun xy => hlower xy.1 xy.2))
    (Filter.Eventually.of_forall (fun x => by simpa only [gaussianCovariance, pow_two] using hlower x x))
  rw [fieldChaosMoment_independent_common_scalar_factor (P.prod P) Ψ hΨ ν h hh hhb γ c (-q)] at hup
  rw [fieldChaosMoment_independent_common_scalar_factor P Φ hΦ ν h hh hhb γ c (-q)] at hlo
  exact ⟨hup, hlo⟩

end DOZZ.Proofs
