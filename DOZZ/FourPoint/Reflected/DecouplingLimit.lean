/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.DecouplingComparison
public import DOZZ.FourPoint.Reflected.CommonScalarLimit
public import DOZZ.Statements.GMC.KahaneLimitFieldNegativePower
import Mathlib.Tactic
/-! Two-sided lateral comparison passes through the actual mass limits in probability. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exact comparison factor survives cutoff removal using the limiting Kahane comparison
`DOZZ.kahane_limit_field_negative_power`. No convergence of negative moments or uniform
integrability is assumed. -/
theorem reflected_kahane_decoupling_limit
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (Φ : ℝ → Ω → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField P (Φ r)) (A : Set S) (hA : MeasurableSet A)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ b : ℝ≥0, ∀ x, h x ≤ b) (γ q c : ℝ) (hq : 0 < q)
    (hcross : ∀ r, ∀ᵐ xy ∂ν.prod ν, ¬(xy.1 ∈ A ↔ xy.2 ∈ A) →
      |gaussianCovariance P (fun ω => Φ r ω xy.1) (fun ω => Φ r ω xy.2)| ≤ c ^ 2)
    (ZX : Ω → ℝ) (ZY : Ω × Ω → ℝ)
    (hXconv : TendstoInMeasure P
      (fun r ω => (fieldChaosMass P (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure (P.prod P)
      (fun r ω => (fieldChaosMass (P.prod P) (reflected_decoupled_field (Φ r) A)
        ν h γ ω).toReal) atTop ZY) :
    let m := ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * (q ^ 2 + q)))
    (∫⁻ ω, ENNReal.ofReal (ZX ω) ^ (-q) ∂P) ≤
      m * (∫⁻ ω, ENNReal.ofReal (ZY ω) ^ (-q) ∂P.prod P) ∧
    (∫⁻ ω, ENNReal.ofReal (ZY ω) ^ (-q) ∂P.prod P) ≤
      m * (∫⁻ ω, ENNReal.ofReal (ZX ω) ^ (-q) ∂P) := by
  let Ψ := fun r => reflected_decoupled_field (Φ r) A
  have hΨ (r : ℝ) := reflected_decoupled_field_gaussian P (Φ r) (hΦ r) A hA
  have hsand (r : ℝ) (x y : S)
      (hb : ¬(x ∈ A ↔ y ∈ A) →
        |gaussianCovariance P (fun ω => Φ r ω x) (fun ω => Φ r ω y)| ≤ c ^ 2) :
      gaussianCovariance P (fun ω => Φ r ω x) (fun ω => Φ r ω y) ≤
        gaussianCovariance (P.prod P) (fun ω => Ψ r ω x) (fun ω => Ψ r ω y) + c^2 ∧
      gaussianCovariance (P.prod P) (fun ω => Ψ r ω x) (fun ω => Ψ r ω y) ≤
        gaussianCovariance P (fun ω => Φ r ω x) (fun ω => Φ r ω y) + c^2 := by
    rw [reflected_decoupled_field_covariance P (Φ r) (hΦ r) A x y]
    by_cases he : x ∈ A ↔ y ∈ A
    · rw [ite_eq_left he]
      exact ⟨le_add_of_nonneg_right (sq_nonneg c), le_add_of_nonneg_right (sq_nonneg c)⟩
    · rw [ite_eq_right he]
      obtain ⟨hl, hu⟩ := abs_le.mp (hb he)
      constructor <;> linarith only [hl, hu]
  have hu (r : ℝ) (x y : S)
      (hb : ¬(x ∈ A ↔ y ∈ A) →
        |gaussianCovariance P (fun ω => Φ r ω x) (fun ω => Φ r ω y)| ≤ c ^ 2) :
      gaussianCovariance P (fun ω => Φ r ω x) (fun ω => Φ r ω y) ≤
        gaussianCovariance ((P.prod P).prod (gaussianReal 0 1))
          (fun u => Ψ r u.1 x + c*u.2) (fun u => Ψ r u.1 y + c*u.2) := by
    rw [gaussianCovariance_field_independent_common_scalar_add (P.prod P) (Ψ r) (hΨ r) c]
    exact (hsand r x y hb).1
  have hl (r : ℝ) (x y : S)
      (hb : ¬(x ∈ A ↔ y ∈ A) →
        |gaussianCovariance P (fun ω => Φ r ω x) (fun ω => Φ r ω y)| ≤ c ^ 2) :
      gaussianCovariance (P.prod P) (fun ω => Ψ r ω x) (fun ω => Ψ r ω y) ≤
        gaussianCovariance (P.prod (gaussianReal 0 1))
          (fun u => Φ r u.1 x + c*u.2) (fun u => Φ r u.1 y + c*u.2) := by
    rw [gaussianCovariance_field_independent_common_scalar_add P (Φ r) (hΦ r) c]
    exact (hsand r x y hb).2
  have hXm : AEMeasurable ZX P := hXconv.aemeasurable fun r =>
    (centeredGaussianField_fieldChaosMass_measurable P (Φ r) (hΦ r) ν h hh γ).ennreal_toReal.aemeasurable
  have hYm : AEMeasurable ZY (P.prod P) := hYconv.aemeasurable fun r =>
    (centeredGaussianField_fieldChaosMass_measurable (P.prod P) (Ψ r) (hΨ r) ν h hh γ).ennreal_toReal.aemeasurable
  have hup := DOZZ.kahane_limit_field_negative_power P ((P.prod P).prod (gaussianReal 0 1))
    Φ (fun r u x => Ψ r u.1 x + c*u.2) hΦ
    (fun r => independent_common_scalar_add_isCenteredGaussianField (P.prod P) (Ψ r) (hΨ r) c)
    ν h hh hhb γ q hq
    (fun r => (hcross r).mono fun xy hb => hu r xy.1 xy.2 hb)
    (fun r => ae_of_all _ fun x => by simpa only [gaussianCovariance, pow_two] using hu r x x (fun he => False.elim (he Iff.rfl)))
    ZX (fun u => Real.exp (γ*c*u.2-γ^2/2*c^2)*ZY u.1) hXconv
    (reflected_common_scalar_field_limit (P.prod P) Ψ hΨ ν h γ c ZY hYconv)
  have hlo := DOZZ.kahane_limit_field_negative_power (P.prod P) (P.prod (gaussianReal 0 1))
    Ψ (fun r u x => Φ r u.1 x + c*u.2) hΨ
    (fun r => independent_common_scalar_add_isCenteredGaussianField P (Φ r) (hΦ r) c)
    ν h hh hhb γ q hq
    (fun r => (hcross r).mono fun xy hb => hl r xy.1 xy.2 hb)
    (fun r => ae_of_all _ fun x => by simpa only [gaussianCovariance, pow_two] using hl r x x (fun he => False.elim (he Iff.rfl)))
    ZY (fun u => Real.exp (γ*c*u.2-γ^2/2*c^2)*ZX u.1) hYconv
    (reflected_common_scalar_field_limit P Φ hΦ ν h γ c ZX hXconv)
  simp only [ENNReal.rpow_eq_pow] at hup hlo
  rw [reflected_common_scalar_moment (P.prod P) ZY hYm γ c (-q)] at hup
  rw [reflected_common_scalar_moment P ZX hXm γ c (-q)] at hlo
  simpa only [neg_sq, sub_neg_eq_add] using And.intro hup hlo

end DOZZ.Proofs
