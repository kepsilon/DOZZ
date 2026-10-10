/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.DeletedMoment
public import DOZZ.FourPoint.ReflectedOuter.MovingMoment
public import DOZZ.FourPoint.ReflectedOuter.Rates
import Mathlib.Tactic

/-! # The reflected outer correction on the full buffer range

Rooting the deleted disk gives `r^(κ+δ)`, and relative kernel perturbation on the retained region
gives `‖z‖/r = ‖z‖^ξ`, with `r = ‖z‖^(1-ξ)`. The inequalities `hfreeze` and `hslack` make both
rates little-o of `‖z‖^κ`. No estimate requires `ξ < 1/2`.
-/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The literal outer inverse moment has the reflected little-o rate. -/
theorem gammaHalf_reflected_outer_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hreflect : Q γ - α₁ < γ / 2)
    (hslack : γ * (Q γ - α₁) < ξ)
    (hfreeze : γ * (Q γ - α₁) <
      (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsComplexLittleOAtZero (γ * (Q γ - α₁))
      (fun z : ℂ =>
        ((gammaHalfOuterMoment P M γ α₁ α₂ α₃
            ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) z ξ -
          gammaHalfMoment P M γ α₁ α₂ α₃
            ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) 0 : ℝ) : ℂ)) := by
  let p : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  let e : ℝ := γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  obtain ⟨Cd, εd, _, hεd, hdb⟩ := reflected_retainedZero_deleted_moment_bound
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hα₂ hα₃ hreflect hs hX hM
  obtain ⟨Cm, _, hmb⟩ := reflected_outer_moving_moment_bound
    P X M γ α₁ α₂ α₃ p hγ hγ₂ hp (by linarith only [hα₁, hγ]) hα₂ hα₃ hX hM
  apply reflected_outer_rate_littleO (γ * (Q γ - α₁)) ξ e Cm Cd _ hslack hfreeze
  filter_upwards [reflected_outer_cutoff_geometry ξ εd hξ hξ₂ hεd,
    self_mem_nhdsWithin] with z hz hz0
  obtain ⟨hr, hr₁, hz₁, hsep, hrε⟩ := hz
  have hdel := hdb (‖z‖ ^ (1 - ξ)) hr hrε
  have hmov := hmb z ξ hr hr₁ hz₁ hsep
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have he : ‖z‖ / ‖z‖ ^ (1 - ξ) = ‖z‖ ^ ξ := by
    have hh := Real.rpow_sub hnz 1 (1 - ξ)
    rw [Real.rpow_one, show (1 : ℝ) - (1 - ξ) = ξ by ring] at hh
    exact hh.symm
  rw [he] at hmov
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        (∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) (M ω)) ^ (-p) ∂P).toReal| +
      |(∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) (M ω)) ^ (-p) ∂P).toReal -
        gammaHalfMoment P M γ α₁ α₂ α₃ p 0| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hmov hdel

end DOZZ.Proofs
