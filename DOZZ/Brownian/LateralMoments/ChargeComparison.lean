/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseGamma
public import DOZZ.GMC.FieldGaussianCommonScalar

/-! Uniform charge comparison on bounded charts, including different source fields. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- The circle covariance has a cutoff-independent lower bound on a bounded chart. -/
theorem latmom_circle_covariance_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (x y : ℂ) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    -(Real.log (2*R+1) + gmcCircleChartRemainder R) ≤
      ∫ ω, Xc ω x r * Xc ω y r ∂P := by
  have hlo := circleField_covariance_ge_log P X hX Xc hXc R r hR hr x y hx hy
  have hm : max ‖x-y‖ (Real.exp (-r)) ≤ 2*R+1 := by
    apply max_le
    · linarith [norm_sub_le x y]
    · have he : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
      linarith only [he, hR]
  have hmpos : 0 < max ‖x-y‖ (Real.exp (-r)) :=
    (Real.exp_pos _).trans_le (le_max_right _ _)
  have hlog := Real.log_le_log hmpos hm
  rw [Real.log_div (by norm_num) hmpos.ne', Real.log_one] at hlo
  change -(Real.log (2*R+1) + (Real.log 3 + 2*Real.log (1+R))) ≤ _
  linarith only [hlo, hlog]

/-- Adding one independent Gaussian scalar to the larger charge dominates every smaller
charge on a bounded chart. The constant is independent of the smaller field and charge. -/
theorem latmom_cutoff_charge_domination
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X X₀ : Ω → Distr)
    (hX : IsEquatorGFF P X) (hX₀ : IsEquatorGFF P X₀)
    (Xc Xc₀ : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (hXc₀ : IsCircleAverage P X₀ Xc₀)
    (γ g : ℝ) (hγ : 0 < γ) (hγg : γ ≤ g)
    (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ) (hR : 0 ≤ R)
    (hAR : ∀ x ∈ A, ‖x‖ ≤ R) (p : ℝ) (hp : p ≤ 0 ∨ 1 ≤ p)
    (r : ℝ) (hr : 0 ≤ r) :
    gmcMassMoment P (regularizedGMC P Xc γ r) A p ≤
      ENNReal.ofReal (Real.exp (g ^ 2 *
        (Real.log (2*R+1) + gmcCircleChartRemainder R) / 2 * (p ^ 2-p))) *
      gmcMassMoment P (regularizedGMC P Xc₀ g r) A p := by
  have hg : 0 < g := hγ.trans_le hγg
  let D := Real.log (2*R+1) + gmcCircleChartRemainder R
  have hD : 0 ≤ D := add_nonneg (Real.log_nonneg (by linarith))
    (gmcCircleChartRemainder_nonneg hR)
  let c := γ/g
  have hc0 : 0 ≤ c := div_nonneg hγ.le hg.le
  have hc1 : c ≤ 1 := (div_le_one hg).mpr hγg
  have hc2 : c ^ 2 ≤ 1 := by nlinarith only [hc0, hc1]
  let ν := gmcReferenceMeasure.restrict A
  have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hΦ := circleAverage_smul_isCenteredGaussianField P X hX Xc hXc r c
  have hΨ := circleAverage_isCenteredGaussianField P X₀ hX₀ Xc₀ hXc₀ r
  let Ψ : Ω × ℝ → ℂ → ℝ := fun ω x => Xc₀ ω.1 x r + Real.sqrt D * ω.2
  have hΨc := independent_common_scalar_add_isCenteredGaussianField
    P (fun ω x => Xc₀ ω x r) hΨ (Real.sqrt D)
  have heq (x y : ℂ) : (∫ ω, Xc ω x r * Xc ω y r ∂P) =
      ∫ ω, Xc₀ ω x r * Xc₀ ω y r ∂P := by
    rw [circleField_covariance_eq P X hX Xc hXc,
      circleField_covariance_eq P X₀ hX₀ Xc₀ hXc₀]
  have hcov (x y : ℂ) (hx : x ∈ A) (hy : y ∈ A) :
      (∫ ω, c * Xc ω x r * (c * Xc ω y r) ∂P) ≤
      ∫ ω, Ψ ω x * Ψ ω y ∂P.prod (gaussianReal 0 1) := by
    have hfun : (fun ω => c * Xc ω x r * (c * Xc ω y r)) =
        fun ω => c ^ 2 * (Xc ω x r * Xc ω y r) := by funext ω; ring
    rw [hfun, integral_const_mul, heq]
    have hscalar := gaussianCovariance_field_independent_common_scalar_add
      P (fun ω x => Xc₀ ω x r) hΨ (Real.sqrt D) x y
    change (∫ ω, Ψ ω x * Ψ ω y ∂P.prod (gaussianReal 0 1)) =
      (∫ ω, Xc₀ ω x r * Xc₀ ω y r ∂P) + (Real.sqrt D)^2 at hscalar
    rw [hscalar, Real.sq_sqrt hD]
    have hlo := latmom_circle_covariance_lower_bound
      P X₀ hX₀ Xc₀ hXc₀ R r hR hr x y (hAR x hx) (hAR y hy)
    change -D ≤ _ at hlo
    have hnonneg := mul_nonneg (sub_nonneg.mpr hc2) (show 0 ≤
      (∫ ω, Xc₀ ω x r * Xc₀ ω y r ∂P) + D from by linarith only [hlo])
    nlinarith only [hnonneg, hD, sq_nonneg c]
  have hprod : ν.prod ν = (gmcReferenceMeasure.prod gmcReferenceMeasure).restrict (A ×ˢ A) :=
    by dsimp [ν]; rw [Measure.prod_restrict]
  have hcovAE : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, c * Xc ω xy.1 r * (c * Xc ω xy.2 r) ∂P) ≤
        ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂P.prod (gaussianReal 0 1) := by
    rw [hprod]
    filter_upwards [ae_restrict_mem (hA.prod hA)] with xy hxy
    exact hcov xy.1 xy.2 hxy.1 hxy.2
  have hdiagAE : ∀ᵐ x ∂ν,
      (∫ ω, (c * Xc ω x r)^2 ∂P) ≤ ∫ ω, Ψ ω x ^ 2 ∂P.prod (gaussianReal 0 1) := by
    filter_upwards [ae_restrict_mem hA] with x hx
    simpa only [pow_two] using hcov x x hx hx
  have hk := kahane_field_power_convex P (P.prod (gaussianReal 0 1))
    (fun ω x => c * Xc ω x r) Ψ hΦ hΨc ν (fun _ => 1)
      measurable_const ⟨1, fun _ => le_rfl⟩ g p hp hcovAE hdiagAE
  have hfactor := fieldChaosMoment_independent_common_scalar_factor P
    (fun ω x => Xc₀ ω x r) hΨ ν (fun _ => 1) measurable_const
    ⟨1, fun _ => le_rfl⟩ g (Real.sqrt D) p
  rw [Real.sq_sqrt hD] at hfactor
  rw [hfactor] at hk
  simpa only [c, ν, D, gmcMassMoment, ENNReal.rpow_eq_pow, regularizedGMC_apply_eq_fieldChaosMass_scaled
    P X hX Xc hXc γ g r hg.ne' A hA,
    regularizedGMC_apply_eq_fieldChaosMass P X₀ hX₀ Xc₀ hXc₀ g r A hA] using hk

end DOZZ.Proofs
end
