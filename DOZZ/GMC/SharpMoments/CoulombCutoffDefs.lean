/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.RegularizedCoulombMass
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.GMC.Moments.InversionCutoff
public import DOZZ.GMC.SharpMoments.LocationTransfer

/-! # The regularized Coulomb mass as a single-chart integral

The inverted-chart cutoff chaos is the image of the circle-average cutoff chaos under complex
inversion, so the regularized Coulomb mass is the integral of one explicit weight against the
circle-average cutoff chaos: the finite-chart weight times the finite partition function plus the
inverted-chart weight, evaluated at the inverted point, times the inverted partition function. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The finite-chart softened Coulomb weight at cutoff `r`. -/
noncomputable def coulombCutoffFiniteWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) (x : ℂ) : ℝ≥0∞ :=
  (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / (‖x - z k‖ + Real.exp (-r)))) (γ * α k)) *
    ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf)

/-- The inverted-chart softened Coulomb weight at cutoff `r`. -/
noncomputable def coulombCutoffInfinityWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) (u : ℂ) : ℝ≥0∞ :=
  (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus u / (‖1 - z k * u‖ + Real.exp (-r))))
      (γ * α k)) *
    ENNReal.rpow (ENNReal.ofReal (normPlus u / (‖u‖ + Real.exp (-r)))) (γ * αinf)

/-- The single-chart regularized Coulomb weight. -/
noncomputable def coulombCutoffWeight (partition : GMCChartPartition) {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ) : ℝ≥0∞ :=
  (partition.finiteWeight x : ℝ≥0∞) * coulombCutoffFiniteWeight γ α z αinf r x +
    (partition.infinityWeight x⁻¹ : ℝ≥0∞) * coulombCutoffInfinityWeight γ α z αinf r x⁻¹

theorem measurable_coulombCutoffFiniteWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) : Measurable (coulombCutoffFiniteWeight γ α z αinf r) := by
  unfold coulombCutoffFiniteWeight
  simp only [ENNReal.rpow_eq_pow]
  refine Measurable.mul (Finset.measurable_prod _ fun k _ => ?_) ?_
  · exact (ENNReal.measurable_ofReal.comp (measurable_normPlus.div
      ((measurable_id.sub_const (z k)).norm.add_const _))).pow_const _
  · exact (ENNReal.measurable_ofReal.comp measurable_normPlus).pow_const _

theorem measurable_coulombCutoffInfinityWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) : Measurable (coulombCutoffInfinityWeight γ α z αinf r) := by
  unfold coulombCutoffInfinityWeight
  simp only [ENNReal.rpow_eq_pow]
  refine Measurable.mul (Finset.measurable_prod _ fun k _ => ?_) ?_
  · exact (ENNReal.measurable_ofReal.comp (measurable_normPlus.div
      ((measurable_const.sub (measurable_const.mul measurable_id)).norm.add_const _))).pow_const _
  · exact (ENNReal.measurable_ofReal.comp (measurable_normPlus.div
      (measurable_norm.add_const _))).pow_const _

theorem measurable_coulombCutoffWeight (partition : GMCChartPartition) {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) :
    Measurable (coulombCutoffWeight partition γ α z αinf r) := by
  unfold coulombCutoffWeight
  refine Measurable.add ?_ ?_
  · exact (partition.finiteWeight.continuous.measurable.coe_nnreal_ennreal).mul
      (measurable_coulombCutoffFiniteWeight γ α z αinf r)
  · exact ((partition.infinityWeight.continuous.measurable.comp measurable_inv).coe_nnreal_ennreal).mul
      ((measurable_coulombCutoffInfinityWeight γ α z αinf r).comp measurable_inv)

/-- The regularized Coulomb mass integrates the single-chart weight against the circle-average
cutoff chaos. -/
theorem regularizedCoulombMass_eq_lintegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (partition : GMCChartPartition) {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ)
    (ω : Ω) :
    regularizedCoulombMass P Xc γ partition α z αinf r ω =
      ∫⁻ x, coulombCutoffWeight partition γ α z αinf r x ∂regularizedGMC P Xc γ r ω := by
  let _ := hX.1
  have hV : Measurable (fun x : ℂ => ∫ ω', Xc ω' x r ^ 2 ∂P) := by
    have hf : Measurable (fun q : ℂ × Ω => Xc q.2 q.1 r ^ 2) :=
      ((hXc.1 r).comp measurable_swap).pow_const 2
    exact hf.stronglyMeasurable.integral_prod_right.measurable
  have hX1 : Measurable (fun x : ℂ => Xc ω x r) :=
    (hXc.1 r).comp (measurable_const.prodMk measurable_id)
  have hwick : Measurable (fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hX1.const_mul γ).sub (hV.const_mul _)))
  have hfin : Measurable fun x : ℂ => (partition.finiteWeight x : ℝ≥0∞) *
      coulombCutoffFiniteWeight γ α z αinf r x :=
    (partition.finiteWeight.continuous.measurable.coe_nnreal_ennreal).mul
      (measurable_coulombCutoffFiniteWeight γ α z αinf r)
  have hinf : Measurable fun u : ℂ => (partition.infinityWeight u : ℝ≥0∞) *
      coulombCutoffInfinityWeight γ α z αinf r u :=
    (partition.infinityWeight.continuous.measurable.coe_nnreal_ennreal).mul
      (measurable_coulombCutoffInfinityWeight γ α z αinf r)
  unfold regularizedCoulombMass
  rw [← regularizedGMC_map_complexInv P Xc γ r ω hwick]
  have h1 : (∫⁻ x, (partition.finiteWeight x : ℝ≥0∞) *
      (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / (‖x - z k‖ + Real.exp (-r)))) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) ∂regularizedGMC P Xc γ r ω) =
      ∫⁻ x, (partition.finiteWeight x : ℝ≥0∞) * coulombCutoffFiniteWeight γ α z αinf r x
        ∂regularizedGMC P Xc γ r ω := by
    apply lintegral_congr
    intro x
    rw [coulombCutoffFiniteWeight, mul_assoc]
  have h2 : (∫⁻ u, (partition.infinityWeight u : ℝ≥0∞) *
      (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus u / (‖1 - z k * u‖ + Real.exp (-r))))
        (γ * α k)) * ENNReal.rpow (ENNReal.ofReal (normPlus u / (‖u‖ + Real.exp (-r))))
          (γ * αinf) ∂(regularizedGMC P Xc γ r ω).map (fun x : ℂ => x⁻¹)) =
      ∫⁻ x, (partition.infinityWeight x⁻¹ : ℝ≥0∞) * coulombCutoffInfinityWeight γ α z αinf r x⁻¹
        ∂regularizedGMC P Xc γ r ω := by
    rw [lintegral_map _ measurable_inv]
    · apply lintegral_congr
      intro x
      rw [coulombCutoffInfinityWeight, mul_assoc]
    · convert hinf using 1
      funext u
      rw [coulombCutoffInfinityWeight, mul_assoc]
  rw [h1, h2, ← lintegral_add_left hfin]
  rfl

end DOZZ.Proofs
