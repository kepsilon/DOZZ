/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.ReflectionCutMoments
public import DOZZ.Brownian.LateralMoments.UnitInverse
import Mathlib.Tactic
/-! Positivity of each literal Williams last-cut mass on the same reflection data. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The initial positive unit block makes every actual last-cut reflection mass positive;
its finite full mass supplies the simultaneous upper guard. -/
theorem dual_reflection_cut_positive_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α c : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z) :
    ∀ᵐ ω ∂P, 0 < twoSidedReflectionCutMass γ c B Z ω ∧
      twoSidedReflectionCutMass γ c B Z ω < ⊤ := by
  have hZ := hData.2.1
  have hBm := conditionedPair_aemeasurable P B (Q γ-α) hData.1
  have hZm := hZ.2.2.2.1
  have hm := twoSidedReflectionCutMass_aemeasurable P γ c B Z hBm hZm hZ.2.2.2.2.1
  have hi : IndepFun (fun ω => (B ω).1) Z P :=
    hData.2.2.comp₀ hBm hZm measurable_fst.aemeasurable measurable_id.aemeasurable
  obtain ⟨C, hC, hb⟩ := initialUnitBlockMass_inverse_moment_le P γ (Q γ-α) 1 hγ
    zero_lt_one Z hZm hZ.2.2.2.2.1
  have hbound := hb (Q γ-α) le_rfl (fun ω => (B ω).1) hData.1.1 hi
  have hblock : (∫⁻ ω, initialUnitBlockMass γ (B ω).1 (Z ω)^(-(1 : ℝ)) ∂P) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top hC
      (lateralGMC_unit_inverse_moment_lt_top P γ Z hZ 1 zero_lt_one))
  have hInv : (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^(-(1 : ℝ)) ∂P) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
        (initialUnitBlockMass_le_cutMass γ c B Z ω) (by norm_num : (0 : ℝ) ≤ 1))) hblock
  filter_upwards [ae_lt_top' (hm.pow_const (-(1 : ℝ))) hInv.ne,
    reflected_reflection_mass_positive_finite_ae P γ α B Z hγ hγ₂ hα hData] with ω hInv hfull
  constructor
  · apply pos_iff_ne_zero.mpr
    intro he
    rw [he, ENNReal.zero_rpow_of_neg (by norm_num : -(1 : ℝ) < 0)] at hInv
    exact lt_irrefl _ hInv
  · exact (twoSidedReflectionCutMass_le_mass γ c B Z ω).trans_lt hfull.2

end DOZZ.Proofs
