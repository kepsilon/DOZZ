/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralUnitBlock.Factorization

/-!
# The Brownian part of the conditional unit-block estimate, with the lateral input explicit

This internal lemma derives the exact conditional estimate from the single lateral inverse
moment. The real constant is chosen before every Lipschitz drift and block location. It is
not the unconditional statement `DOZZ.brownian_lateralUnitBlock_conditional_inverse_bound`:
finiteness of the lateral moment remains an input.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The only analytic input in this conditional unit-block estimate is the unit lateral inverse
moment. -/
theorem lateralUnitBlock_conditional_inverse_bound_of_lateral_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → BrownianPath) (hB : IsBrownianReal (fun t ω => B ω t) P)
    (γ q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hInd : IndepFun B Z P)
    (hMoment : (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : ℝ → ℝ, LipschitzWith (Real.toNNReal c) F →
    ∀ a : ℝ≥0,
      ConditionalLIntegralBound P
        (lateralUnitBlockEndpointIncrement B F a)
        (fun ω => ENNReal.rpow (lateralUnitBlockMass γ B F Z a ω) (-q))
        (fun v => ENNReal.ofReal (C * (1 + Real.exp (-q * γ * v)))) := by
  classical
  have hBm : AEMeasurable B P := aemeasurable_brownianPath_of_eval hB.aemeasurable
  have hμB := lateralUnitBlock_brownianPath_map_isBrownian P B hB
  let D : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * q * γ * c))
  let K : ℝ≥0∞ := ∫⁻ p, lateralUnitBlock_bridgeWeight (q * γ) p ∂P.map B
  let L : ℝ≥0∞ := ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P
  have hK : K < ⊤ := lateralUnitBlock_bridge_exponential_moment_lt_top _ hμB (q * γ)
    (mul_nonneg hq.le hZ.1.le)
  have hfinite : D * K * L ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) hMoment).ne
  let C : ℝ := (D * K * L).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCeq : ENNReal.ofReal C = D * K * L := ENNReal.ofReal_toReal hfinite
  refine ⟨C, hC, ?_⟩
  intro F hF a
  have hloc : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω) := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω
    exact fun n => hω (-(n : ℝ)) n
  have hm := lateralUnitBlock_unitBlockMass_aemeasurable P γ B hBm F hF.continuous.measurable
    Z hZ.2.2.2.1 (fun _ => a) aemeasurable_const hloc
  have ht := lateralUnitBlock_endpoint_aemeasurable P B hBm F hF.continuous.measurable
    (fun _ => a) aemeasurable_const
  refine ⟨ht, ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hm,
    by fun_prop, ?_⟩
  intro A hA
  change (∫⁻ ω, (if lateralUnitBlockEndpointIncrement B F a ω ∈ A then
      (lateralUnitBlockMass γ B F Z a ω) ^ (-q) else 0) ∂P) ≤ _
  let d : ℝ := F ((a : ℝ) + 1) - F a
  let w : ℝ → ℝ≥0∞ := fun n => if n + d ∈ A then
    ENNReal.ofReal (1 + Real.exp (-q * γ * (n + d))) else 0
  have hw : Measurable w := Measurable.ite
    (hA.preimage (measurable_id.add_const d)) (by fun_prop) measurable_const
  have hendpoint (ω : Ω) : lateralUnitBlockEndpointIncrement B F a ω =
      brownianShiftPath a (B ω) 1 + d := by
    rw [lateralUnitBlock_endpoint_eq]
    change (B ω) (a + 1) - (B ω) a + F ((a : ℝ) + 1) - F a =
      (B ω) (a + 1) - (B ω) a + (F ((a : ℝ) + 1) - F a)
    ring
  have hbound : (∫⁻ ω, (if lateralUnitBlockEndpointIncrement B F a ω ∈ A then
      (lateralUnitBlockMass γ B F Z a ω) ^ (-q) else 0) ∂P) ≤
      D * ∫⁻ ω, lateralUnitBlock_bridgeWeight (q * γ) (brownianShiftPath a (B ω)) *
        w (brownianShiftPath a (B ω) 1) *
        (Z ω (Icc (a : ℝ) ((a : ℝ) + 1))) ^ (-q) ∂P := by
    rw [← lintegral_const_mul' D _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hZ.2.2.2.2.1] with ω hω
    by_cases hv : lateralUnitBlockEndpointIncrement B F a ω ∈ A
    · rw [ite_eq_left hv]
      have hwω : w (brownianShiftPath a (B ω) 1) =
          ENNReal.ofReal (1 + Real.exp (-q * γ * lateralUnitBlockEndpointIncrement B F a ω)) := by
        dsimp [w]
        rw [← hendpoint, ite_eq_left hv]
      rw [hwω]
      simpa only [lateralUnitBlock_bridgeWeight, D, mul_assoc] using
        lateralUnitBlock_unitBlockMass_inverse_le γ q c hZ.1.le hq.le hc B F hF Z a ω
          (hω a ((a : ℝ) + 1)).ne
    · rw [ite_eq_right hv]
      exact bot_le
  have hfactor := lateralUnitBlock_bridge_lateral_endpoint_factor P B hB γ Z hZ hInd a (q * γ) q w hw
  have hright : (∫⁻ ω, (if lateralUnitBlockEndpointIncrement B F a ω ∈ A then
      ENNReal.ofReal (C * (1 + Real.exp (-q * γ * lateralUnitBlockEndpointIncrement B F a ω)))
      else 0) ∂P) =
      (D * K * L) * ∫⁻ ω, w (brownianShiftPath a (B ω) 1) ∂P := by
    have hpoint (ω : Ω) : (if lateralUnitBlockEndpointIncrement B F a ω ∈ A then
        ENNReal.ofReal (C * (1 + Real.exp (-q * γ * lateralUnitBlockEndpointIncrement B F a ω)))
        else 0) = (D * K * L) * w (brownianShiftPath a (B ω) 1) := by
      rw [hendpoint]
      dsimp [w]
      split_ifs
      · rw [ENNReal.ofReal_mul hC, hCeq]
      · rw [mul_zero]
    rw [lintegral_congr hpoint]
    exact lintegral_const_mul' _ _ hfinite
  rw [hfactor] at hbound
  rw [hright]
  simpa only [K, L, mul_assoc, mul_left_comm, mul_comm] using hbound

end DOZZ.Proofs

end
