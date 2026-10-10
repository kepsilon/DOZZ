/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralUnitBlock.StoppingFactorization

/-!
# The stopped conditional unit-block estimate with the remaining lateral input explicit

The constant is chosen before the drift, the stopping time and the stopped event.
The sole additional analytic premise is the finite unit lateral inverse moment.
This internal theorem is not the unconditional statement
`DOZZ.brownian_lateralUnitBlock_conditional_inverse_bound_stopping`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The raw stopping-time form of the conditional unit-block estimate follows from the single
unit lateral inverse moment. -/
theorem lateralUnitBlock_conditional_inverse_bound_stopping_of_lateral_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → BrownianPath) (hBm : ∀ t : ℝ≥0, Measurable fun ω => B ω t)
    (hB : IsBrownianReal (fun t ω => B ω t) P)
    (γ q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hInd : IndepFun B Z P)
    (hMoment : (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : ℝ → ℝ, LipschitzWith (Real.toNNReal c) F →
    ∀ τ : Ω → ℝ≥0, IsBrownianStoppingTime B τ →
      ∀ G ∈ brownianStoppedEvents B τ, ∀ S : Set ℝ, MeasurableSet S →
        ∫⁻ ω, (G ∩ {ω | lateralUnitBlockEndpointIncrement B F (τ ω) ω ∈ S}).indicator
            (fun ω => ENNReal.rpow (lateralUnitBlockMass γ B F Z (τ ω) ω) (-q)) ω ∂P ≤
          ∫⁻ ω, (G ∩ {ω | lateralUnitBlockEndpointIncrement B F (τ ω) ω ∈ S}).indicator
            (fun ω => ENNReal.ofReal (C * (1 + Real.exp
              (-q * γ * lateralUnitBlockEndpointIncrement B F (τ ω) ω)))) ω ∂P := by
  classical
  have hmB : Measurable B := ContinuousMap.measurable_iff_eval.mpr hBm
  have hμ := lateralUnitBlock_brownianPath_map_isBrownian P B hB
  let D : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * q * γ * c))
  let K : ℝ≥0∞ := ∫⁻ p, lateralUnitBlock_bridgeWeight (q * γ) p ∂P.map B
  let L : ℝ≥0∞ := ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P
  have hK : K < ⊤ := lateralUnitBlock_bridge_exponential_moment_lt_top _ hμ (q * γ)
    (mul_nonneg hq.le hZ.1.le)
  have hfinite : D * K * L ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) hMoment).ne
  let C : ℝ := (D * K * L).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCeq : ENNReal.ofReal C = D * K * L := ENNReal.ofReal_toReal hfinite
  refine ⟨C, hC, ?_⟩
  intro F hF τ hτ G hG S hS
  let U : Ω → BrownianPath := fun ω => brownianShiftPath (τ ω) (B ω)
  let H : Ω → ℝ≥0 × ℝ := fun ω => (τ ω, G.indicator (fun _ => (1 : ℝ)) ω)
  have hmH : Measurable[(lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSpace] H :=
    (lateralUnitBlock_stoppingTime_measurable_stopped B hBm τ hτ).prodMk
      (measurable_const.indicator (lateralUnitBlock_stoppedEvent_measurableSpace B hBm τ hτ G hG))
  let d : ℝ≥0 → ℝ := fun a => F ((a : ℝ) + 1) - F a
  have hmd : Measurable d :=
    (hF.continuous.measurable.comp (NNReal.continuous_coe.measurable.add_const 1)).sub
      (hF.continuous.measurable.comp NNReal.continuous_coe.measurable)
  let w : (ℝ≥0 × ℝ) × ℝ → ℝ≥0∞ := fun z =>
    if z.1.2 = 1 ∧ z.2 + d z.1.1 ∈ S then
      ENNReal.ofReal (1 + Real.exp (-q * γ * (z.2 + d z.1.1))) else 0
  have hmval : Measurable (fun z : (ℝ≥0 × ℝ) × ℝ => z.2 + d z.1.1) :=
    measurable_snd.add (hmd.comp measurable_fst.fst)
  have hmw : Measurable w := Measurable.ite
    (((measurableSet_singleton (1 : ℝ)).preimage measurable_fst.snd).inter
      (hS.preimage hmval))
    (ENNReal.measurable_ofReal.comp (measurable_const.add
      (Real.measurable_exp.comp (measurable_const.mul hmval)))) measurable_const
  let v : Ω → ℝ := fun ω => lateralUnitBlockEndpointIncrement B F (τ ω) ω
  let E : Set Ω := G ∩ {ω | v ω ∈ S}
  have hendpoint (ω : Ω) : v ω = U ω 1 + d (τ ω) := by
    dsimp only [v]
    rw [lateralUnitBlock_endpoint_eq]
    change (B ω) (τ ω + 1) - (B ω) (τ ω) + F ((τ ω : ℝ) + 1) - F (τ ω) =
      (B ω) (τ ω + 1) - (B ω) (τ ω) + (F ((τ ω : ℝ) + 1) - F (τ ω))
    ring
  have hwpoint (ω : Ω) : w (H ω, U ω 1) =
      E.indicator (fun ω => ENNReal.ofReal (1 + Real.exp (-q * γ * v ω))) ω := by
    by_cases hω : ω ∈ G
    · simp [w, H, E, hω, hendpoint, Set.indicator_apply]
    · simp [w, H, E, hω, Set.indicator_apply]
  have hfactor := lateralUnitBlock_stopped_bridge_lateral_factor P B hBm hB γ Z hZ hInd τ hτ
    (q * γ) q (mul_nonneg hq.le hZ.1.le) H hmH w hmw
  have hbound : (∫⁻ ω, E.indicator
      (fun ω => (lateralUnitBlockMass γ B F Z (τ ω) ω) ^ (-q)) ω ∂P) ≤
      D * ∫⁻ ω, lateralUnitBlock_bridgeWeight (q * γ) (U ω) * w (H ω, U ω 1) *
        (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q) ∂P := by
    rw [← lintegral_const_mul' D _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hZ.2.2.2.2.1] with ω hω
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he, hwpoint, indicator_of_mem he]
      simpa only [lateralUnitBlock_bridgeWeight, D, U, v, mul_assoc] using
        lateralUnitBlock_unitBlockMass_inverse_le γ q c hZ.1.le hq.le hc B F hF Z (τ ω) ω
          (hω (τ ω) ((τ ω : ℝ) + 1)).ne
    · rw [indicator_of_notMem he]
      exact bot_le
  have hright : (∫⁻ ω, E.indicator
      (fun ω => ENNReal.ofReal (C * (1 + Real.exp (-q * γ * v ω)))) ω ∂P) =
      (D * K * L) * ∫⁻ ω, w (H ω, U ω 1) ∂P := by
    have he (ω : Ω) : E.indicator
        (fun ω => ENNReal.ofReal (C * (1 + Real.exp (-q * γ * v ω)))) ω =
        (D * K * L) * w (H ω, U ω 1) := by
      rw [hwpoint]
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω, indicator_of_mem hω, ENNReal.ofReal_mul hC, hCeq]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero]
    rw [lintegral_congr he]
    exact lintegral_const_mul' _ _ hfinite
  change (∫⁻ ω, E.indicator
      (fun ω => (lateralUnitBlockMass γ B F Z (τ ω) ω) ^ (-q)) ω ∂P) ≤ _
  rw [hright]
  rw [hfactor] at hbound
  simpa only [K, L, mul_assoc, mul_left_comm, mul_comm] using hbound

end DOZZ.Proofs
