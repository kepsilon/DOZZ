/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.WilliamsBounds
public import DOZZ.Statements.Brownian.LastoneBrownianSmallPowerLimit

/-! The critical small-power limit of the exponential-maximum last-cut model. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Williams' independent maximum/conditioned-copy model has critical moment tending to `2`. The
lower bound uses the retained unit block and the upper bound the full-mass small-power theorem
`lastone_brownian_smallPower_limit`. -/
theorem lastone_williamsModel_smallPower_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (Z : Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → IndepFun (B ν) Z P) :
    Tendsto (fun ν => (∫⁻ z : ℝ × Ω,
      williamsMassFunctional γ
        (((z.1, negativeConditionedLastExitSegment z.1 (B ν z.2).2),
          (B ν z.2).1), Z z.2) ^ (ν / γ)
            ∂(brownianMaximumReferenceLaw ν).prod P).toReal)
      (𝓝[>] 0) (𝓝 2) := by
  let : IsProbabilityMeasure P := hZ.2.2.1
  let I : ℝ → ℝ≥0∞ := fun ν => ∫⁻ ω, twoSidedReflectionMass γ (B ν) Z ω ^ (ν / γ) ∂P
  let J : ℝ → ℝ≥0∞ := fun ν => ∫⁻ ω, initialUnitBlockMass γ (B ν ω).1 (Z ω) ^ (ν / γ) ∂P
  let W : ℝ → ℝ≥0∞ := fun ν => ∫⁻ z : ℝ × Ω,
    williamsMassFunctional γ
      (((z.1, negativeConditionedLastExitSegment z.1 (B ν z.2).2),
        (B ν z.2).1), Z z.2) ^ (ν / γ)
          ∂(brownianMaximumReferenceLaw ν).prod P
  have hI : Tendsto (fun ν => (I ν).toReal) (𝓝[>] 0) (𝓝 1) :=
    DOZZ.lastone_brownian_smallPower_limit P γ hγ hγ2 Z B
      hB hZ hInd
  have he : Tendsto (fun ν : ℝ => ν / γ) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.div_const γ :
      Tendsto (fun ν : ℝ => ν / γ) (𝓝 0) (𝓝 (0 / γ))).mono_left nhdsWithin_le_nhds
  have hJ : Tendsto (fun ν => (J ν).toReal) (𝓝[>] 0) (𝓝 1) :=
    lastone_initialUnitBlock_smallPower_limit P γ 1 hγ one_pos Z B
      (fun ν hν _ => hB ν hν) hZ (fun ν hν _ => hInd ν hν)
      (fun ν => ν / γ) he (fun ν hν => div_pos hν hγ)
  have hunif := lastone_positiveDrift_uniform_moments P γ 1 hγ
    Z B (fun ν hν _ => hB ν hν) hZ (fun ν hν _ => hInd ν hν)
  obtain ⟨u, hu, C, hC, hCbound⟩ := hunif.1
  have hsmall : ∀ᶠ ν in 𝓝[>] (0 : ℝ), 0 < ν ∧ ν < 1 ∧ ν / γ ≤ u := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
      he.eventually (eventually_le_nhds hu)] with ν hν heν
    exact ⟨hν.1, hν.2, heν⟩
  have hbounds : ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      2 * (J ν).toReal ≤ (W ν).toReal ∧ (W ν).toReal ≤ 2 * (I ν).toReal := by
    filter_upwards [hsmall] with ν hν
    have hIfin : I ν < ⊤ := by
      have hb : I ν ≤ 1 + C := by
        calc
          I ν ≤ ∫⁻ ω, 1 + twoSidedReflectionMass γ (B ν) Z ω ^ u ∂P :=
            lintegral_mono fun ω => ennreal_rpow_le_one_add_rpow _
              (div_pos hν.1 hγ).le hν.2.2
          _ = 1 + ∫⁻ ω, twoSidedReflectionMass γ (B ν) Z ω ^ u ∂P := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ 1 + C := add_le_add le_rfl (hCbound ν hν.1 hν.2.1.le)
      exact lt_of_le_of_lt hb (ENNReal.add_lt_top.mpr ⟨by norm_num, hC⟩)
    have h2Ifin : (2 : ℝ≥0∞) * I ν ≠ ⊤ :=
      (ENNReal.mul_lt_top (by norm_num) hIfin).ne
    have hb := lastone_williamsModel_moment_bounds P γ ν hγ hν.1 (B ν) Z
      (aemeasurable_of_twoSidedConditioned (hB ν hν.1)) hZ.2.2.2.1 hZ.2.2.2.2.1
    change 2 * J ν ≤ W ν ∧ W ν ≤ 2 * I ν at hb
    have hWfin := ne_top_of_le_ne_top h2Ifin hb.2
    have hlow := ENNReal.toReal_mono hWfin hb.1
    have hupp := ENNReal.toReal_mono h2Ifin hb.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using And.intro hlow hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun ν => 2 * (J ν).toReal) (h := fun ν => 2 * (I ν).toReal)
  · simpa using hJ.const_mul 2
  · simpa using hI.const_mul 2
  · exact hbounds.mono fun ν hν => hν.1
  · exact hbounds.mono fun ν hν => hν.2

end DOZZ.Proofs
