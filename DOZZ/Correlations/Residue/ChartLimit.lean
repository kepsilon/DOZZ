/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ChartMass
public import DOZZ.Correlations.Residue.FullFromUnit

/-! Return from the separated finite-root chart to the exact unit-volume residue. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Exact normalization of the finite-chart moment residue. One critical root gives factor
2, while the coalesced pair gives factor 4. No large-position limiting theorem is used. -/
theorem residue_unit_limit_from_chart_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 m Rbar : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hmass : Tendsto (fun ε : ℝ => ε *
        (∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α3, α2] ![3, 7] (α3 - α2 + ε))
          (reflectionExponent γ α3 - ε / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 (m * γ * reflectionExponent γ α3 *
        (4 : ℝ) ^ (-(γ * α2 * reflectionExponent γ α3)) * Rbar))) :
    Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
      (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
      (𝓝 (2 * m * reflectionExponent γ α3 * Rbar)) := by
  let p := reflectionExponent γ α3
  have hs (ε : ℝ) : sExp γ α3 α2 (α3 - α2 + ε) = -p + ε / γ := by
    dsimp only [p]
    unfold sExp reflectionExponent
    ring
  have hexp (ε : ℝ) : -(γ * (α3 + α2 - (α3 - α2 + ε)) *
      sExp γ α3 α2 (α3 - α2 + ε) / 2) =
      -(γ * (2 * α2 - ε) * (-p + ε / γ) / 2) := by rw [hs]; ring
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hexplim : Tendsto (fun ε : ℝ =>
      -(γ * (2 * α2 - ε) * (-p + ε / γ) / 2)) (𝓝[>] 0) (𝓝 (γ * α2 * p)) := by
    have hl : Tendsto (fun ε : ℝ => 2 * α2 - ε) (𝓝[>] 0) (𝓝 (2 * α2)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub he : Tendsto (fun ε : ℝ => 2 * α2 - ε) (𝓝[>] 0) (𝓝 (2 * α2 - 0)))
    have hr : Tendsto (fun ε : ℝ => -p + ε / γ) (𝓝[>] 0) (𝓝 (-p)) := by
      simpa only [zero_div, add_zero] using
        (tendsto_const_nhds.add (he.div_const γ) : Tendsto (fun ε : ℝ => -p + ε / γ) (𝓝[>] 0) (𝓝 (-p + 0 / γ)))
    have hh := (((hl.const_mul γ).mul hr).div_const 2).neg
    convert hh using 1
    congr 1
    ring
  have hfactor := ((Real.continuous_const_rpow (by norm_num : (4 : ℝ) ≠ 0)).continuousAt.tendsto.comp hexplim).const_mul (2 / γ)
  have hprod := hfactor.mul hmass
  convert hprod using 1
  · ext ε
    rw [unitVolumeStructureConstant_swap13 P X M γ (α3 - α2 + ε) α2 α3 hγ hγ2 hX hM,
      residue_unitVolume_finite_chart P X M γ α3 α2 (α3 - α2 + ε) hγ hγ2 hX hM, hexp ε]
    rw [hs]
    have hq : -(-p + ε / γ) = p - ε / γ := by ring
    rw [hq]
    dsimp only [Function.comp_def, p]
    ring
  · have hpowers : (4 : ℝ) ^ (γ * α2 * p) * 4 ^ (-(γ * α2 * p)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4), add_neg_cancel, Real.rpow_zero]
    dsimp only [p] at hpowers
    congr 1
    symm
    dsimp only [p]
    calc _ = (2 * m * reflectionExponent γ α3 * Rbar) *
        ((4 : ℝ) ^ (γ * α2 * reflectionExponent γ α3) *
          (4 : ℝ) ^ (-(γ * α2 * reflectionExponent γ α3))) := by
            field_simp [hγ.ne']
      _ = _ := by rw [hpowers, mul_one]

end DOZZ.Proofs
