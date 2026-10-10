/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.SmallPower
public import DOZZ.Brownian.Reflection.Moments
public import DOZZ.Brownian.Reflection.LastCut
public import DOZZ.Brownian.LateralMoments.UnitInverse

/-! The lower Williams bound at the critical endpoint. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The positive unit block is retained in the full reflection mass. -/
theorem lastone_initialUnitBlockMass_le
    {Ω : Type*} (γ : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (ω : Ω) :
    initialUnitBlockMass γ (B ω).1 (Z ω) ≤ twoSidedReflectionMass γ B Z ω := by
  exact (initialUnitBlockMass_le_cutMass γ 0 B Z ω).trans
    (twoSidedReflectionCutMass_le_mass γ 0 B Z ω)

/-- The initial conditioned unit block has small-power expectation tending to one, uniformly
through the zero-drift endpoint. This is the lower bound used after Williams disintegration. -/
theorem lastone_positiveDrift_uniform_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₀ : ℝ) (hγ : 0 < γ)
    (Z : Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → IndepFun (B ν) Z P) :
    (∃ u : ℝ, 0 < u ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∫⁻ ω, twoSidedReflectionMass γ (B ν) Z ω ^ u ∂P ≤ C) ∧
    ∀ v : ℝ, 0 < v → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∫⁻ ω, initialUnitBlockMass γ (B ν ω).1 (Z ω) ^ (-v) ∂P ≤ C := by
  obtain ⟨C, hC, hCb⟩ := twoSidedReflectionMass_rpow_lintegral_le_zeroDrift P γ ν₀ (1 / 2)
    hγ (by norm_num) (by norm_num) Z hZ.2.2.2.1 hZ.2.2.2.2.1
    (lateralGMC_singleton_ae P γ Z hZ 0) _
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    (lateralGMC_Icc_unit_moment_le_intensity P γ (1 / 2) Z hZ (by norm_num) (by norm_num))
  refine ⟨⟨1 / 2, by norm_num, C, hC, fun ν hν hν₀' =>
    hCb ν hν₀' (B ν) (hB ν hν hν₀') (hInd ν hν hν₀')⟩, ?_⟩
  intro v hv
  obtain ⟨Cv, hCv, hCvb⟩ := initialUnitBlockMass_inverse_moment_le P γ ν₀ v hγ hv Z
    hZ.2.2.2.1 hZ.2.2.2.2.1
  refine ⟨Cv * ∫⁻ ω, Z ω (Icc 0 1) ^ (-v) ∂P,
    ENNReal.mul_lt_top hCv (lateralGMC_unit_inverse_moment_lt_top P γ Z hZ v hv), ?_⟩
  intro ν hν hν₀'
  exact hCvb ν hν₀' (fun ω => (B ν ω).1) (hB ν hν hν₀').1
    ((hInd ν hν hν₀').comp measurable_fst measurable_id)

/-- The initial unit-block critical moment requires only the positive-drift family, so it
applies directly to the supplied-space source witness. -/
theorem lastone_initialUnitBlock_smallPower_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ν₀ : ℝ) (hγ : 0 < γ) (hν₀ : 0 < ν₀)
    (Z : Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → IndepFun (B ν) Z P)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hepos : ∀ ν : ℝ, 0 < ν → 0 < e ν) :
    Tendsto (fun ν => (∫⁻ ω,
      initialUnitBlockMass γ (B ν ω).1 (Z ω) ^ e ν ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  let : IsProbabilityMeasure P := hZ.2.2.1
  have hmom := lastone_positiveDrift_uniform_moments P γ ν₀ hγ Z B hB hZ hInd
  obtain ⟨u, hu, Cu, hCu, hUb⟩ := hmom.1
  obtain ⟨Cv, hCv, hVb⟩ := hmom.2 1 one_pos
  let J : ℝ → Ω → ℝ≥0∞ := fun ν ω => initialUnitBlockMass γ (B ν ω).1 (Z ω)
  have hJm (ν : ℝ) (hν : 0 < ν) (hν₀' : ν ≤ ν₀) : AEMeasurable (J ν) P :=
    initialUnitBlockMass_aemeasurable P γ (fun ω => (B ν ω).1) Z
      (hB ν hν hν₀').1.1 hZ.2.2.2.1 hZ.2.2.2.2.1
  have hJU (ν : ℝ) (hν : 0 < ν) (hν₀' : ν ≤ ν₀) :
      ∫⁻ ω, J ν ω ^ u ∂P ≤ Cu := by
    exact (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (lastone_initialUnitBlockMass_le γ (B ν) Z ω) hu.le).trans (hUb ν hν hν₀')
  have hJV (ν : ℝ) (hν : 0 < ν) (hν₀' : ν ≤ ν₀) :
      ∫⁻ ω, J ν ω ^ (-1 : ℝ) ∂P ≤ Cv := hVb ν hν hν₀'
  have hIoo : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν ∈ Ioo 0 ν₀ := Ioo_mem_nhdsGT hν₀
  apply lastone_smallPower_moment_tendsto_one P J (𝓝[>] 0) e u 1 hu one_pos
    Cu Cv hCu hCv he
  · exact hIoo.mono fun ν hν => hepos ν hν.1
  · exact hIoo.mono fun ν hν => hJm ν hν.1 hν.2.le
  · filter_upwards [hIoo] with ν hν
    have hm := hJm ν hν.1 hν.2.le
    have hpospow := ae_lt_top'
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hm)
      (lt_of_le_of_lt (hJU ν hν.1 hν.2.le) hCu).ne
    have hinvpow := ae_lt_top'
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hm)
      (lt_of_le_of_lt (hJV ν hν.1 hν.2.le) hCv).ne
    filter_upwards [hpospow, hinvpow] with ω hU hV
    change J ν ω ^ u < ⊤ at hU
    change J ν ω ^ (-1 : ℝ) < ⊤ at hV
    constructor
    · apply pos_iff_ne_zero.mpr
      intro h0
      rw [h0, ENNReal.zero_rpow_of_neg (by norm_num)] at hV
      exact lt_irrefl _ hV
    · apply lt_top_iff_ne_top.mpr
      intro ht
      rw [ht, ENNReal.top_rpow_of_pos hu] at hU
      exact lt_irrefl _ hU
  · exact hIoo.mono fun ν hν => hJU ν hν.1 hν.2.le
  · exact hIoo.mono fun ν hν => hJV ν hν.1 hν.2.le

end DOZZ.Proofs
