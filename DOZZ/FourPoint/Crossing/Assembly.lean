/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.OneChannel
public import DOZZ.FourPoint.Crossing.CoefficientExtraction
public import DOZZ.FourPoint.Crossing.DiagonalUniqueness
public import DOZZ.FourPoint.Crossing.Multiplier
public import DOZZ.FourPoint.Crossing.Normalization
public import DOZZ.Statements.Correlations.UnitVolumeStructureConstantSymmetricExtended
public import DOZZ.Hypergeom.ClassificationDiagonalConnection
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients
import Mathlib.Tactic

/-! # Crossing coefficient assembly with both analytic inputs visible

The two premises are literal specializations of the conclusions of
`degenerateFourPoint_diagonal_classification` and
`gammaHalf_full_unreflected_formula`. This is not the unconditional proof of
`DOZZ.gammaHalf_crossing`, nor a reduction from the unreflected formula alone. The global
zero-channel classification remains an additional BPZ input.
-/

public section
open MeasureTheory
namespace DOZZ.Proofs

/-- With the original diagonal classification and the admissible epsilon-channel
unreflected formula, the connection matrix gives both literal crossing identities. -/
theorem gammaHalf_crossing_of_diagonal_and_unreflected {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hεhi : ε < 2 / γ) (hα : α < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiagonal :
      let a := gaussParameterA γ (γ / 2) α' ε α
      let b := gaussParameterB γ (γ / 2) α' ε α
      let c := gaussParameterC γ (γ / 2) α'
      ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) α' ε α z =
        structureConstant P M γ μ (α' - γ / 2) ε α *
          (‖gaussFMinus H a b c z‖ ^ 2 + gaussCoefficientRatio a b c *
            ‖gaussFPlus H a b c z‖ ^ 2))
    (hformula :
      let a := gaussParameterA γ (γ / 2) ε α' α
      let b := gaussParameterB γ (γ / 2) ε α' α
      let c := gaussParameterC γ (γ / 2) ε
      ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) ε α' α z =
        structureConstant P M γ μ (ε - γ / 2) α' α * ‖gaussFMinus H a b c z‖ ^ 2 +
        (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re) *
          structureConstant P M γ μ (ε + γ / 2) α' α * ‖gaussFPlus H a b c z‖ ^ 2) :
    structureConstant P M γ μ (α' - γ / 2) ε α =
      gammaHalfCrossingMultiplier γ μ α' ε α *
        structureConstant P M γ μ α' (ε + γ / 2) α ∧
    unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
      gammaHalfUnitCrossingMultiplier γ μ α' ε α *
        unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by
  let a := gaussParameterA γ (γ / 2) α' ε α
  let b := gaussParameterB γ (γ / 2) α' ε α
  let c := gaussParameterC γ (γ / 2) α'
  let d₀ := structureConstant P M γ μ (α' - γ / 2) ε α
  let d₁ := d₀ * gaussCoefficientRatio a b c
  let u := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v := Real.Gamma c * Real.Gamma (a + b - c) * (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  let e₀ := structureConstant P M γ μ (ε - γ / 2) α' α
  let Bε := -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re
  let e₁ := Bε * structureConstant P M γ μ (ε + γ / 2) α' α
  have hεQ : ε < Q γ := by unfold Q; linarith only [hεhi, hγ]
  have hsum : 2 * Q γ + γ / 2 < α' + ε + α := by linarith only [hs]
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, _, hK₂⟩ :=
    DOZZ.gauss_physical_parameter_range γ (γ / 2) α' ε α hγ hγ2 (Or.inl rfl)
      hsum hα' hεQ hα
  obtain ⟨hcn, hδn, _⟩ := crossing_gammaHalf_parameter_guards γ α' ε α hγ hγ2 hεhi hα' hα hs
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < c := lt_trans hb hbc
  have ha1 : a < 1 := lt_trans (lt_trans hab hbc) hc1
  have hb1 : b < 1 := lt_trans hbc hc1
  have hratio := gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero a b c hK₂.ne'
  have hconstraint : gaussK₁ a b c * d₀ + gaussK₂ a b c * d₁ = 0 := by
    dsimp [d₁]
    linear_combination d₀ * hratio
  have hcross : d₀ * u * v + d₁ * w * x = 0 := by
    calc
      _ = Real.Gamma (c - a - b) * Real.Gamma (a + b - c) *
          (gaussK₁ a b c * d₀ + gaussK₂ a b c * d₁) := by
        dsimp [u, v, w, x, gaussK₁, gaussK₂]
        ring
      _ = 0 := by rw [hconstraint, mul_zero]
  have htransfer := gauss_diagonal_one_basis_of_constraint hH a b c d₀ d₁ hcn hδn hconstraint
  have hone := gammaHalf_one_channel_of_full_unreflected H P X M γ μ α' ε α hγ hγ2 hX hM hformula
  have he : ∀ z ∈ gaussCutPlane,
      (d₀ * u ^ 2 + d₁ * w ^ 2) * ‖gaussGMinus H a b c z‖ ^ 2 +
        (d₀ * v ^ 2 + d₁ * x ^ 2) * ‖gaussGPlus H a b c z‖ ^ 2 =
          e₀ * ‖gaussGMinus H a b c z‖ ^ 2 + e₁ * ‖gaussGPlus H a b c z‖ ^ 2 := by
    intro z hz
    calc
      _ = d₀ * ‖gaussFMinus H a b c z‖ ^ 2 + d₁ * ‖gaussFPlus H a b c z‖ ^ 2 :=
        (htransfer z hz).symm
      _ = fourPointT P M γ μ (-γ / 2) α' ε α z := by
        rw [hdiagonal z hz]
        dsimp [d₁, d₀, a, b, c]
        ring
      _ = _ := hone z hz
  have hE := (crossing_one_channel_coefficients_unique hH a b c
    (d₀ * u ^ 2 + d₁ * w ^ 2) (d₀ * v ^ 2 + d₁ * x ^ 2) e₀ e₁ hδn he).2.symm
  have hex := crossing_diagonal_coefficient_extraction a b c d₀ d₁ e₁
    ha ha1 hb hb1 hc hc1 hδ hδ1 hcn hδn hcross hE
  have hswap : structureConstant P M γ μ (ε + γ / 2) α' α =
      structureConstant P M γ μ α' (ε + γ / 2) α := by
    rw [residue_structureConstant_eq_unitVolume, residue_structureConstant_eq_unitVolume]
    have heS : sExp γ (ε + γ / 2) α' α = sExp γ α' (ε + γ / 2) α := by
      unfold sExp
      congr 1
      ring
    have hpQ : ε + γ / 2 < Q γ := by unfold Q; linarith only [hεhi]
    have hpS : 0 < sExp γ (ε + γ / 2) α' α := by
      unfold sExp
      apply div_pos _ hγ
      linarith only [hs, hγ]
    have hdom : ExtendedSeiberg3 γ (ε + γ / 2) α' α := by
      refine ⟨hpQ, hα', hα, ?_⟩
      apply lt_trans (neg_neg_of_pos hpS)
      apply lt_min
      · positivity
      · apply lt_min
        · exact mul_pos (div_pos (by norm_num) hγ) (sub_pos.mpr hpQ)
        · apply lt_min
          · exact mul_pos (div_pos (by norm_num) hγ) (sub_pos.mpr hα')
          · exact mul_pos (div_pos (by norm_num) hγ) (sub_pos.mpr hα)
    have hsym := DOZZ.unitVolumeStructureConstant_symmetric_extended
      P X M γ (ε + γ / 2) α' α hγ hγ2 hX hM hdom
    rw [heS, hsym.1]
  have hfull : structureConstant P M γ μ (α' - γ / 2) ε α =
      gammaHalfCrossingMultiplier γ μ α' ε α *
        structureConstant P M γ μ α' (ε + γ / 2) α := by
    dsimp [e₁, Bε] at hex
    rw [hswap, ← mul_assoc, crossing_connection_times_fusion γ μ α' ε α] at hex
    exact hex
  exact ⟨hfull, gammaHalf_crossing_unit_of_full P M γ μ α' ε α hγ hμ hs hfull⟩

end DOZZ.Proofs
