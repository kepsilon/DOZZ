/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.CoefficientExtraction
public import DOZZ.FourPoint.Crossing.DiagonalUniqueness
public import DOZZ.FourPoint.Diagonal.Assembly
public import DOZZ.ShiftEquations.Shifts.Seeds.Reflection
public import DOZZ.Hypergeom.ClassificationDiagonalConnection
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Statements.FourPoint.DualCrossingMultiplier
public import DOZZ.Hypergeom.PhysicalRange
public import DOZZ.Statements.Hypergeom.GaussGPlus
public import DOZZ.Statements.Hypergeom.GaussGMinus
import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import Mathlib.Tactic

/-!
# The two channels of the dual degenerate four-point function

For charges `α, ε, α' < Q` with `α + ε + α' > 2Q + 2/γ`, the reduced four-point function with
the `-2/γ` insertion is diagonal in the basis at `0` (the classification
`DOZZ.degenerateFourPoint_diagonal_classification` at `χ = 2/γ` for `(α, ε, α')`) and, through the
exchange `z ↦ 1 - z` of its first two charges (`dual_fourPoint_reflection`), diagonal in the basis
at `1` (the same classification for `(ε, α, α')`). The connection matrix between the two bases
then fixes the four coefficients against each other; in particular the first zero-channel
coefficient `C(α - 2/γ, ε, α')` is the dual crossing multiplier times the second one-channel
coefficient `C(ε - 2/γ, α, α') ρ(ε, α, α')` ([KRV, Propositions 9.9 and 9.10], which proceed
along the same lines as [KRV, Proposition 9.8]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The dual Gauss parameters are symmetric in the first two charges, and the one-channel
parameter is `1 + a + b - c`. -/
theorem dual_channel_parameters (γ α ε α' : ℝ) (hγ : γ ≠ 0) :
    gaussParameterA γ (2 / γ) ε α α' = gaussParameterA γ (2 / γ) α ε α' ∧
      gaussParameterB γ (2 / γ) ε α α' = gaussParameterB γ (2 / γ) α ε α' ∧
      gaussParameterC γ (2 / γ) ε = 1 + gaussParameterA γ (2 / γ) α ε α' +
        gaussParameterB γ (2 / γ) α ε α' - gaussParameterC γ (2 / γ) α := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gaussParameterA
    ring
  · unfold gaussParameterB
    ring
  · unfold gaussParameterA gaussParameterB gaussParameterC Q
    field_simp
    ring

/-- **The one-channel form**: the classification for `(ε, α, α')`, read through `z ↦ 1 - z`, is a
diagonal form of the four-point function of `(α, ε, α')` in the basis at `1`. -/
theorem dual_one_channel_of_classification {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(2 / γ)) α ε α' z =
      structureConstant P M γ μ (ε - 2 / γ) α α' *
          ‖gaussGMinus H (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
            (gaussParameterC γ (2 / γ) α) z‖ ^ 2 +
        structureConstant P M γ μ (ε - 2 / γ) α α' *
          gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
            (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε) *
          ‖gaussGPlus H (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
            (gaussParameterC γ (2 / γ) α) z‖ ^ 2 := by
  obtain ⟨hA, hB, hC⟩ := dual_channel_parameters γ α ε α' hγ.ne'
  have h22 := degenerateFourPoint_diagonal_classification hH P X M γ μ (2 / γ) ε α α' hγ hγ2 hμ
    (Or.inr rfl) hε hα hα' (by linarith) hX hM
  intro z hz
  rw [dual_fourPoint_reflection P X M γ μ α ε α' hγ hγ2 hX hM z]
  have h := h22 (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz)
  rw [h, hA, hB]
  have hCC : (gaussParameterC γ (2 / γ) ε : ℂ) =
      1 + (gaussParameterA γ (2 / γ) α ε α' : ℂ) + (gaussParameterB γ (2 / γ) α ε α' : ℂ) -
        (gaussParameterC γ (2 / γ) α : ℂ) := by
    exact_mod_cast hC
  unfold gaussFMinus gaussFPlus gaussGMinus gaussGPlus
  rw [hCC]
  have hpow (A B C : ℂ) : 1 - (1 + A + B - C) = C - A - B := by ring
  have hplusA (A B C : ℂ) : A - (1 + A + B - C) + 1 = C - B := by ring
  have hplusB (A B C : ℂ) : B - (1 + A + B - C) + 1 = C - A := by ring
  have hplusC (A B C : ℂ) : 2 - (1 + A + B - C) = 1 + C - A - B := by ring
  rw [hpow, hplusA, hplusB, hplusC]
  ring

/-- **The first zero-channel coefficient from the second one-channel coefficient**:
`C(α - 2/γ, ε, α') = dualCrossingMultiplier(α', α, ε) · C(ε - 2/γ, α, α') ρ(ε, α, α')`, on the whole
seed domain, from the classification alone. -/
theorem dual_first_coefficient_of_classification {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    structureConstant P M γ μ (α - 2 / γ) ε α' =
      dualCrossingMultiplier γ α' α ε *
        (structureConstant P M γ μ (ε - 2 / γ) α α' *
          gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
            (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε)) := by
  obtain ⟨H, hH⟩ := DOZZ.Proofs.gauss_hypergeometric_exists
  let a := gaussParameterA γ (2 / γ) α ε α'
  let b := gaussParameterB γ (2 / γ) α ε α'
  let c := gaussParameterC γ (2 / γ) α
  let d₀ := structureConstant P M γ μ (α - 2 / γ) ε α'
  let d₁ := d₀ * gaussCoefficientRatio a b c
  let u := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v := Real.Gamma c * Real.Gamma (a + b - c) * (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  let e₀ := structureConstant P M γ μ (ε - 2 / γ) α α'
  let e₁ := e₀ * gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
    (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε)
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, _, hK₂⟩ :=
    DOZZ.Proofs.gauss_physical_parameter_range γ (2 / γ) α ε α' hγ hγ2 (Or.inr rfl) hs hα hε hα'
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < c := lt_trans hb hbc
  have ha1 : a < 1 := lt_trans (lt_trans hab hbc) hc1
  have hb1 : b < 1 := lt_trans hbc hc1
  have hcn : ∀ n : ℤ, c ≠ (n : ℝ) := by
    intro n hn
    have h0 : (0 : ℝ) < n := by rw [← hn]; exact hc
    have h1 : (n : ℝ) < 1 := by rw [← hn]; exact hc1
    have hn0 : (0 : ℤ) < n := by exact_mod_cast h0
    have hn1 : n < (1 : ℤ) := by exact_mod_cast h1
    omega
  have hδn : ∀ n : ℤ, c - a - b ≠ (n : ℝ) := by
    intro n hn
    have h0 : (0 : ℝ) < n := by rw [← hn]; exact hδ
    have h1 : (n : ℝ) < 1 := by rw [← hn]; exact hδ1
    have hn0 : (0 : ℤ) < n := by exact_mod_cast h0
    have hn1 : n < (1 : ℤ) := by exact_mod_cast h1
    omega
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
  have h22 := degenerateFourPoint_diagonal_classification hH P X M γ μ (2 / γ) α ε α' hγ hγ2 hμ
    (Or.inr rfl) hα hε hα' hs hX hM
  have hone := dual_one_channel_of_classification hH P X M γ μ α ε α' hγ hγ2 hμ hα hε hα' hs hX hM
  have he : ∀ z ∈ gaussCutPlane,
      (d₀ * u ^ 2 + d₁ * w ^ 2) * ‖gaussGMinus H a b c z‖ ^ 2 +
        (d₀ * v ^ 2 + d₁ * x ^ 2) * ‖gaussGPlus H a b c z‖ ^ 2 =
          e₀ * ‖gaussGMinus H a b c z‖ ^ 2 + e₁ * ‖gaussGPlus H a b c z‖ ^ 2 := by
    intro z hz
    calc
      _ = d₀ * ‖gaussFMinus H a b c z‖ ^ 2 + d₁ * ‖gaussFPlus H a b c z‖ ^ 2 :=
        (htransfer z hz).symm
      _ = fourPointT P M γ μ (-(2 / γ)) α ε α' z := by
        rw [h22 z hz]
        dsimp [d₁, d₀, a, b, c]
        ring
      _ = _ := by
        rw [hone z hz]
  have hE := (crossing_one_channel_coefficients_unique hH a b c
    (d₀ * u ^ 2 + d₁ * w ^ 2) (d₀ * v ^ 2 + d₁ * x ^ 2) e₀ e₁ hδn he).2.symm
  have hex := crossing_diagonal_coefficient_extraction a b c d₀ d₁ e₁
    ha ha1 hb hb1 hc hc1 hδ hδ1 hcn hδn hcross hE
  have hM' : lR a * lR b / (lR c * lR (a + b - c)) = dualCrossingMultiplier γ α' α ε := by
    unfold dualCrossingMultiplier
    simp only [lFun_ofReal_re_eq_lR]
    rfl
  rw [hM'] at hex
  exact hex

end DOZZ.Proofs

end
