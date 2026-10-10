/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentReg
public import DOZZ.FourPoint.BPZ.WirtingerMass
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.Statements.Hypergeom.IsRealGaussSolution

/-! # The reduced four-point function: versions, moments and derivatives

* A measurable version of the GMC measure is a GMC measure with the same reduced function.
* Off `0` and `1`, the reduced function `T` is `K E[I^{-s}]` with
  `K = 2 μ^{-s} Γ(s)/γ`, `I` the degenerate four-point mass and `s` the Seiberg exponent.
* `T` is twice continuously differentiable off `0` and `1`, and its Wirtinger derivatives are
  `K` times the Wirtinger functionals of the expectations of the moment fields. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- An almost sure version of a GMC measure, with finite values, is a GMC measure. -/
theorem bpz_isGMCOf_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Distr}
    {M N : Ω → Measure ℂ} (hM : IsGMCOf P X γ M) (hNfin : ∀ ω, IsFiniteMeasure (N ω))
    (hMN : ∀ᵐ ω ∂P, M ω = N ω) : IsGMCOf P X γ N := by
  obtain ⟨-, Xc, hXc, hconv⟩ := hM
  refine ⟨hNfin, Xc, hXc, fun f => TendstoInMeasure.congr_right ?_ (hconv f)⟩
  filter_upwards [hMN] with ω h
  rw [h]

/-- The reduced function only depends on the almost sure class of the measure. -/
theorem bpz_fourPointT_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {M N : Ω → Measure ℂ} (hMN : ∀ᵐ ω ∂P, M ω = N ω) (μ α₀ : ℝ) (z : ℂ) :
    fourPointT P M γ μ α₀ α₁ α₂ α₃ z = fourPointT P N γ μ α₀ α₁ α₂ α₃ z := by
  unfold fourPointT
  have h : (∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α₀, α₁, α₂] ![z, 0, 1] α₃)
      (-fourPointSExp γ α₀ α₁ α₂ α₃) ∂P) =
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (N ω) ![α₀, α₁, α₂] ![z, 0, 1] α₃)
        (-fourPointSExp γ α₀ α₁ α₂ α₃) ∂P :=
    lintegral_congr_ae (hMN.mono fun ω h => by dsimp only; rw [h])
  rw [h]

/-- Off `0` and `1`, the reduced function is `K E[I^{-s}]`. -/
theorem bpz_fourPointT_eq_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (μ : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
      2 * μ ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) / γ * Real.Gamma (fourPointSExp γ (-χ) α₁ α₂ α₃) *
        ∫ ω, bpzSoftMassReal (γ * χ / 2) 0 (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ^
          (-fourPointSExp γ (-χ) α₁ α₂ α₃) ∂P := by
  rw [fourPointT_eq_bpzMass P X hX hγ hγ2 M hM μ z]
  congr 1
  have hmeas : AEStronglyMeasurable (fun ω => bpzSoftMassReal (γ * χ / 2) 0
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃)) P :=
    (((bpz_measurable_softMassReal _ 0 measurable_bpzBaseWeight z).comp hMm).pow_const
      _).aestronglyMeasurable
  have h0 : 0 ≤ᵐ[P] fun ω => bpzSoftMassReal (γ * χ / 2) 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (M ω) z ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (bpzSoftI_nonneg 0 _ z) _
  rw [integral_eq_lintegral_of_nonneg_ae h0 hmeas]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [bpzMass_pos_ae P X hX hγ hγ2 M hM 0 le_rfl zero_le_one z,
    bpzMass_lt_top_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ 0 z hz0 hz1] with ω hpos hfin
  have hI : bpzSoftMassReal (γ * χ / 2) 0 (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z =
      (bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z).toReal := bpzSoftI_eq_toReal 0 (M ω) z
  rw [hI, ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hpos.ne' hfin.ne),
    ENNReal.ofReal_toReal hfin.ne]
  rfl

/-- **Regularity of the reduced function.** Off `0` and `1` the reduced function is `C²`, and its
Wirtinger derivatives are `K` times the Wirtinger functionals of the expectations of the moment
fields. -/
theorem bpz_fourPointT_contDiff_wirtinger {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 0 < fourPointSExp γ (-χ) α₁ α₂ α₃) (μ : ℝ) :
    ContDiffOn ℝ 2 (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z) {z : ℂ | z ≠ 0 ∧ z ≠ 1} ∧
    ∀ z ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1},
      wirtingerZ (fun w => (fourPointT P M γ μ (-χ) α₁ α₂ α₃ w : ℂ)) z =
        ((2 * μ ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) / γ *
          Real.Gamma (fourPointSExp γ (-χ) α₁ α₂ α₃) : ℝ) : ℂ) *
          bpzWirtL (∫ ω, bpzMomField1 (γ * χ / 2) (fourPointSExp γ (-χ) α₁ α₂ α₃) 0
            (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) ∧
      wirtingerZ (wirtingerZ (fun w => (fourPointT P M γ μ (-χ) α₁ α₂ α₃ w : ℂ))) z =
        ((2 * μ ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) / γ *
          Real.Gamma (fourPointSExp γ (-χ) α₁ α₂ α₃) : ℝ) : ℂ) *
          bpzWirt2L (∫ ω, bpzMomField2 (γ * χ / 2) (fourPointSExp γ (-χ) α₁ α₂ α₃) 0
            (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) := by
  set s := fourPointSExp γ (-χ) α₁ α₂ α₃ with hs_def
  set K : ℝ := 2 * μ ^ (-s) / γ * Real.Gamma s with hK
  set F0 : ℂ → ℝ := fun z => ∫ ω, bpzSoftMassReal (γ * χ / 2) 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
    (M ω) z ^ (-s) ∂P with hF0
  set F1 : ℂ → ℂ →L[ℝ] ℝ := fun z => ∫ ω, bpzMomField1 (γ * χ / 2) s 0
    (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P with hF1
  set F2 : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun z => ∫ ω, bpzMomField2 (γ * χ / 2) s 0
    (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P with hF2
  set U : Set ℂ := {z : ℂ | z ≠ 0 ∧ z ≠ 1} with hU
  have hUo : IsOpen U := bpz_isOpen_regularPlane
  obtain ⟨hd1, hd2⟩ := bpz_hasFDerivAt_moments P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs
  have hEq : ∀ z ∈ U, fourPointT P M γ μ (-χ) α₁ α₂ α₃ z = K * F0 z := fun z hz =>
    bpz_fourPointT_eq_moment P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ μ hz.1 hz.2
  have hTd : ∀ z ∈ U, HasFDerivAt (fun w => fourPointT P M γ μ (-χ) α₁ α₂ α₃ w) (K • F1 z) z := by
    intro z hz
    refine ((hd1 z hz).const_mul K).congr_of_eventuallyEq ?_
    filter_upwards [hUo.mem_nhds hz] with w hw using hEq w hw
  have hD : ∀ z ∈ U, HasFDerivAt (fun w => K • F1 w) (K • F2 z) z := fun z hz =>
    (hd2 z hz).const_smul K
  have hc2 : ContinuousOn (fun w => K • F2 w) U :=
    (bpz_continuousOn_momField2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le).const_smul K
  refine ⟨bpz_contDiffOn_two_of hUo hTd hD hc2, fun z hz => ⟨?_, ?_⟩⟩
  · rw [bpz_wirtingerZ_ofReal (hTd z hz), bpzWirtL_apply]
    simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  · rw [bpz_wirtingerZ_wirtingerZ_ofReal hUo hz hTd (hD z hz), bpzWirt2L_apply]
    simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring

end DOZZ.Proofs
