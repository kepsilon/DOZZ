/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceRadialSignedExpectation
public import DOZZ.FourPoint.Reflected.SourceKernelExpectation
public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
public import DOZZ.FourPoint.ReflectedOuter.Rates
/-! The actual source Williams expectation squeezes the literal full inverse-moment difference. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_williams_kernel_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N) (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ)
    (B : Ω → BrownianPath × BrownianPath)
    (hL : IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (hData : IsReflectionData P γ α₁ B (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw (Q γ-α₁) Qν)
    (p : ℝ) (hp : 0 < p) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hh : 0 < h) :
    let W := fun z : ℂ => ∫ v : Ω × (ℝ × Ω),
      ((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        reflected_radial_scale γ (Q γ-α₁) h Xc z v.1*Real.exp (γ*v.2.1)*
          (twoSidedReflectionCutMass γ v.2.1 B
            (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) v.2.2).toReal)^(-p)-
        (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)
      ∂P.prod ((brownianMaximumReferenceLaw (Q γ-α₁)).prod P)
    let E := fun z : ℂ => gammaHalfMoment P M γ α₁ α₂ α₃ p z-
      (reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
        (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) p).toReal
    ∀ᶠ z : ℂ in 𝓝[≠] 0,
      max 1 ((1+Real.exp (-h))^(γ^2/2)*(1-Real.exp (-h)*‖z‖)⁻¹^|γ*α₂|)*W z+E z ≤
        gammaHalfMoment P M γ α₁ α₂ α₃ p z-gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ ∧
      gammaHalfMoment P M γ α₁ α₂ α₃ p z-gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ ≤
        min 1 ((1-Real.exp (-h))^(γ^2/2)*(1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α₂|))*W z+E z := by
  let R := Real.exp (-h)
  have hR : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hh)
  filter_upwards [reflected_outer_cutoff_geometry ξ 1 hξ hξ1 zero_lt_one,self_mem_nhdsWithin]
    with z hz hz0
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hr1 : ‖z‖^(1-ξ) ≤ 1 := hz.2.2.2.2.le
  have hzr : ‖z‖ < ‖z‖^(1-ξ) := by linarith only [hz.1,hz.2.2.2.1]
  have hzn : ‖z‖ < 1 := hzr.trans_le hr1
  have hz1 : z ≠ 1 := by intro he; simp [he] at hzn
  let T := Real.toNNReal (-Real.log ‖z‖+h)
  have hcoord : (T : ℝ) = -Real.log ‖z‖+h := Real.coe_toNNReal _
    (add_nonneg (neg_nonneg.mpr (Real.log_nonpos hn.le hzn.le)) hh.le)
  have hη : Real.exp (-(T : ℝ)) = R*‖z‖ := by
    rw [hcoord,neg_add,neg_neg,Real.exp_add,Real.exp_log hn,mul_comm]
  have hη1 : Real.exp (-(T : ℝ)) < 1 := by
    rw [hη]
    exact (mul_le_of_le_one_left hn.le hR1.le).trans_lt hzn
  have hTr : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ) := by
    rw [hη]
    exact (mul_le_of_le_one_left hn.le hR1.le).trans hzr.le
  have hk := reflected_source_copied_kernel_inverse_squeeze P X hX Xc hc hcont γ hγ hγ₂ M hM
    N hN hi heq hfin α₁ α₂ α₃ ξ p R hp hα₁ hα₂ hα₃ z hz0 hz1 hzn.le hz.1 hzr hr1 T
    hR.le hR1 hη1 hη.le
  have hw := reflected_source_copied_radial_signed_expectation P X hX Xc hc hm hcont γ hγ hγ₂ M hM
    N hN hi heq hfin α₁ α₂ α₃ ξ h hα₁ B hL hData Qν hQν z hz0 T hcoord hz.1 hzr hTr p hp.le
    hα₂ hα₃ hz1 hzn.le hr1
  dsimp only at hk
  change (∫⁻ ω : Ω × Ω, (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ+
    ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in reflected_innerRegion (Real.exp (-(T : ℝ))),
      ENNReal.ofReal (‖x‖^(-(γ*α₁)))*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))^(-p) ∂P.prod P).toReal-
      (∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal = _ at hw
  rw [hw,hη] at hk
  dsimp only [R] at hk
  let C := (reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
    (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) p).toReal
  let O := (∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal
  let F := gammaHalfMoment P M γ α₁ α₂ α₃ p z
  change max 1 ((1+Real.exp (-h))^(γ^2/2)*(1-Real.exp (-h)*‖z‖)⁻¹^|γ*α₂|)*_+(F-C) ≤ F-O ∧
    F-O ≤ min 1 ((1-Real.exp (-h))^(γ^2/2)*(1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α₂|))*_+(F-C)
  change max 1 ((1+Real.exp (-h))^(γ^2/2)*(1-Real.exp (-h)*‖z‖)⁻¹^|γ*α₂|)*_ ≤ C-O ∧
    C-O ≤ min 1 ((1-Real.exp (-h))^(γ^2/2)*(1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α₂|))*_ at hk
  constructor <;> linarith only [hk.1,hk.2]

end DOZZ.Proofs
