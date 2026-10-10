/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.LateralComparisonError
public import DOZZ.FourPoint.Dual.SpatialGuard
import Mathlib.Tactic
/-! A signed quantitative decoupling bound for the actual separated dual masses. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The supplied dual mass on the two separated regions, averaged at inverse order `q`. -/
noncomputable def dualSeparatedInverseMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ q : ℝ) (z : ℂ) (s r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ x in reflected_innerRegion s,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)+
    (∫⁻ x in reflected_outerRegion r,
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω))^(-q) ∂P

/-- The same separated observable with independent inner and outer lateral copies. -/
noncomputable def dualCopiedSeparatedInverseMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (N : Ω → Measure ℂ)
    (γ α₁ α₂ α₃ q : ℝ) (z : ℂ) (s r : ℝ) : ℝ≥0∞ :=
  let J := fun U (a : TwoSidedPath) ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
  ∫⁻ v : TwoSidedPath × (Ω × Ω),
    (J (reflected_innerRegion s) v.1 v.2.1+
      J (reflected_outerRegion r) v.1 v.2.2)^(-q)
      ∂(P.map (originRadialPath Xc)).prod (P.prod P)

/-- The actual signed decoupling error is uniformly at most a constant times the relative
radius. Finiteness of both expectations follows from the supplied GMC's fixed disk moments. -/
theorem dual_source_decoupling_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun v : ℂ × ℝ => Xc ω v.1 v.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s r : ℝ,
      0 < s → 0 < r → r ≤ 1 → s/r ≤ 1/2 →
      (3*γ^2/2*(q^2+q))*(s/r) ≤ 1 →
      ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
        (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
        N =ᵐ[P] (fun ω => (M ω).withDensity
          (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
        |(dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z s r).toReal-
          (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z s r).toReal| ≤ C*(s/r) := by
  obtain ⟨C₀, hC₀, hguard⟩ := dual_spatial_guard_inverse_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q hq.le
  let d := 3*γ^2/2*(q^2+q)
  have hd : 0 < d := by dsimp only [d]; positivity
  refine ⟨(2*Real.exp 1*C₀)*d, by positivity, ?_⟩
  intro z hz s r hs hr hr1 hsep ht1
  obtain ⟨N, hN, hi, hfin, heq, hcmp⟩ := dual_source_separated_regions_comparison
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM α₁ α₂ α₃ z hz s r hs hr hr1 hsep q hq
  refine ⟨N, hN, hi, hfin, heq, ?_⟩
  have hD := (reflected_separated_region_geometry s r hs hr hr1 hsep).2.2.2.2.2.2.2.2
  have ha : dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z s r ≤ ENNReal.ofReal C₀ := by
    apply le_trans (lintegral_mono ?_) (hguard z hz)
    intro ω
    have hb : (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω) ≤
        (∫⁻ x in reflected_innerRegion s,
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)+
        (∫⁻ x in reflected_outerRegion r,
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω) :=
      (lintegral_mono_set hD).trans (le_add_left le_rfl)
    dsimp only
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hb hq.le)
  have hex : γ^2*(3*(s/r))/2*(q^2+q) = d*(s/r) := by dsimp only [d]; ring
  dsimp only at hcmp
  rw [hex] at hcmp
  have hb := dual_lateral_comparison_real_bound
    (dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z s r)
    (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z s r)
    (d*(s/r)) C₀ (mul_nonneg hd.le (div_pos hs hr).le) ht1 hC₀.le ha hcmp.1 hcmp.2
  convert hb using 1
  ring

end DOZZ.Proofs
