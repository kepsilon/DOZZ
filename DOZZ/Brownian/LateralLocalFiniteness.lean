/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Statements.Brownian.LateralProjectedGMC
public import DOZZ.Statements.Defs.IsGMCOf
import Mathlib.Topology.Order.Compact

/-!
# Local finiteness of the polar lateral projection

On a compact logarithmic-radius interval the radial Wick weight is bounded, since the radial
path is continuous. A finite plane measure therefore has finite projected mass on every bounded
interval. This is one carrier condition needed for the lateral GMC layer.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The polar projection of a finite source measure has finite mass on every compact interval.
The bound depends on the compact interval and the continuous radial path. -/
theorem lateralProjectedGMC_Icc_ne_top
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) [IsFiniteMeasure M]
    (a b : ℝ) :
    lateralProjectedGMC γ A M (Set.Icc a b) < ⊤ := by
  by_cases hab : a ≤ b
  · obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hab) (continuous_abs.comp A.continuous).continuousOn
    let K : ℝ := |A s₀|
    let R : ℝ := max |a| |b|
    let C : ℝ := |γ| * K + |γ * Q γ| * R
    have hK_nonneg : 0 ≤ K := abs_nonneg _
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hweight (x : ℂ)
        (hx : -Real.log ‖x‖ ∈ Set.Icc a b) :
        ENNReal.ofReal (if ‖x‖ = 0 then 0 else
          Real.exp (-γ * A (-Real.log ‖x‖) +
            γ * Q γ * |Real.log ‖x‖|)) ≤ ENNReal.ofReal (Real.exp C) := by
      by_cases hx0 : ‖x‖ = 0
      · simp [hx0]
      · have hs : -Real.log ‖x‖ ∈ Set.Icc a b := hx
        have hAs : |A (-Real.log ‖x‖)| ≤ K := by
          have h := (isMaxOn_iff.mp hmax) (-Real.log ‖x‖) hs
          simpa [K, Function.comp_apply] using h
        have hlog : |Real.log ‖x‖| ≤ R := by
          have hleft : a ≤ -Real.log ‖x‖ := hs.1
          have hright : -Real.log ‖x‖ ≤ b := hs.2
          have hlowR : -R ≤ -Real.log ‖x‖ := by
            dsimp [R]
            calc
              -max |a| |b| ≤ -|a| := neg_le_neg (le_max_left _ _)
              _ ≤ a := neg_abs_le a
              _ ≤ -Real.log ‖x‖ := hleft
          have hupR : -Real.log ‖x‖ ≤ R := by
            dsimp [R]
            exact hright.trans ((le_abs_self b).trans (le_max_right _ _))
          have habs : abs (-Real.log ‖x‖) ≤ R := abs_le.mpr ⟨hlowR, hupR⟩
          simpa [abs_neg] using habs
        have hexp : -γ * A (-Real.log ‖x‖) +
            γ * Q γ * |Real.log ‖x‖| ≤ C := by
          dsimp [C]
          calc
            -γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|
                ≤ abs (-γ * A (-Real.log ‖x‖)) +
                    abs (γ * Q γ * abs (Real.log ‖x‖)) :=
                    add_le_add (le_abs_self _) (le_abs_self _)
            _ = abs γ * abs (A (-Real.log ‖x‖)) +
                  abs (γ * Q γ) * abs (Real.log ‖x‖) := by
                  rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_abs]
            _ ≤ abs γ * K + abs (γ * Q γ) * R := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hAs (abs_nonneg _))
                    (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
        have hexp' : Real.exp (-γ * A (-Real.log ‖x‖) +
              γ * Q γ * |Real.log ‖x‖|) ≤ Real.exp C :=
          Real.exp_le_exp.mpr hexp
        simpa [hx0] using ENNReal.ofReal_le_ofReal hexp'
    let ρ : ℂ → ℝ := fun x => -Real.log ‖x‖
    let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (if ‖x‖ = 0 then 0 else
      Real.exp (-γ * A (ρ x) + γ * Q γ * |Real.log ‖x‖|))
    have hρ : Measurable ρ := measurable_neg.comp (Real.measurable_log.comp measurable_norm)
    have hpre : MeasurableSet (ρ ⁻¹' Set.Icc a b) :=
      measurableSet_Icc.preimage hρ
    unfold lateralProjectedGMC
    change (M.withDensity w).map ρ (Set.Icc a b) < ⊤
    rw [Measure.map_apply hρ measurableSet_Icc,
      withDensity_apply w hpre]
    have hmono :
        (∫⁻ x in ρ ⁻¹' Set.Icc a b, w x ∂M) ≤
          ∫⁻ x in ρ ⁻¹' Set.Icc a b, ENNReal.ofReal (Real.exp C) ∂M := by
      apply setLIntegral_mono' hpre
      intro x hx
      exact hweight x hx
    exact lt_of_le_of_lt hmono (by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top M _))
  · have hempty : Set.Icc a b = ∅ := Set.Icc_eq_empty hab
    have hρ : Measurable (fun x : ℂ => -Real.log ‖x‖) :=
      measurable_neg.comp (Real.measurable_log.comp measurable_norm)
    rw [lateralProjectedGMC, Measure.map_apply hρ measurableSet_Icc, hempty]
    simp

/-- A finite random GMC source and any samplewise continuous radial path give the almost-sure
compact-interval finiteness clause of the lateral carrier. -/
theorem ae_lateralProjectedGMC_interval_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (A : Ω → TwoSidedPath) (M : Ω → Measure ℂ)
    (hM : ∀ ω, IsFiniteMeasure (M ω)) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ,
      lateralProjectedGMC γ (A ω) (M ω) (Set.Icc a b) < ⊤ := by
  exact Filter.Eventually.of_forall fun ω a b => by
    exact @lateralProjectedGMC_Icc_ne_top γ (A ω) (M ω) (hM ω) a b

end DOZZ.Proofs

end
