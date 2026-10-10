/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.ZeroMass
public import DOZZ.GMC.Annulus.BallCover
import Mathlib.Tactic

/-! # Positivity, finiteness, and the literal deleted-disk splitting -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained zero mass equals its real-kernel integral when the fixed roots have no atoms. -/
theorem reflected_retainedZero_kernel_integral (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    reflectedRetainedZeroMass γ α₁ α₂ α₃ r μ =
      ∫⁻ x in {x : ℂ | r ≤ ‖x‖}, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ := by
  let D : Set ℂ := {x | r ≤ ‖x‖}
  have h0r : (μ.restrict D) {0} = 0 := by
    apply le_zero_iff.mp
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact (measure_mono inter_subset_left).trans_eq h0
  have h1r : (μ.restrict D) {1} = 0 := by
    apply le_zero_iff.mp
    rw [Measure.restrict_apply (measurableSet_singleton 1)]
    exact (measure_mono inter_subset_left).trans_eq h1
  exact (gammaHalfMass_eq_coulombMass γ α₁ α₂ α₃ 0 (μ.restrict D) h0r h0r h1r).symm

/-- The retained zero mass is bounded by the full zero mass without any atom hypothesis. -/
theorem reflected_retainedZero_le_full (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ) :
    reflectedRetainedZeroMass γ α₁ α₂ α₃ r μ ≤
      coulombMass γ μ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ :=
  lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

/-- The full zero mass splits into the retained mass and exactly the deleted open disk. -/
theorem reflected_retainedZero_split (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    coulombMass γ μ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ =
      reflectedRetainedZeroMass γ α₁ α₂ α₃ r μ +
        ∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ := by
  rw [← gammaHalfMass_eq_coulombMass γ α₁ α₂ α₃ 0 μ h0 h0 h1,
    reflected_retainedZero_kernel_integral γ α₁ α₂ α₃ r μ h0 h1]
  have hc : ({x : ℂ | r ≤ ‖x‖} : Set ℂ)ᶜ = Metric.ball (0 : ℂ) r := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, Metric.mem_ball, dist_zero_right]
  exact (lintegral_add_compl _ (isClosed_le continuous_const continuous_norm).measurableSet).symm.trans (by rw [hc])

/-- The retained zero mass of a supplied GMC is almost surely strictly positive and finite. -/
theorem reflected_retainedZero_ae_positive_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ r : ℝ) (hr : r ≤ 1)
    (hα₁ : α₁ - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, 0 < reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω) ∧
      coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ < ⊤ := by
  filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ₂ M hM 3 (1 / 8) (by norm_num),
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1,
    reflected_rho_ae_finite P X hX γ hγ hγ₂ M hM (α₁ - γ / 2) α₂ α₃ hα₁ hα₂ hα₃]
      with ω hb h0 h1 hf
  have hlow := reflected_retainedZero_fixed_disk_lower γ α₁ α₂ α₃ r (M ω) hr
  have hw : 0 < ENNReal.ofReal ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-γ / 2, α₁, α₂] : Fin 3 → ℝ) i|) *
      (4 : ℝ) ^ (-|γ * α₃|)) := ENNReal.ofReal_pos.mpr (by positivity)
  refine ⟨(ENNReal.mul_pos hw.ne' hb.ne').trans_le hlow, ?_⟩
  rw [← gammaHalfMass_eq_coulombMass γ α₁ α₂ α₃ 0 (M ω) h0 h0 h1,
    reflected_zero_kernel_integral_eq_rho γ α₁ α₂ α₃ (M ω) h0 h1]
  exact hf

end DOZZ.Proofs
