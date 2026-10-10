/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.UniformWeightLimit
public import DOZZ.GMC.AdmissibleGMCRestriction
public import DOZZ.Statements.GMC.FieldChaosMass
import Mathlib.Tactic
/-! Actual compact admissible chaos tests in the field-mass limit Kahane interface. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
open DOZZ.Assembly

/-- The actual compact admissible chaos convergence supplies exactly the finite-field mass
convergence required by the limiting negative-power Kahane comparison
`DOZZ.kahane_limit_field_negative_power`. -/
theorem reflected_admissible_field_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ)
    (N : Ω → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : BoundedContinuousFunction ℂ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hfK : tsupport (f : ℂ → ℝ) ⊆ K) (R₀ : ℝ) (hR₀ : Real.exp (-R₀) ≤ ε₀) :
    IsFiniteMeasure ((logRegularizationReference U dens).restrict K) ∧
    TendstoInMeasure P
      (fun r ω => (fieldChaosMass P
        (fun ω x => Y ω (Real.exp (-max r R₀)) x)
        ((logRegularizationReference U dens).restrict K)
        (fun x => (f x).toNNReal) γ ω).toReal) atTop
      (fun ω => ∫ x, f x ∂N ω) := by
  have hσ := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  have hfin : IsFiniteMeasure ((logRegularizationReference U dens).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hσ⟩
  refine ⟨hfin, ?_⟩
  have hf0 : ∀ x ∉ K, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hfK h))
  have hr (r : ℝ) : Real.exp (-max r R₀) ≤ ε₀ :=
    (Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))).trans hR₀
  have hi (r : ℝ) := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU
    γ (max r R₀) (hr r) ‖f‖ f f.continuous.measurable
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) hf0
  have he (r : ℝ) : (fun ω => regularizedLogChaosTestMass P U dens Y γ (max r R₀) ω f) =ᵐ[P]
      (fun ω => (fieldChaosMass P (fun ω x => Y ω (Real.exp (-max r R₀)) x)
        ((logRegularizationReference U dens).restrict K)
        (fun x => (f x).toNNReal) γ ω).toReal) := by
    filter_upwards [hi r] with ω hω
    have hnon : ∀ᵐ x ∂(logRegularizationReference U dens).restrict K,
        0 ≤ f x * Real.exp (γ * Y ω (Real.exp (-max r R₀)) x - γ ^ 2 / 2 *
          ∫ ω', Y ω' (Real.exp (-max r R₀)) x ^ 2 ∂P) :=
      ae_of_all _ fun x => mul_nonneg (hf x) (Real.exp_pos _).le
    have hm := ofReal_integral_eq_lintegral_ofReal hω.integrableOn hnon
    have hid : fieldChaosMass P (fun ω x => Y ω (Real.exp (-max r R₀)) x)
        ((logRegularizationReference U dens).restrict K) (fun x => (f x).toNNReal) γ ω =
      ∫⁻ x, ENNReal.ofReal (f x * Real.exp (γ * Y ω (Real.exp (-max r R₀)) x - γ ^ 2 / 2 *
        ∫ ω', Y ω' (Real.exp (-max r R₀)) x ^ 2 ∂P))
          ∂(logRegularizationReference U dens).restrict K := by
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (hf x)).symm
    rw [hid, ← hm, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnon)]
    exact (integral_restrict_eq_integral_of_zero_on_compl _ K hK.measurableSet _
      (fun x hx => by rw [hf0 x hx, zero_mul])).symm
  have ht : Tendsto (fun r : ℝ => max r R₀) atTop atTop :=
    tendsto_atTop_mono (fun r => le_max_left r R₀) tendsto_id
  exact TendstoInMeasure.congr he (Filter.EventuallyEq.refl _ _)
    ((hN.2.2.2 f (hK.of_isClosed_subset (isClosed_tsupport _) hfK) (hfK.trans hKU)).comp ht)

end DOZZ.Proofs
