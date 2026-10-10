/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.OuterPast
public import DOZZ.FourPoint.Reflected.ChartMassMeasurable
import Mathlib.Tactic
/-! Measurable exterior observables on the locally finite lateral carrier. -/
@[expose] public section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Lateral plane measures finite on compact subsets away from the origin. -/
abbrev DualLocalPlaneMeasure := {μ : Measure ℂ //
  ∀ K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → μ K < ⊤}

/-- The copied exterior mass evaluated from stopped radial data. -/
noncomputable def dualPastExteriorMass (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (r : ℝ)
    (p : (BrownianPath × BrownianPath) × DualLocalPlaneMeasure) : ℝ≥0∞ :=
  ∫⁻ x in ({0} : Set ℂ)ᶜ,
    (reflected_outerRegion r).indicator
      (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) *
        ENNReal.ofReal (dualPastReinsertionWeight γ p.1 x)) x ∂p.2.val

/-- Local finiteness suffices for the unbounded exterior mass to be measurable. -/
theorem dual_past_exterior_mass_measurable (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (r : ℝ) :
    Measurable (dualPastExteriorMass γ α₁ α₂ α₃ z r) := by
  unfold dualPastExteriorMass
  apply reflected_chart_parameter_mass_measurable
    ({0} : Set ℂ)ᶜ (isClosed_singleton.isOpen_compl) (fun μ : DualLocalPlaneMeasure => μ.val) measurable_subtype_coe
    (fun μ K hK hKU => μ.property K hK hKU)
    (fun p => (reflected_outerRegion r).indicator
      (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) *
        ENNReal.ofReal (dualPastReinsertionWeight γ p.1 x)) p.2)
  have hm : Measurable (fun p : (BrownianPath × BrownianPath) × ℂ =>
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z p.2) *
      ENNReal.ofReal (dualPastReinsertionWeight γ p.1 p.2)) :=
    ((dual_kernel_measurable γ α₁ α₂ α₃ z).comp measurable_snd).ennreal_ofReal.mul
      (dual_past_reinsertion_weight_measurable γ).ennreal_ofReal
  have hr : MeasurableSet (reflected_outerRegion r) := by
    unfold reflected_outerRegion
    exact (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (Set.Finite.measurableSet (by simp)).compl
  exact hm.indicator (hr.preimage measurable_snd)

/-- Lifting an independent variable to a subtype with the induced sigma algebra preserves
independence; no measurable-set assumption on the subtype predicate is needed. -/
theorem dual_indepFun_subtype_lift {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) (f : Ω → A) (g : Ω → B) (S : B → Prop)
    (hg : ∀ ω, S (g ω)) (hi : IndepFun f g P) :
    IndepFun f (fun ω => (⟨g ω, hg ω⟩ : Subtype S)) P := by
  rw [IndepFun_iff_Indep] at hi ⊢
  change Indep (MeasurableSpace.comap f _)
    (MeasurableSpace.comap (fun ω => (⟨g ω, hg ω⟩ : Subtype S))
      (MeasurableSpace.comap Subtype.val _)) P
  rw [MeasurableSpace.comap_comp]
  exact hi


/-- Beyond the restart radius, the measurable past observable is exactly the literal
copied exterior kernel integral. -/
theorem dual_past_exterior_mass_eq (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (A : TwoSidedPath) (T : ℝ≥0) (r : ℝ) (hr : Real.exp (-(T : ℝ)) ≤ r)
    (N : DualLocalPlaneMeasure) :
    dualPastExteriorMass γ α₁ α₂ α₃ z r
      ((stopBrownianPath (radialPositiveHalf A) T, radialNegativeHalf A), N) =
    ∫⁻ x in ({0} : Set ℂ)ᶜ, (reflected_outerRegion r).indicator
      (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) *
        ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) x ∂N.val := by
  unfold dualPastExteriorMass
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ reflected_outerRegion r
  · simp only [Set.indicator_of_mem hx]
    rw [dual_past_reinsertion_weight_eq γ A T x (hr.trans hx.1.le)]
  · simp only [Set.indicator_of_notMem hx]

/-- The dual restart likelihood evaluated solely at the terminal stopped-past value. -/
noncomputable def dualPastRestartWeight (γ ν : ℝ) (T : ℝ≥0) (z : ℂ)
    (p : BrownianPath × BrownianPath) : ℝ :=
  ‖z‖ ^ (2 : ℝ) * Real.exp (γ * (p.1 T - ν * T))

/-- Both the restart likelihood and exterior mass are measurable past observables. -/
theorem dual_past_restart_exterior_measurable (γ ν α₁ α₂ α₃ : ℝ)
    (T : ℝ≥0) (z : ℂ) (r : ℝ) :
    Measurable (fun p : (BrownianPath × BrownianPath) × DualLocalPlaneMeasure =>
      (dualPastRestartWeight γ ν T z p.1,
        dualPastExteriorMass γ α₁ α₂ α₃ z r p)) := by
  have hb : Measurable (fun p : (BrownianPath × BrownianPath) × DualLocalPlaneMeasure =>
      dualPastRestartWeight γ ν T z p.1) := by
    unfold dualPastRestartWeight
    exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      (((ContinuousMap.measurable_eval T).comp
        (measurable_fst.comp measurable_fst)).sub measurable_const)))
  exact hb.prodMk (dual_past_exterior_mass_measurable γ α₁ α₂ α₃ z r)

/-- The likelihood and exterior mass remain jointly independent of the future inward path. -/
theorem dual_radial_future_indep_restart_exterior
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → TwoSidedPath)
    (hA : AEMeasurable A P)
    (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (hhalves : IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P)
    (N : Ω → DualLocalPlaneMeasure) (hN : AEMeasurable N P)
    (hi : IndepFun A N P) (T : ℝ≥0) (γ ν α₁ α₂ α₃ : ℝ) (z : ℂ) (r : ℝ) :
    IndepFun (fun ω => brownianShiftPath T (radialPositiveHalf (A ω)))
      (fun ω => (dualPastRestartWeight γ ν T z
        (stopBrownianPath (radialPositiveHalf (A ω)) T, radialNegativeHalf (A ω)),
        dualPastExteriorMass γ α₁ α₂ α₃ z r
          ((stopBrownianPath (radialPositiveHalf (A ω)) T,
            radialNegativeHalf (A ω)), N ω))) P := by
  exact (reflected_radial_future_indep_full_past_lateral
    P A hA hB hhalves N hN hi T).comp measurable_id
      (dual_past_restart_exterior_measurable γ ν α₁ α₂ α₃ T z r)

end DOZZ.Proofs
