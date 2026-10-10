/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCircleIntegrated
public import DOZZ.GMC.Construction.RootedCircleObservableLimit
public import DOZZ.GMC.Construction.RootedMarkedL1Limit

/-! The rooted identity for bounded continuous marks of finitely many determining coordinates. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- On a bounded root set where point insertion is finite almost surely, rooting agrees with
singular insertion for every nonnegative bounded continuous finite-coordinate mark. -/
theorem rooted_finite_coordinate_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMmeas : Measurable M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall (0 : ℂ) R)
    (hRoot : ∀ᵐ u ∂gmcReferenceMeasure.restrict A,
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)))
    (s : Finset gmcTiltCoordinateIndex)
    (φ : BoundedContinuousFunction (∀ _i : {i // i ∈ s}, ℝ) ℝ)
    (hφpos : ∀ q, 0 ≤ φ q) :
    (∫⁻ ω, ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω))) *
      M ω A ∂P) =
    ∫⁻ u in A, ∫⁻ ω, ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + γ * gffRootCovariance u f)
      (gmcRootedMeasure γ u (M ω)))) ∂P ∂gmcReferenceMeasure := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let mark : Ω → ℝ := fun ω => φ (gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω))
  have hmark : Measurable mark := by
    have hx : Measurable (fun ω f => X ω f) := measurable_pi_iff.mpr fun f => (hX.2 f).1
    exact φ.continuous.measurable.comp
      ((measurable_gmcTiltFiniteCoordinatePath s).comp (hx.prodMk hMmeas))
  let H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun u q μ =>
    A.indicator (fun _ => ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s q μ))) u
  have hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) => H q.1 q.2.1 q.2.2) := by
    exact (ENNReal.measurable_ofReal.comp (φ.continuous.measurable.comp
      ((measurable_gmcTiltFiniteCoordinatePath s).comp measurable_snd))).indicator
        (hA.preimage measurable_fst)
  have heq (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (mark ω) * regularizedGMC P Xc γ (n : ℝ) ω A ∂P) =
      ∫⁻ u in A, ∫⁻ ω, ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + γ * circleCross u (n : ℝ) f)
        ((M ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))))))) ∂P
        ∂gmcReferenceMeasure := by
    have ht := regularizedGMC_integrated_rooted_limiting_mark_identity
      P X hX γ hγ hγ2 M hM hMmeas Xc hXc (n : ℝ) H hH
    have hl : (∫⁻ ω, ∫⁻ u, H u (fun f => X ω f) (M ω)
        ∂regularizedGMC P Xc γ (n : ℝ) ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal (mark ω) * regularizedGMC P Xc γ (n : ℝ) ω A ∂P := by
      apply lintegral_congr
      intro ω
      exact lintegral_indicator_const hA _
    have hr : (∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * circleCross u (n : ℝ) f)
        ((M ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))))) ∂P
        ∂gmcReferenceMeasure) =
        ∫⁻ u in A, ∫⁻ ω, ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
          (fun f => X ω f + γ * circleCross u (n : ℝ) f)
          ((M ω).withDensity (fun x => ENNReal.ofReal
            (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))))))) ∂P
          ∂gmcReferenceMeasure := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ A
      · simp only [H, Set.indicator_of_mem hu]
      · simp only [H, Set.indicator_of_notMem hu, lintegral_zero]
    exact hl.symm.trans (ht.trans hr)
  have hl := regularizedGMC_bounded_mass_mark_lintegral_tendsto
    P X hX γ hγ hγ2 M hM Xc hXc A hA R hAR mark hmark.aestronglyMeasurable
    (fun ω => hφpos _) ‖φ‖ (norm_nonneg _)
    (fun ω => φ.norm_coe_le_norm _)
  have hr := circleRooted_bounded_coordinate_lintegral_tendsto
    P X hX γ hγ hγ2 M hM hMmeas (gmcReferenceMeasure.restrict A) hRoot s φ
  exact tendsto_nhds_unique hl (by simpa only [heq] using hr)

end DOZZ.Proofs
