/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedJointLaw
public import DOZZ.GMC.Construction.RootedObservableFactor

/-! The arbitrary measurable rooted identity on bounded root sets. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- The full measurable rooted identity on a bounded root set follows from almost sure
finiteness of point insertion there. The observable itself need not be bounded. -/
theorem rooted_GMC_identity_on_bounded_set
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMmeas : Measurable M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (B : Set ℂ) (hB : MeasurableSet B) (R : ℝ)
    (hBR : B ⊆ Metric.closedBall (0 : ℂ) R)
    (hRoot : ∀ᵐ u ∂gmcReferenceMeasure.restrict B,
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)))
    (H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) => H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ∫⁻ u in B, H u (fun f => X ω f) (M ω) ∂M ω ∂P) =
      ∫⁻ u in B, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f)
        (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  obtain ⟨K, hK, hfactor⟩ := rooted_observable_factors_through_coordinates H hH
  let leftPath : Ω → gmcTiltCoordinateIndex → ℝ := fun ω =>
    gmcTiltCoordinatePath (fun f => X ω f) (M ω)
  let rightPath : ℂ × Ω → gmcTiltCoordinateIndex → ℝ := fun q =>
    gmcTiltCoordinatePath (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))
  let family := fun ω => Measure.map (fun u => (u, leftPath ω)) ((M ω).restrict B)
  have hl : Measurable leftPath := measurable_gmcTiltCoordinatePath.comp
    ((measurable_pi_iff.mpr fun f => (hX.2 f).1).prodMk hMmeas)
  have hr : Measurable rightPath := measurable_pointRootedCoordinatePath P X hX γ M hMmeas hM.1
  have hres : Measurable (fun ω => (M ω).restrict B) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp_rw [Measure.restrict_apply hA]
    exact (Measure.measurable_coe (hA.inter hB)).comp hMmeas
  have hfin (ω : Ω) : IsFiniteMeasure ((M ω).restrict B) := by
    let _ := hM.1 ω
    infer_instance
  have hfamily : Measurable family := measurable_markedMeasure_family _ hres hfin leftPath hl
  have hjoint := rooted_joint_coordinate_law P X hX γ hγ hγ2 M hM hMmeas
    Xc hXc B hB R hBR hRoot
  calc
    _ = ∫⁻ ω, ∫⁻ u in B, K (u, leftPath ω) ∂M ω ∂P := by
      apply lintegral_congr
      intro ω
      apply lintegral_congr
      intro u
      exact hfactor u _ _ (hM.1 ω)
    _ = ∫⁻ p, K p ∂P.bind family := by
      rw [Measure.lintegral_bind hfamily.aemeasurable hK.aemeasurable]
      apply lintegral_congr
      intro ω
      exact (lintegral_map hK (show Measurable (fun u : ℂ => (u, leftPath ω)) from
        measurable_id.prodMk measurable_const)).symm
    _ = ∫⁻ p, K p ∂Measure.map (fun q : ℂ × Ω => (q.1, rightPath q))
        ((gmcReferenceMeasure.restrict B).prod P) := by rw [hjoint]
    _ = ∫⁻ u in B, ∫⁻ ω, K (u, rightPath (u, ω)) ∂P ∂gmcReferenceMeasure := by
      rw [lintegral_map hK (show Measurable (fun q : ℂ × Ω => (q.1, rightPath q)) from
        measurable_fst.prodMk hr)]
      exact lintegral_prod _ (hK.comp (measurable_fst.prodMk hr)).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hRoot] with u hu
      apply lintegral_congr_ae
      filter_upwards [hu] with ω hω
      exact (hfactor u _ _ hω).symm

end DOZZ.Proofs
