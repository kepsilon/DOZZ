/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCoordinateLaw
public import DOZZ.GMC.Construction.RootedMarkedMeasure

/-! The law of the root together with all determining field and chaos coordinates. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Including the root in the full coordinate law permits arbitrary measurable root-dependent
observables on every bounded root set with almost surely finite insertion. -/
theorem rooted_joint_coordinate_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMmeas : Measurable M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (B : Set ℂ) (hB : MeasurableSet B) (R : ℝ)
    (hBR : B ⊆ Metric.closedBall (0 : ℂ) R)
    (hRoot : ∀ᵐ u ∂gmcReferenceMeasure.restrict B,
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω))) :
    P.bind (fun ω => Measure.map
      (fun u => (u, gmcTiltCoordinatePath (fun f => X ω f) (M ω))) ((M ω).restrict B)) =
    Measure.map (fun q : ℂ × Ω => (q.1, gmcTiltCoordinatePath
      (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2)))) ((gmcReferenceMeasure.restrict B).prod P) := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let leftPath : Ω → gmcTiltCoordinateIndex → ℝ := fun ω =>
    gmcTiltCoordinatePath (fun f => X ω f) (M ω)
  let rightPath : ℂ × Ω → gmcTiltCoordinateIndex → ℝ := fun q =>
    gmcTiltCoordinatePath (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))
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
  have hmean : (∫⁻ ω, (M ω).restrict B Set.univ ∂P) < ⊤ := by
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM B hB]
    exact measure_lt_top _ _
  let _ := isFiniteMeasure_bind_markedMeasure P _ hres hfin leftPath hl hmean
  apply Measure.ext_prod
  intro A D hA hD
  rw [bind_markedMeasure_apply_prod P _ hres hfin leftPath hl A hA D hD]
  have hden : (fun ω => (M ω).restrict B A) = fun ω => M ω (A ∩ B) := by
    funext ω
    exact Measure.restrict_apply hA
  rw [hden]
  have hRootAB : ∀ᵐ u ∂gmcReferenceMeasure.restrict (A ∩ B),
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)) :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hRoot
  have hLaw := rooted_full_coordinate_law P X hX γ hγ hγ2 M hM hMmeas
    Xc hXc (A ∩ B) (hA.inter hB) R (Set.inter_subset_right.trans hBR) hRootAB
  have heval := congrArg (fun μ : Measure (gmcTiltCoordinateIndex → ℝ) => μ D) hLaw
  change Measure.map leftPath (P.withDensity (fun ω => M ω (A ∩ B))) D =
    Measure.map (fun q : ℂ × Ω => (q.1, rightPath q))
      ((gmcReferenceMeasure.restrict B).prod P) (A ×ˢ D)
  rw [heval]
  rw [Measure.map_apply hr hD,
    Measure.map_apply (measurable_fst.prodMk hr) (hA.prod hD)]
  rw [← Measure.restrict_restrict hA, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (hr hD)]
  congr 1
  ext q
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  exact and_comm

end DOZZ.Proofs
