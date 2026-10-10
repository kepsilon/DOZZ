/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.GMCFiniteCoordinateTilt

/-! Factoring root-dependent observables through determining real coordinates. -/

@[expose] public section

open MeasureTheory MeasurableSpace
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- A measurable root/field/finite-measure observable has a measurable representative on the
root and real determining-coordinate path. -/
theorem rooted_observable_factors_through_coordinates
    (H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) => H q.1 q.2.1 q.2.2)) :
    ∃ K : ℂ × (gmcTiltCoordinateIndex → ℝ) → ℝ≥0∞, Measurable K ∧
      ∀ (u : ℂ) (q : TestFn → ℝ) (μ : Measure ℂ), IsFiniteMeasure μ →
        H u q μ = K (u, gmcTiltCoordinatePath q μ) := by
  let Q := TestFn → ℝ
  let E := Option (ℚ × ℚ) → ℝ≥0∞
  let lift : ℂ × (Q × FiniteMeasure ℂ) → ℂ × (Q × E) :=
    Prod.map id gmcJointFiniteEval
  have hJoint : MeasurableSpace.comap gmcJointFiniteEval
      (inferInstance : MeasurableSpace (Q × E)) =
      (inferInstance : MeasurableSpace (Q × FiniteMeasure ℂ)) := by
    change MeasurableSpace.comap (fun p : Q × FiniteMeasure ℂ =>
      (p.1, gmcFiniteMeasureEval p.2))
      ((inferInstance : MeasurableSpace Q).prod (inferInstance : MeasurableSpace E)) =
      (inferInstance : MeasurableSpace Q).prod (inferInstance : MeasurableSpace (FiniteMeasure ℂ))
    rw [MeasurableSpace.comap_prodMk, MeasurableSpace.prod]
    rw [show (inferInstance : MeasurableSpace (FiniteMeasure ℂ)) =
      MeasurableSpace.comap gmcFiniteMeasureEval (inferInstance : MeasurableSpace E) from
        gmcFiniteMeasure_sigma_eq]
    rw [MeasurableSpace.comap_comp]
    rfl
  have hSigma : MeasurableSpace.comap lift
      (inferInstance : MeasurableSpace (ℂ × (Q × E))) =
      (inferInstance : MeasurableSpace (ℂ × (Q × FiniteMeasure ℂ))) := by
    change MeasurableSpace.comap (Prod.map id gmcJointFiniteEval)
      ((inferInstance : MeasurableSpace ℂ).prod inferInstance) = _
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id, hJoint]
    rfl
  have hPull : Measurable (fun p : ℂ × (Q × FiniteMeasure ℂ) =>
      H p.1 p.2.1 (p.2.2 : Measure ℂ)) := by
    exact hH.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd |>.prodMk
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))
  have hPull' : @Measurable (ℂ × (Q × FiniteMeasure ℂ)) ℝ≥0∞
      (MeasurableSpace.comap lift inferInstance) inferInstance
      (fun p => H p.1 p.2.1 (p.2.2 : Measure ℂ)) := by
    rw [hSigma]
    exact hPull
  obtain ⟨G, hG, hGfactor⟩ := hPull'.exists_eq_measurable_comp
  let decode : (gmcTiltCoordinateIndex → ℝ) → Q × E := fun v =>
    (fun f => v (.inl f), fun j => ENNReal.ofReal (v (.inr j)))
  have hd : Measurable decode := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr fun f => measurable_pi_apply (Sum.inl f)
    · exact measurable_pi_iff.mpr fun j => ENNReal.measurable_ofReal.comp
        (measurable_pi_apply (Sum.inr j))
  refine ⟨fun p => G (p.1, decode p.2),
    hG.comp (measurable_fst.prodMk (hd.comp measurable_snd)), ?_⟩
  intro u q μ hμ
  have heq : decode (gmcTiltCoordinatePath q μ) =
      gmcJointFiniteEval (q, ⟨μ, hμ⟩) := by
    apply Prod.ext
    · rfl
    · funext j
      change ENNReal.ofReal (μ (gmcTiltCoordinateSet j)).toReal =
        gmcFiniteMeasureEval ⟨μ, hμ⟩ j
      rw [ENNReal.ofReal_toReal (@measure_ne_top ℂ _ μ hμ _)]
      cases j <;> rfl
  have hf := congrFun hGfactor (u, (q, ⟨μ, hμ⟩))
  change H u q μ = G (u, gmcJointFiniteEval (q, ⟨μ, hμ⟩)) at hf
  change H u q μ = G (u, decode (gmcTiltCoordinatePath q μ))
  rw [heq]
  exact hf

end DOZZ.Proofs
