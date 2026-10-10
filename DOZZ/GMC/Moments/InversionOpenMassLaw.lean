/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionGlobalTestLaw
public import DOZZ.GMC.EquatorGFFChaosTransport
@[expose] public section
open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- Inversion preserves finite vectors of open-set masses of a measurable GMC. -/
theorem gmc_inversion_open_mass_fintype_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hmeas : Measurable M)
    (U : ι → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    P.map (fun ω j => (M ω).map (fun z : ℂ => z⁻¹) (U j)) =
      P.map (fun ω j => M ω (U j)) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hNmeas : Measurable N := (Measure.measurable_map _ measurable_inv).comp hmeas
  have hNfin : ∀ ω, IsFiniteMeasure (N ω) := by
    intro ω
    let := hM.1 ω
    infer_instance
  let q := fun n j => gmcOpenApprox (U (e j)) (hU (e j)) n
  let A := fun ω (j : Fin (Fintype.card ι)) => (N ω (U (e j))).toReal
  let B := fun ω (j : Fin (Fintype.card ι)) => (M ω (U (e j))).toReal
  have hA : Measurable A := measurable_pi_iff.mpr fun j =>
    ((Measure.measurable_coe (hU (e j)).measurableSet).comp hNmeas).ennreal_toReal
  have hB : Measurable B := measurable_pi_iff.mpr fun j =>
    ((Measure.measurable_coe (hU (e j)).measurableSet).comp hmeas).ennreal_toReal
  have hqn n j := finiteMeasure_bcf_integral_measurable N hNmeas hNfin (q n j)
  have hqm n j := finiteMeasure_bcf_integral_measurable M hmeas hM.1 (q n j)
  have hlaw : P.map A = P.map B := by
    apply gmc_limit_test_vector_law
      (fun n ω j => ∫ x, q n j x ∂N ω) (fun n ω j => ∫ x, q n j x ∂M ω) A B
    · intro n; exact (measurable_pi_iff.mpr (hqn n)).aemeasurable
    · intro n; exact (measurable_pi_iff.mpr (hqm n)).aemeasurable
    · exact hA.aemeasurable
    · exact hB.aemeasurable
    · intro n
      exact gmc_inversion_test_vector_law P X hX γ hγ hγ2 M hM hmeas (q n)
    · intro j
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hqn n j).aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun ω => by
        let := hNfin ω
        exact gmcOpenApprox_integral_tendsto (N ω) (U (e j)) (hU (e j))
    · intro j
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hqm n j).aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun ω => by
        let := hM.1 ω
        exact gmcOpenApprox_integral_tendsto (M ω) (U (e j)) (hU (e j))
  let post := fun v : Fin (Fintype.card ι) → ℝ =>
    fun j : ι => ENNReal.ofReal (v (e.symm j))
  have hp : Measurable post := by fun_prop
  have heA : post ∘ A = fun ω j => N ω (U j) := by
    funext ω j
    simp only [post, A, Function.comp_apply, Equiv.apply_symm_apply]
    let := hNfin ω
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  have heB : post ∘ B = fun ω j => M ω (U j) := by
    funext ω j
    simp only [post, B, Function.comp_apply, Equiv.apply_symm_apply]
    let := hM.1 ω
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  calc
    P.map (fun ω j => N ω (U j)) = (P.map A).map post := by
      rw [← heA, Measure.map_map hp hA]
    _ = (P.map B).map post := congrArg (Measure.map post) hlaw
    _ = P.map (fun ω j => M ω (U j)) := by rw [Measure.map_map hp hB, heB]
end DOZZ.Proofs
