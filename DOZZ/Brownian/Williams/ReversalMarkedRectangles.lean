/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.ReversalMarkedDensity
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Rectangle integrals for the actual marked first-hit reversal law

Finiteness of the actual pushforward supplies integrability of its nonnegative density.
Fubini then gives the same past-cylinder and lifetime-interval formula as the last-exit law.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- A finite nonnegative product density has its iterated real rectangle integral. -/
theorem real_withDensity_prod_rectangle {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (η : Measure β) [SFinite μ] [SFinite η]
    (f : α × β → ℝ) (hf : Measurable f) (hn : ∀ z, 0 ≤ f z)
    [IsFiniteMeasure ((μ.prod η).withDensity (fun z => ENNReal.ofReal (f z)))]
    (A : Set α) (B : Set β) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((μ.prod η).withDensity (fun z => ENNReal.ofReal (f z))).real (A ×ˢ B) =
      ∫ x in A, ∫ y in B, f (x,y) ∂η ∂μ := by
  let M := (μ.prod η).withDensity (fun z => ENNReal.ofReal (f z))
  have hmass : (∫⁻ z, ENNReal.ofReal (f z) ∂μ.prod η) ≠ ⊤ := by
    have he : M univ = ∫⁻ z, ENNReal.ofReal (f z) ∂μ.prod η := by
      dsimp only [M]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← he]
    exact measure_ne_top _ _
  have hi : Integrable f (μ.prod η) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (ae_of_all _ hn)).mp hmass
  calc
    _ = ∫ z in A ×ˢ B, (1 : ℝ) ∂M := by simp [integral_const, M]
    _ = ∫ z in A ×ˢ B, f z ∂μ.prod η := by
      dsimp only [M]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        hf.ennreal_ofReal.aemeasurable.restrict
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ (hA.prod hB)]
      simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_one]
    _ = _ := by
      rw [← Measure.prod_restrict]
      exact integral_prod _ (by rw [Measure.prod_restrict]; exact hi.integrableOn)

/-- The actual first-hit reversal law on any finite past rectangle and lifetime interval
has the conditioned entrance FDD and the final last-exit boundary factor. -/
theorem brownianPath_firstHit_reversedIncreasing_rectangle
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0)
    (A : Set (Fin (n+1) → ℝ)) (hA : MeasurableSet A) (u v : ℝ) :
    ((P.restrict {p : BrownianPath | ss (Fin.last n) <
      firstPassageTime (driftedBrownianPath ν p) c}).map
        (brownianFirstHitReversedIncreasingObservation ν c n ss)).real (A ×ˢ Ioc u v) =
      ∫ x in A, ∫ t in Ioc u v,
        conditionedPositiveTransitionDensity ν (t-(ss (Fin.last n) : ℝ))
          (x (Fin.last n)) c * ν / conditionedH ν c
        ∂(volume : Measure ℝ)
        ∂(volume : Measure (Fin (n+1) → ℝ)).withDensity
          (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ))) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let μ : Measure (Fin (n+1) → ℝ) := volume.withDensity
    (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))
  have hlaw := brownianPath_firstHit_reversedIncreasing_density_map_unrestricted
    P hB ν c hν hc n ss hss hs0
  have : IsFiniteMeasure ((μ.prod volume).withDensity
      (fun z => ENNReal.ofReal (brownianReversalBoundaryDensity ν c n ss z))) := by
    rw [← hlaw]
    infer_instance
  rw [hlaw]
  exact real_withDensity_prod_rectangle μ volume (brownianReversalBoundaryDensity ν c n ss)
    (measurable_brownianReversalBoundaryDensity ν c n ss)
    (brownianReversalBoundaryDensity_nonneg ν c hν hc n ss) A (Ioc u v) hA measurableSet_Ioc

end DOZZ.Proofs
end
