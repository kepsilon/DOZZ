/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.IndependentRegroup
/-! Independent copies on distinct source spaces preserve the exterior past mark. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- Independent source copies push forward to the product of their actual marginal laws. -/
theorem dual_independent_copy_map_law
    {Ω Λ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure Λ) (P : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (F : Λ → α) (G : Ω → β)
    (hF : AEMeasurable F Q) (hG : AEMeasurable G P) :
    (Q.prod P).map (fun ω : Λ × Ω => (F ω.1, G ω.2)) = (Q.map F).prod (P.map G) := by
  have hf : ∀ᵐ ω : Λ × Ω ∂Q.prod P, F ω.1 = hF.mk F ω.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hF.ae_eq_mk
  have hg : ∀ᵐ ω : Λ × Ω ∂Q.prod P, G ω.2 = hG.mk G ω.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae hG.ae_eq_mk
  have he : (fun ω : Λ × Ω => (F ω.1, G ω.2)) =ᵐ[Q.prod P]
      Prod.map (hF.mk F) (hG.mk G) := by
    filter_upwards [hf, hg] with ω hω hω'
    exact Prod.ext hω hω'
  rw [Measure.map_congr he, ← Measure.map_prod_map Q P hF.measurable_mk hG.measurable_mk,
    ← Measure.map_congr hF.ae_eq_mk, ← Measure.map_congr hG.ae_eq_mk]



end DOZZ.Proofs
