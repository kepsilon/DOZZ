/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.IndependentInnerTransport
/-! Align the inner/outer independent-copy ordering with the source full-path carrier. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The independent radial-law/inner/outer model equals the source radial/outer/inner
model. Tonelli and product symmetry apply before converting either expectation to real. -/
theorem dual_radial_copy_lintegral_regroup
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → α) (hA : AEMeasurable A P)
    (F : α × (Ω × Ω) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂(P.map A).prod (P.prod P)) =
      ∫⁻ v : (Ω × Ω) × Ω, F (A v.1.1,(v.2,v.1.2)) ∂(P.prod P).prod P := by
  let G : Ω × (Ω × Ω) → ℝ≥0∞ := fun v => F (A v.1,(v.2.2,v.2.1))
  have hG : AEMeasurable G (P.prod (P.prod P)) := hF.comp_aemeasurable
    (hA.comp_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk
      (measurable_fst.comp measurable_snd)).aemeasurable)
  have he := (measurePreserving_prodAssoc P P P).lintegral_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding G
  change (∫⁻ v : (Ω × Ω) × Ω, F (A v.1.1,(v.2,v.1.2)) ∂(P.prod P).prod P) =
    ∫⁻ v, G v ∂P.prod (P.prod P) at he
  rw [he, lintegral_prod _ hG, lintegral_prod _ hF.aemeasurable]
  have hk : Measurable (fun a : α => ∫⁻ v : Ω × Ω, F (a,v) ∂P.prod P) :=
    hF.lintegral_prod_right'
  rw [lintegral_map' hk.aemeasurable hA]
  apply lintegral_congr
  intro ω
  exact (lintegral_prod_swap (μ := P) (ν := P) (fun v : Ω × Ω => F (A ω,v))).symm

end DOZZ.Proofs
