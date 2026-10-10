/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Comap

/-!
# Uniqueness of lifetime-marked measures above a deterministic cutoff

Open-closed lifetime intervals strictly beyond the final observation determine the measure
on that domain. Pullback to the open interval avoids adding any boundary-atom assumption.
-/

@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs

/-- Intervals with both endpoints above a cutoff determine finite measures supported above it. -/
theorem measure_eq_of_Ioc_above (μ η : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (s : ℝ) (hμ : ∀ᵐ t ∂μ, s < t) (hη : ∀ᵐ t ∂η, s < t)
    (h : ∀ a b : ℝ, s < a → a < b → μ (Ioc a b) = η (Ioc a b)) : μ = η := by
  let e : Ioi s → ℝ := Subtype.val
  have he : MeasurableEmbedding e := MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hsub : μ.comap e = η.comap e := by
    apply Measure.ext_of_Ioc' _ _ (fun _ _ _ => measure_ne_top _ _)
    intro a b hab
    rw [Measure.comap_apply e he.injective (fun _ => he.measurableSet_image.mpr) _ measurableSet_Ioc,
      Measure.comap_apply e he.injective (fun _ => he.measurableSet_image.mpr) _ measurableSet_Ioc]
    have himage : e '' Ioc a b = Ioc (a : ℝ) (b : ℝ) := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ht
        exact ⟨⟨t, a.property.trans ht.1⟩, ht, rfl⟩
    rw [himage]
    exact h a b a.property hab
  have hrμ : μ.restrict (Ioi s) = μ := Measure.restrict_eq_self_of_ae_mem hμ
  have hrη : η.restrict (Ioi s) = η := Measure.restrict_eq_self_of_ae_mem hη
  ext A hA
  have hpre : MeasurableSet (e ⁻¹' A) := hA.preimage he.measurable
  have heq := congrArg (fun M : Measure (Ioi s) => M (e ⁻¹' A)) hsub
  rw [Measure.comap_apply e he.injective (fun _ => he.measurableSet_image.mpr) _ hpre,
    Measure.comap_apply e he.injective (fun _ => he.measurableSet_image.mpr) _ hpre,
    image_preimage_eq_inter_range] at heq
  have hrange : range e = Ioi s := Subtype.range_coe
  rw [hrange] at heq
  rw [← hrμ, ← hrη, Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact heq

/-- Past rectangles and lifetime intervals above the final observation determine a finite
marked measure supported beyond that observation. -/
theorem measure_eq_of_prod_Ioc_above {α : Type*} [MeasurableSpace α]
    (μ η : Measure (α × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (s : ℝ) (hμ : ∀ᵐ z ∂μ, s < z.2) (hη : ∀ᵐ z ∂η, s < z.2)
    (h : ∀ (A : Set α), MeasurableSet A → ∀ a b : ℝ, s < a → a < b →
      μ (A ×ˢ Ioc a b) = η (A ×ˢ Ioc a b)) : μ = η := by
  apply Measure.ext_prod
  intro A B hA hB
  let μA := (μ.restrict (A ×ˢ univ)).map Prod.snd
  let ηA := (η.restrict (A ×ˢ univ)).map Prod.snd
  have hsμ : ∀ᵐ t ∂μA, s < t := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt measurable_const measurable_id)).mpr
    exact ae_restrict_of_ae hμ
  have hsη : ∀ᵐ t ∂ηA, s < t := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt measurable_const measurable_id)).mpr
    exact ae_restrict_of_ae hη
  have hslice (C : Set ℝ) (hC : MeasurableSet C) (M : Measure (α × ℝ)) :
      ((M.restrict (A ×ˢ univ)).map Prod.snd) C = M (A ×ˢ C) := by
    rw [Measure.map_apply measurable_snd hC,
      Measure.restrict_apply (hC.preimage measurable_snd)]
    congr 1
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, and_comm]
  have heq : μA = ηA := by
    apply measure_eq_of_Ioc_above μA ηA s hsμ hsη
    intro a b ha hab
    rw [hslice _ measurableSet_Ioc, hslice _ measurableSet_Ioc]
    exact h A hA a b ha hab
  have hh := congrArg (fun M : Measure ℝ => M B) heq
  rw [hslice B hB, hslice B hB] at hh
  exact hh

end DOZZ.Proofs
end
