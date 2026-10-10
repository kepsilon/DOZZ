/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.HeterogeneousCopies
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-! Transport an independent inner input while retaining the entire exterior radial mark. -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Equality of the full exterior/path laws remains valid after adding an independent
inner carrier and applying any measurable signed observable. -/
theorem dual_joint_law_independent_inner_integral
    {Ω Λ Ξ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MeasurableSpace Ξ] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (Q : Measure Λ) (R : Measure Ξ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (F : Ω → α) (G : Λ → α) (Z : Ξ → β)
    (hF : AEMeasurable F P) (hG : AEMeasurable G Q) (hZ : AEMeasurable Z R)
    (hlaw : P.map F = Q.map G) (H : α × β → ℝ) (hH : Measurable H) :
    (∫ ω : Ω × Ξ, H (F ω.1,Z ω.2) ∂P.prod R) =
      ∫ ω : Λ × Ξ, H (G ω.1,Z ω.2) ∂Q.prod R := by
  have hf := hF.comp_fst.prodMk hZ.comp_snd
  have hg := hG.comp_fst.prodMk hZ.comp_snd
  rw [← integral_map hf hH.aestronglyMeasurable,
    ← integral_map hg hH.aestronglyMeasurable,
    dual_independent_copy_map_law P R F Z hF hZ,
    dual_independent_copy_map_law Q R G Z hG hZ, hlaw]

/-- Almost-sure properties also survive addition of an independent inner carrier.
This transports finiteness before any real-valued mass conversion. -/
theorem dual_joint_law_independent_inner_ae
    {Ω Λ Ξ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MeasurableSpace Ξ] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (Q : Measure Λ) (R : Measure Ξ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (F : Ω → α) (G : Λ → α) (Z : Ξ → β)
    (hF : AEMeasurable F P) (hG : AEMeasurable G Q) (hZ : AEMeasurable Z R)
    (hlaw : P.map F = Q.map G) (E : α × β → Prop) (hE : MeasurableSet {v | E v}) :
    (∀ᵐ ω : Ω × Ξ ∂P.prod R, E (F ω.1,Z ω.2)) ↔
      ∀ᵐ ω : Λ × Ξ ∂Q.prod R, E (G ω.1,Z ω.2) := by
  have hf := hF.comp_fst.prodMk hZ.comp_snd
  have hg := hG.comp_fst.prodMk hZ.comp_snd
  rw [← ae_map_iff hf hE, ← ae_map_iff hg hE,
    dual_independent_copy_map_law P R F Z hF hZ,
    dual_independent_copy_map_law Q R G Z hG hZ, hlaw]

end DOZZ.Proofs
