/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Attach an independent pin multiplier to equal mass laws. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem independent_product_law
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (R : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (f : Ω → ℝ≥0∞) (g : Ξ → ℝ≥0∞) (S : Ω → ℝ≥0∞)
    (hf : AEMeasurable f P) (hg : AEMeasurable g R) (hS : AEMeasurable S P)
    (hl : P.map f = R.map g) :
    (P.prod P).map (fun q => S q.2*f q.1) =
      (R.prod P).map (fun q => S q.2*g q.1) := by
  have hfl : HasLaw f (P.map f) P := ⟨hf,rfl⟩
  have hgl : HasLaw g (P.map f) R := ⟨hg,hl.symm⟩
  have hSl : HasLaw S (P.map S) P := ⟨hS,rfl⟩
  have h₁ := hfl.comp (measurePreserving_fst (μ := P) (ν := P)).hasLaw
  have h₂ := hgl.comp (measurePreserving_fst (μ := R) (ν := P)).hasLaw
  have h₃ := hSl.comp (measurePreserving_snd (μ := P) (ν := P)).hasLaw
  have h₄ := hSl.comp (measurePreserving_snd (μ := R) (ν := P)).hasLaw
  have hid₁ : IdentDistrib (f ∘ Prod.fst) (g ∘ Prod.fst) (P.prod P) (R.prod P) :=
    ⟨h₁.aemeasurable,h₂.aemeasurable,h₁.map_eq.trans h₂.map_eq.symm⟩
  have hid₂ : IdentDistrib (S ∘ Prod.snd) (S ∘ Prod.snd) (P.prod P) (R.prod P) :=
    ⟨h₃.aemeasurable,h₄.aemeasurable,h₃.map_eq.trans h₄.map_eq.symm⟩
  have hid := hid₁.prodMk hid₂ (indepFun_prod₀ hf hS) (indepFun_prod₀ hg hS)
  have hm : Measurable (fun q : ℝ≥0∞ × ℝ≥0∞ => q.2*q.1) := measurable_snd.mul measurable_fst
  exact (hid.comp hm).map_eq


end DOZZ.Proofs
