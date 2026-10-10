/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic

/-! Joint Gaussianity of independent finite families on their product probability space. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions NNReal

namespace DOZZ.Proofs

/-- Independent centered jointly Gaussian families form one centered jointly Gaussian family
when concatenated on the product probability space. -/
theorem independent_product_concat_isCenteredJointlyGaussian
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y) :
    IsCenteredJointlyGaussian (PX.prod PY)
      (fun ω (i : Sum ι ι) => match i with
        | Sum.inl j => X ω.1 j
        | Sum.inr j => Y ω.2 j) := by
  classical
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω i => match i with
    | Sum.inl j => X ω.1 j
    | Sum.inr j => Y ω.2 j
  have : IsProbabilityMeasure PX := hX.1
  have : IsProbabilityMeasure PY := hY.1
  let hfst : MeasurePreserving Prod.fst (PX.prod PY) PX := measurePreserving_fst
  let hsnd : MeasurePreserving Prod.snd (PX.prod PY) PY := measurePreserving_snd
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · intro i
    cases i with
    | inl j =>
        change AEMeasurable (fun ω : ΩX × ΩY => X ω.1 j) (PX.prod PY)
        have hm : AEMeasurable (fun ω : ΩX × ΩY => X ω.1 j) (PX.prod PY) := by
          have hm' : AEMeasurable (fun x : ΩX => X x j) ((PX.prod PY).map Prod.fst) := by
            rw [hfst.map_eq]
            exact hX.2.1 j
          exact hm'.comp_measurable measurable_fst
        exact hm
    | inr j =>
        change AEMeasurable (fun ω : ΩX × ΩY => Y ω.2 j) (PX.prod PY)
        have hm : AEMeasurable (fun ω : ΩX × ΩY => Y ω.2 j) (PX.prod PY) := by
          have hm' : AEMeasurable (fun y : ΩY => Y y j) ((PX.prod PY).map Prod.snd) := by
            rw [hsnd.map_eq]
            exact hY.2.1 j
          exact hm'.comp_measurable measurable_snd
        exact hm
  · intro a
    let cX : ι → ℝ := fun i => a (Sum.inl i)
    let cY : ι → ℝ := fun i => a (Sum.inr i)
    let fX : ΩX → ℝ := fun ω => ∑ i, cX i * X ω i
    let fY : ΩY → ℝ := fun ω => ∑ i, cY i * Y ω i
    obtain ⟨hXmem, ⟨vX, hXmap⟩⟩ := hX.2.2 cX
    obtain ⟨hYmem, ⟨vY, hYmap⟩⟩ := hY.2.2 cY
    have hXlaw : HasLaw fX (gaussianReal 0 vX) PX := ⟨hXmem.aemeasurable, hXmap⟩
    have hYlaw : HasLaw fY (gaussianReal 0 vY) PY := ⟨hYmem.aemeasurable, hYmap⟩
    have hXprod : HasLaw (fun ω : ΩX × ΩY => fX ω.1) (gaussianReal 0 vX) (PX.prod PY) :=
      hXlaw.comp hfst.hasLaw
    have hYprod : HasLaw (fun ω : ΩX × ΩY => fY ω.2) (gaussianReal 0 vY) (PX.prod PY) :=
      hYlaw.comp hsnd.hasLaw
    have hIndep : (fun ω : ΩX × ΩY => fX ω.1) ⟂ᵢ[PX.prod PY]
        (fun ω => fY ω.2) :=
      indepFun_prod₀ hXmem.aemeasurable hYmem.aemeasurable
    have hSumLaw : HasLaw (fun ω : ΩX × ΩY => fX ω.1 + fY ω.2)
        (gaussianReal 0 (vX + vY)) (PX.prod PY) := by
      refine ⟨?_, ?_⟩
      · exact (hXprod.aemeasurable.add hYprod.aemeasurable)
      · convert gaussianReal_add_gaussianReal_of_indepFun hIndep hXprod hYprod using 1; simp
    have hsum : (fun ω : ΩX × ΩY => ∑ i, a i * Z ω i) =
        fun ω => fX ω.1 + fY ω.2 := by
      funext ω
      simp [Z, cX, cY, fX, fY, Fintype.sum_sum_type]
    refine ⟨?_, ⟨vX + vY, ?_⟩⟩
    · rw [hsum]
      exact hSumLaw.memLp (ProbabilityTheory.memLp_id_gaussianReal (2 : ℝ≥0))
    · rw [hsum]
      exact hSumLaw.map_eq

end DOZZ.Proofs
