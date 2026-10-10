/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
public import DOZZ.Statements.GMC.IsCenteredGaussianField
public import DOZZ.Statements.GMC.GaussianCovariance
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! # Independent copies of a Gaussian field glued along a set

The comparison field for the two-branch small-deviation step uses two independent copies of a
Gaussian field, one on a measurable set `A` and one on its complement, together with an
independent common Gaussian scalar. Its covariance is the original covariance inside each piece,
zero across the pieces, plus the variance of the scalar; its Wick mass factors as the scalar
exponential times the sum of the two independent piece masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Coordinatewise rescaling preserves centered joint Gaussianity. -/
theorem isCenteredJointlyGaussian_coord_mul {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z) (b : ι → ℝ) :
    IsCenteredJointlyGaussian P (fun ω i => b i * Z ω i) := by
  refine ⟨hZ.1, fun i => (hZ.2.1 i).const_mul (b i), fun a => ?_⟩
  have heq : (fun ω => ∑ i, a i * (b i * Z ω i)) = fun ω => ∑ i, (a i * b i) * Z ω i := by
    funext ω
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq]
  exact hZ.2.2 (fun i => a i * b i)


/-- Independent centered jointly Gaussian families on two factors add to a centered jointly
Gaussian family on the product. -/
theorem isCenteredJointlyGaussian_prod_add {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [Fintype ι] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Z₁ : Ω₁ → ι → ℝ) (Z₂ : Ω₂ → ι → ℝ)
    (h₁ : IsCenteredJointlyGaussian P₁ Z₁) (h₂ : IsCenteredJointlyGaussian P₂ Z₂) :
    IsCenteredJointlyGaussian (P₁.prod P₂) (fun q i => Z₁ q.1 i + Z₂ q.2 i) := by
  have := h₁.1
  have := h₂.1
  refine ⟨inferInstance, fun i => ?_, fun a => ?_⟩
  · exact ((h₁.2.1 i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).add
      ((h₂.2.1 i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  · obtain ⟨hm₁, v₁, hv₁⟩ := h₁.2.2 a
    obtain ⟨hm₂, v₂, hv₂⟩ := h₂.2.2 a
    let U : Ω₁ → ℝ := fun ω => ∑ i, a i * Z₁ ω i
    let V : Ω₂ → ℝ := fun ω => ∑ i, a i * Z₂ ω i
    have heq : (fun q : Ω₁ × Ω₂ => ∑ i, a i * (Z₁ q.1 i + Z₂ q.2 i)) =
        fun q => U q.1 + V q.2 := by
      funext q
      simp only [U, V, mul_add, Finset.sum_add_distrib]
    rw [heq]
    refine ⟨(hm₁.comp_fst P₂).add (hm₂.comp_snd P₁), ⟨v₁ + v₂, ?_⟩⟩
    have hind : IndepFun (fun q : Ω₁ × Ω₂ => U q.1) (fun q => V q.2) (P₁.prod P₂) :=
      indepFun_prod₀ hm₁.aemeasurable hm₂.aemeasurable
    have hU : HasLaw (fun q : Ω₁ × Ω₂ => U q.1) (gaussianReal 0 v₁) (P₁.prod P₂) :=
      (⟨hm₁.aemeasurable, hv₁⟩ : HasLaw U (gaussianReal 0 v₁) P₁).comp
        (measurePreserving_fst (μ := P₁) (ν := P₂)).hasLaw
    have hV : HasLaw (fun q : Ω₁ × Ω₂ => V q.2) (gaussianReal 0 v₂) (P₁.prod P₂) :=
      (⟨hm₂.aemeasurable, hv₂⟩ : HasLaw V (gaussianReal 0 v₂) P₂).comp
        (measurePreserving_snd (μ := P₁) (ν := P₂)).hasLaw
    have h := gaussianReal_add_gaussianReal_of_indepFun hind hU hV
    rw [zero_add] at h
    exact h

/-- The mixed second moment of independent sums of square-integrable variables on a product is
the sum of the factor mixed second moments, as soon as the first-factor variables are centered. -/
theorem gaussianCovariance_prod_add {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (U₁ V₁ : Ω₁ → ℝ) (U₂ V₂ : Ω₂ → ℝ)
    (hU₁ : MemLp U₁ 2 P₁) (hV₁ : MemLp V₁ 2 P₁) (hU₂ : MemLp U₂ 2 P₂) (hV₂ : MemLp V₂ 2 P₂)
    (hU₁0 : ∫ ω, U₁ ω ∂P₁ = 0) (hV₁0 : ∫ ω, V₁ ω ∂P₁ = 0) :
    gaussianCovariance (P₁.prod P₂) (fun q => U₁ q.1 + U₂ q.2) (fun q => V₁ q.1 + V₂ q.2) =
      gaussianCovariance P₁ U₁ V₁ + gaussianCovariance P₂ U₂ V₂ := by
  unfold gaussianCovariance
  have i11 : Integrable (fun q : Ω₁ × Ω₂ => U₁ q.1 * V₁ q.1) (P₁.prod P₂) :=
    ((hU₁.integrable_mul hV₁).comp_fst P₂)
  have i22 : Integrable (fun q : Ω₁ × Ω₂ => U₂ q.2 * V₂ q.2) (P₁.prod P₂) :=
    ((hU₂.integrable_mul hV₂).comp_snd P₁)
  have i12 : Integrable (fun q : Ω₁ × Ω₂ => U₁ q.1 * V₂ q.2) (P₁.prod P₂) :=
    (hU₁.integrable one_le_two).mul_prod (hV₂.integrable one_le_two)
  have i21 : Integrable (fun q : Ω₁ × Ω₂ => U₂ q.2 * V₁ q.1) (P₁.prod P₂) := by
    have h := (hV₁.integrable one_le_two).mul_prod (hU₂.integrable one_le_two)
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    exact mul_comm _ _
  have hexpand : (fun q : Ω₁ × Ω₂ => (U₁ q.1 + U₂ q.2) * (V₁ q.1 + V₂ q.2)) =
      fun q => (U₁ q.1 * V₁ q.1 + U₂ q.2 * V₂ q.2) + (U₁ q.1 * V₂ q.2 + U₂ q.2 * V₁ q.1) := by
    funext q
    ring
  rw [hexpand,
    integral_add (f := fun q : Ω₁ × Ω₂ => U₁ q.1 * V₁ q.1 + U₂ q.2 * V₂ q.2)
      (g := fun q : Ω₁ × Ω₂ => U₁ q.1 * V₂ q.2 + U₂ q.2 * V₁ q.1) (i11.add i22) (i12.add i21),
    integral_add (f := fun q : Ω₁ × Ω₂ => U₁ q.1 * V₁ q.1)
      (g := fun q : Ω₁ × Ω₂ => U₂ q.2 * V₂ q.2) i11 i22,
    integral_add (f := fun q : Ω₁ × Ω₂ => U₁ q.1 * V₂ q.2)
      (g := fun q : Ω₁ × Ω₂ => U₂ q.2 * V₁ q.1) i12 i21,
    integral_fun_fst (fun ω => U₁ ω * V₁ ω),
    integral_fun_snd (fun ω => U₂ ω * V₂ ω), integral_prod_mul U₁ V₂]
  have h21 : (∫ q : Ω₁ × Ω₂, U₂ q.2 * V₁ q.1 ∂P₁.prod P₂) = 0 := by
    have h := integral_prod_mul (μ := P₁) (ν := P₂) V₁ U₂
    rw [hV₁0, zero_mul] at h
    rw [← h]
    congr 1
    funext q
    exact mul_comm _ _
  rw [h21, hU₁0, zero_mul]
  simp

end DOZZ.Proofs
