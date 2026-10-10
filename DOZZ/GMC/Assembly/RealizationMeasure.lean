/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.Realization
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import DOZZ.GMC.Assembly.CircleIntensity

/-! The Riesz measure of the almost sure limit functional on an open chart, its basic properties, and its measurability. -/

@[expose] public section

/-! ### The Riesz limit functional

The Riesz measure of the almost sure limit functional on an open chart.

On the good set, limits along the fast cutoff sequence define a positive linear functional on
continuous tests with compact support in the chart. Riesz–Markov–Kakutani on the chart, pushed
forward to the plane, gives a measure carried by the chart, finite on compact subsets of it, whose
test integrals are the limits. Off the good set the measure is zero. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal CompactlySupported

namespace DOZZ.Assembly

open DOZZ.Proofs

open Classical in
/-- Extension by zero of a compactly supported continuous test on a chart. -/
noncomputable def extendFromChart (U : Set ℂ) (g : C_c(U, ℝ)) : ℂ → ℝ :=
  fun x => if h : x ∈ U then g ⟨x, h⟩ else 0

section Extend

variable {U : Set ℂ}

theorem extendFromChart_val (g : C_c(U, ℝ)) (y : U) : extendFromChart U g y = g y := by
  simp [extendFromChart]

theorem extendFromChart_of_notMem (g : C_c(U, ℝ)) (x : ℂ) (hx : x ∉ U) :
    extendFromChart U g x = 0 := by
  simp only [extendFromChart, hx, dite_false]

theorem isCompact_image_tsupport (g : C_c(U, ℝ)) :
    IsCompact (Subtype.val '' tsupport (g : U → ℝ)) :=
  g.hasCompactSupport.image continuous_subtype_val

theorem support_extendFromChart_subset (g : C_c(U, ℝ)) :
    Function.support (extendFromChart U g) ⊆ Subtype.val '' tsupport (g : U → ℝ) := by
  intro x hx
  by_cases hxU : x ∈ U
  · refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
    rw [Function.mem_support] at hx ⊢
    simpa [extendFromChart, hxU] using hx
  · exact absurd (extendFromChart_of_notMem g x hxU) hx

theorem tsupport_extendFromChart_subset (g : C_c(U, ℝ)) :
    tsupport (extendFromChart U g) ⊆ Subtype.val '' tsupport (g : U → ℝ) :=
  closure_minimal (support_extendFromChart_subset g) (isCompact_image_tsupport g).isClosed

theorem hasCompactSupport_extendFromChart (g : C_c(U, ℝ)) :
    HasCompactSupport (extendFromChart U g) :=
  (isCompact_image_tsupport g).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_extendFromChart_subset g)

theorem tsupport_extendFromChart_subset_chart (g : C_c(U, ℝ)) :
    tsupport (extendFromChart U g) ⊆ U :=
  (tsupport_extendFromChart_subset g).trans (Subtype.coe_image_subset _ _)

theorem continuous_extendFromChart (hU : IsOpen U) (g : C_c(U, ℝ)) :
    Continuous (extendFromChart U g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · have hcomp : extendFromChart U g ∘ Subtype.val = g := funext fun y => extendFromChart_val g y
    have h : ContinuousAt (extendFromChart U g ∘ Subtype.val) ⟨x, hx⟩ := by
      rw [hcomp]; exact g.continuous.continuousAt
    exact hU.isOpenEmbedding_subtypeVal.continuousAt_iff.mp h
  · have hxT : x ∉ Subtype.val '' tsupport (g : U → ℝ) := fun h =>
      hx (Subtype.coe_image_subset _ _ h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [(isCompact_image_tsupport g).isClosed.isOpen_compl.mem_nhds hxT] with y hy
    exact (Function.notMem_support.mp (fun h => hy (support_extendFromChart_subset g h))).symm

theorem extendFromChart_add (g₁ g₂ : C_c(U, ℝ)) :
    extendFromChart U (g₁ + g₂) = fun x => extendFromChart U g₁ x + extendFromChart U g₂ x := by
  funext x
  by_cases hx : x ∈ U
  · simp [extendFromChart, hx]
  · simp [extendFromChart, hx]

theorem extendFromChart_smul (c : ℝ) (g : C_c(U, ℝ)) :
    extendFromChart U (c • g) = fun x => c * extendFromChart U g x := by
  funext x
  by_cases hx : x ∈ U
  · simp [extendFromChart, hx]
  · simp [extendFromChart, hx]

theorem extendFromChart_nonneg (g : C_c(U, ℝ)) (hg : 0 ≤ g) (x : ℂ) :
    0 ≤ extendFromChart U g x := by
  by_cases hx : x ∈ U
  · simp only [extendFromChart, hx, dite_true]; exact hg ⟨x, hx⟩
  · simp [extendFromChart, hx]

end Extend

/-- Limits of cutoff integrals along the fast sequence. -/
noncomputable def realizationLimit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y : Ω → ℝ → ℂ → ℝ) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index) (c : ℝ)
    (ω : Ω) (f : ℂ → ℝ) : ℝ :=
  limUnder atTop (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f ω)

theorem tendsto_realizationLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω)
    (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f ω) atTop
      (𝓝 (realizationLimit P U dens Y γ R e c ω f)) :=
  tendsto_nhds_limUnder (exists_tendsto_fastCutoff_of_mem_goodSet P U dens ε₀ Y hY T γ R e he c
    ω hω f hf hfc hfU)

theorem realizationLimit_add
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω)
    (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (f₁ f₂ : ℂ → ℝ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hf₁c : HasCompactSupport f₁) (hf₂c : HasCompactSupport f₂)
    (hf₁U : tsupport f₁ ⊆ U) (hf₂U : tsupport f₂ ⊆ U) :
    realizationLimit P U dens Y γ R e c ω (fun x => f₁ x + f₂ x) =
      realizationLimit P U dens Y γ R e c ω f₁ + realizationLimit P U dens Y γ R e c ω f₂ := by
  obtain ⟨n, hn⟩ := T.cofinal (tsupport f₁ ∪ tsupport f₂) (hf₁c.union hf₂c)
    (union_subset hf₁U hf₂U)
  obtain ⟨L₁, hL₁⟩ := hf₁.bounded_above_of_compact_support hf₁c
  obtain ⟨L₂, hL₂⟩ := hf₂.bounded_above_of_compact_support hf₂c
  have hsumc : HasCompactSupport (fun x => f₁ x + f₂ x) := hf₁c.add hf₂c
  have hsumU : tsupport (fun x => f₁ x + f₂ x) ⊆ U :=
    (tsupport_add f₁ f₂).trans (union_subset hf₁U hf₂U)
  have hlin (j : ℕ) : admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j)
      (fun x => f₁ x + f₂ x) ω = admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f₁ ω +
        admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f₂ ω :=
    admissibleCutoffIntegral_add P U dens ε₀ Y hY (T.chart (.inl (n, 0))) γ _ ω
      (hω.2 j (.inl (n, 0))) L₁ L₂ f₁ f₂ hf₁.measurable hf₂.measurable
      (fun x => by rw [← Real.norm_eq_abs]; exact hL₁ x)
      (fun x => by rw [← Real.norm_eq_abs]; exact hL₂ x)
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hn (Or.inl h))))
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hn (Or.inr h))))
  have h₁ := tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω f₁ hf₁ hf₁c hf₁U
  have h₂ := tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω f₂ hf₂ hf₂c hf₂U
  have hsum := tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω
    (fun x => f₁ x + f₂ x) (hf₁.add hf₂) hsumc hsumU
  have hfun : (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j)
      (fun x => f₁ x + f₂ x) ω) = fun j =>
        admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f₁ ω +
          admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f₂ ω := funext hlin
  rw [hfun] at hsum
  exact tendsto_nhds_unique hsum (h₁.add h₂)

theorem realizationLimit_smul
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω)
    (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (a : ℝ) (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    realizationLimit P U dens Y γ R e c ω (fun x => a * f x) =
      a * realizationLimit P U dens Y γ R e c ω f := by
  have h := tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω f hf hfc hfU
  have hc : HasCompactSupport (fun x => a * f x) := hfc.mul_left
  have hU' : tsupport (fun x => a * f x) ⊆ U :=
    (tsupport_mul_subset_right (f := fun _ => a)).trans hfU
  have hsmul := tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω
    (fun x => a * f x) (continuous_const.mul hf) hc hU'
  simp only [admissibleCutoffIntegral_smul] at hsmul
  exact tendsto_nhds_unique hsmul (h.const_mul a)

theorem realizationLimit_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω)
    (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ realizationLimit P U dens Y γ R e c ω f := by
  refine ge_of_tendsto (tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω f hf hfc hfU)
    (Eventually.of_forall fun j => ?_)
  exact integral_nonneg fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le

/-- The positive linear limit functional of a sample on continuous tests compactly supported in
the chart; it vanishes off the good set. -/
noncomputable def realizationFunctional {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω) : C_c(U, ℝ) →ₚ[ℝ] ℝ := by
  classical
  by_cases hω : ω ∈ realizationGoodSet P U dens Y T γ R e c
  · exact PositiveLinearMap.mk₀
      { toFun := fun g => realizationLimit P U dens Y γ R e c ω (extendFromChart U g)
        map_add' := fun g₁ g₂ => by
          rw [extendFromChart_add]
          exact realizationLimit_add P U dens ε₀ Y hY T γ R e he c ω hω _ _
            (continuous_extendFromChart hU g₁) (continuous_extendFromChart hU g₂)
            (hasCompactSupport_extendFromChart g₁) (hasCompactSupport_extendFromChart g₂)
            (tsupport_extendFromChart_subset_chart g₁) (tsupport_extendFromChart_subset_chart g₂)
        map_smul' := fun a g => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [extendFromChart_smul]
          exact realizationLimit_smul P U dens ε₀ Y hY T γ R e he c ω hω a _
            (continuous_extendFromChart hU g) (hasCompactSupport_extendFromChart g)
            (tsupport_extendFromChart_subset_chart g) }
      (fun g hg => realizationLimit_nonneg P U dens ε₀ Y hY T γ R e he c ω hω _
        (continuous_extendFromChart hU g) (hasCompactSupport_extendFromChart g)
        (tsupport_extendFromChart_subset_chart g) (extendFromChart_nonneg g hg))
  · exact 0

theorem realizationFunctional_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω)
    (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c) (g : C_c(U, ℝ)) :
    realizationFunctional P U hU dens ε₀ Y hY T γ R e he c ω g =
      realizationLimit P U dens Y γ R e c ω (extendFromChart U g) := by
  simp only [realizationFunctional, hω, dite_true]
  rfl

/-- The realized random measure: the push-forward of the Riesz measure of the limit functional
on the good set, and zero elsewhere. -/
noncomputable def realizationMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω) : Measure ℂ := by
  classical
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact if ω ∈ realizationGoodSet P U dens Y T γ R e c then
    Measure.map Subtype.val
      (RealRMK.rieszMeasure (realizationFunctional P U hU dens ε₀ Y hY T γ R e he c ω))
  else 0

end DOZZ.Assembly

/-! ### Basic properties of the realized measure

Basic properties of the realized random measure: it is carried by the chart, finite on
compact subsets of the chart, and on the good set its integrals of continuous tests with compact
support in the chart are the almost sure cutoff limits. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal CompactlySupported

namespace DOZZ.Assembly

open DOZZ.Proofs

section Props

variable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ)

theorem realizationMeasure_of_mem (ω : Ω) (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c) :
    letI : LocallyCompactSpace U := hU.locallyCompactSpace
    realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω = Measure.map Subtype.val
      (RealRMK.rieszMeasure (realizationFunctional P U hU dens ε₀ Y hY T γ R e he c ω)) := by
  simp only [realizationMeasure, hω, ite_true]

theorem realizationMeasure_of_notMem (ω : Ω) (hω : ω ∉ realizationGoodSet P U dens Y T γ R e c) :
    realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω = 0 := by
  simp only [realizationMeasure, hω, ite_false]

/-- The realized measure is carried by the chart. -/
theorem realizationMeasure_compl (ω : Ω) :
    realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω Uᶜ = 0 := by
  by_cases hω : ω ∈ realizationGoodSet P U dens Y T γ R e c
  · rw [realizationMeasure_of_mem P U hU dens ε₀ Y hY T γ R e he c ω hω,
      Measure.map_apply measurable_subtype_coe hU.isClosed_compl.measurableSet]
    have hempty : (Subtype.val : U → ℂ) ⁻¹' Uᶜ = ∅ := by
      ext y
      simp
    rw [hempty, measure_empty]
  · rw [realizationMeasure_of_notMem P U hU dens ε₀ Y hY T γ R e he c ω hω, Measure.coe_zero,
      Pi.zero_apply]

/-- The realized measure is finite on compact subsets of the chart. -/
theorem realizationMeasure_lt_top_of_isCompact (ω : Ω) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ U) : realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω K < ⊤ := by
  by_cases hω : ω ∈ realizationGoodSet P U dens Y T γ R e c
  · let : LocallyCompactSpace U := hU.locallyCompactSpace
    rw [realizationMeasure_of_mem P U hU dens ε₀ Y hY T γ R e he c ω hω,
      Measure.map_apply measurable_subtype_coe hK.measurableSet]
    have hcomp : IsCompact ((Subtype.val : U → ℂ) ⁻¹' K) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hKU]
      exact hK
    exact hcomp.measure_lt_top
  · rw [realizationMeasure_of_notMem P U hU dens ε₀ Y hY T γ R e he c ω hω, Measure.coe_zero,
      Pi.zero_apply]
    exact ENNReal.zero_lt_top

/-- On the good set, integrals of continuous tests with compact support in the chart are the
cutoff limits. -/
theorem integral_realizationMeasure (ω : Ω) (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∫ x, f x ∂realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω =
      realizationLimit P U dens Y γ R e c ω f := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [realizationMeasure_of_mem P U hU dens ε₀ Y hY T γ R e he c ω hω,
    integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
  have hcomp : IsCompact ((Subtype.val : U → ℂ) ⁻¹' tsupport f) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hfU]
    exact hfc
  have hsupp : HasCompactSupport (f ∘ (Subtype.val : U → ℂ)) := by
    refine hcomp.of_isClosed_subset (isClosed_tsupport _) ?_
    exact closure_minimal (fun y hy => subset_tsupport f hy)
      ((isClosed_tsupport f).preimage continuous_subtype_val)
  let g : C_c(U, ℝ) := ⟨⟨f ∘ Subtype.val, hf.comp continuous_subtype_val⟩, hsupp⟩
  have hint := RealRMK.integral_rieszMeasure
    (realizationFunctional P U hU dens ε₀ Y hY T γ R e he c ω) g
  have hext : extendFromChart U g = f := by
    funext x
    by_cases hx : x ∈ U
    · simp [extendFromChart, hx, g]
    · rw [extendFromChart_of_notMem g x hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hfU h))).symm
  rw [realizationFunctional_apply P U hU dens ε₀ Y hY T γ R e he c ω hω, hext] at hint
  exact hint

end Props

end DOZZ.Assembly

/-! ### Measurability of the realized measure

Measurability of the realized random measure.

Limits of measurable cutoff integrals are measurable on the good set; continuous ramps give the
mass of every open set whose closure lies in an exhausting compact; a π-system argument gives the
restrictions to the interiors of the exhausting compacts; and these exhaust the chart. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal CompactlySupported

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Every measure of an open set with nonempty complement is the supremum of its continuous
ramp integrals. -/
theorem measure_isOpen_eq_iSup_openRamp (μ : Measure ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hVc : Vᶜ.Nonempty) :
    μ V = ⨆ k : ℕ, ∫⁻ x, ENNReal.ofReal (openRamp V k x) ∂μ := by
  have hrampMeas (k : ℕ) : Measurable (fun x => ENNReal.ofReal (openRamp V k x)) :=
    ENNReal.measurable_ofReal.comp (openRamp V k).continuous.measurable
  rw [← lintegral_iSup hrampMeas (fun k m hkm x =>
    ENNReal.ofReal_le_ofReal (openRamp_mono V x hkm))]
  have hlim (x : ℂ) : (⨆ k, ENNReal.ofReal (openRamp V k x)) =
      V.indicator (fun _ => (1 : ℝ≥0∞)) x :=
    tendsto_nhds_unique (tendsto_atTop_iSup fun k m hkm =>
      ENNReal.ofReal_le_ofReal (openRamp_mono V x hkm)) (openRamp_tendsto V hV hVc x)
  simp only [hlim]
  rw [lintegral_indicator_const hV.measurableSet, one_mul]

section Measurable

variable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ)

include hY he in
/-- Cutoff limits of a continuous test supported in the chart are measurable on the good set. -/
theorem measurable_indicator_realizationLimit (f : ℂ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Measurable ((realizationGoodSet P U dens Y T γ R e c).indicator
      (fun ω => realizationLimit P U dens Y γ R e c ω f)) := by
  have hG := realizationGoodSet_measurable P U dens ε₀ Y hY T γ R e c
  refine measurable_of_tendsto_metrizable (f := fun j => (realizationGoodSet P U dens Y T γ R e c
    ).indicator (fun ω => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f ω))
    (fun j => (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ _ f
      hf.measurable).indicator hG) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ realizationGoodSet P U dens Y T γ R e c
  · simp only [Set.indicator_of_mem hω]
    exact tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω f hf hfc hfU
  · simp only [Set.indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- On the good set, nonnegative continuous tests supported in the chart integrate to their
cutoff limits in the extended sense. -/
theorem lintegral_realizationMeasure (ω : Ω) (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω =
      ENNReal.ofReal (realizationLimit P U dens Y γ R e c ω f) := by
  set μ := realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω
  have hfin : μ (tsupport f) < ⊤ :=
    realizationMeasure_lt_top_of_isCompact P U hU dens ε₀ Y hY T γ R e he c ω _ hfc hfU
  obtain ⟨L, hL⟩ := hf.bounded_above_of_compact_support hfc
  have hint : Integrable f μ := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport f) (subset_tsupport f)]
    have : IsFiniteMeasure (μ.restrict (tsupport f)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hfin⟩
    exact Integrable.of_bound hf.aestronglyMeasurable L (ae_of_all _ hL)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0),
    integral_realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω hω f hf hfc hfU]

/-- The mass of an open set whose closure lies in an exhausting compact is measurable. -/
theorem measurable_realizationMeasure_isOpen (n : ℕ) (V : Set ℂ) (hV : IsOpen V)
    (hVK : closure V ⊆ T.K n) :
    Measurable (fun ω => realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω V) := by
  have hG := realizationGoodSet_measurable P U dens ε₀ Y hY T γ R e c
  have hVc : Vᶜ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    subst h
    have hb := ((T.compact n).isBounded.subset (subset_closure.trans hVK))
    exact NormedSpace.unbounded_univ ℝ ℂ hb
  have hramp (k : ℕ) : Continuous (openRamp V k) ∧ HasCompactSupport (openRamp V k : ℂ → ℝ) ∧
      tsupport (openRamp V k : ℂ → ℝ) ⊆ U := by
    have hsupp : tsupport (openRamp V k : ℂ → ℝ) ⊆ T.K n := by
      refine (closure_mono ?_).trans ((closure_mono subset_closure).trans
        ((T.compact n).isClosed.closure_subset_iff.mpr hVK))
      intro x hx
      by_contra hxV
      apply hx
      rw [openRamp_apply, Metric.infDist_zero_of_mem (show x ∈ Vᶜ from hxV)]
      simp
    exact ⟨(openRamp V k).continuous, (T.compact n).of_isClosed_subset (isClosed_tsupport _) hsupp,
      hsupp.trans (T.subset n)⟩
  have heq : (fun ω => realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω V) = fun ω =>
      ⨆ k : ℕ, ENNReal.ofReal ((realizationGoodSet P U dens Y T γ R e c).indicator
        (fun ω => realizationLimit P U dens Y γ R e c ω (openRamp V k)) ω) := by
    funext ω
    by_cases hω : ω ∈ realizationGoodSet P U dens Y T γ R e c
    · rw [measure_isOpen_eq_iSup_openRamp _ V hV hVc]
      congr 1
      funext k
      rw [Set.indicator_of_mem hω, lintegral_realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω
        hω _ (hramp k).1 (hramp k).2.1 (hramp k).2.2 (openRamp_nonneg V k)]
    · rw [realizationMeasure_of_notMem P U hU dens ε₀ Y hY T γ R e he c ω hω]
      simp [Set.indicator_of_notMem hω]
  rw [heq]
  exact Measurable.iSup fun k => ENNReal.measurable_ofReal.comp
    (measurable_indicator_realizationLimit P U dens ε₀ Y hY T γ R e he c _ (hramp k).1
      (hramp k).2.1 (hramp k).2.2)

omit [IsProbabilityMeasure P] in
include hU in
/-- The interiors of the exhausting compacts exhaust the chart. -/
theorem iUnion_interior_K : (⋃ n, interior (T.K n)) = U := by
  apply subset_antisymm
  · exact iUnion_subset fun n => interior_subset.trans (T.subset n)
  · intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := T.cofinal (Metric.closedBall x (δ / 2)) (isCompact_closedBall _ _)
      ((Metric.closedBall_subset_ball (by linarith)).trans hball)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    exact interior_maximal (Metric.ball_subset_closedBall.trans hn) Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith))

/-- The restrictions of the realized measure to the interiors of the exhausting compacts are
measurable random finite measures. -/
theorem measurable_realizationMeasure_restrict_interior (n : ℕ) :
    Measurable (fun ω => (realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω).restrict
      (interior (T.K n))) := by
  have hcl : closure (interior (T.K n)) ⊆ T.K n :=
    (closure_mono interior_subset).trans (T.compact n).isClosed.closure_subset
  have hfin : ∀ ω, IsFiniteMeasure ((realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω).restrict
      (interior (T.K n))) := fun ω => ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono interior_subset)
      (realizationMeasure_lt_top_of_isCompact P U hU dens ε₀ Y hY T γ R e he c ω _ (T.compact n)
        (T.subset n))⟩
  refine Measurable.measure_of_isPiSystem (S := {s : Set ℂ | IsOpen s})
    (BorelSpace.measurable_eq.trans rfl) isPiSystem_isOpen ?_ ?_
  · intro s hs
    have hs' : IsOpen s := hs
    simp_rw [Measure.restrict_apply hs'.measurableSet]
    exact measurable_realizationMeasure_isOpen P U hU dens ε₀ Y hY T γ R e he c n _
      (hs'.inter isOpen_interior) ((closure_mono inter_subset_right).trans hcl)
  · simp_rw [Measure.restrict_apply_univ]
    exact measurable_realizationMeasure_isOpen P U hU dens ε₀ Y hY T γ R e he c n _
      isOpen_interior hcl

/-- The realized random measure is measurable. -/
theorem measurable_realizationMeasure :
    Measurable (fun ω => realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hmono : Monotone (fun n => A ∩ interior (T.K n)) := fun n m hnm =>
    inter_subset_inter_right _ (interior_mono (monotone_nat_of_le_succ T.mono hnm))
  have heq : (fun ω => realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω A) = fun ω =>
      ⨆ n, (realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω).restrict
        (interior (T.K n)) A := by
    funext ω
    have hAU : A ∩ U = ⋃ n, A ∩ interior (T.K n) := by
      rw [← inter_iUnion, iUnion_interior_K U hU T]
    rw [← measure_inter_conull (t := U)
      (realizationMeasure_compl P U hU dens ε₀ Y hY T γ R e he c ω), hAU,
      hmono.measure_iUnion]
    simp_rw [Measure.restrict_apply hA]
  rw [heq]
  exact Measurable.iSup fun n => (Measure.measurable_coe hA).comp
    (measurable_realizationMeasure_restrict_interior P U hU dens ε₀ Y hY T γ R e he c n)

end Measurable

end DOZZ.Assembly
