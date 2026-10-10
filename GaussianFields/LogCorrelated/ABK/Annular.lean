/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.CanonicalField

/-!
# GaussianFields ABK annular field

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Annular shell kernels -/

/-- The annular interval `[a,b]` in the scale variable, implemented as an indicator on the product
kernel.  ABK uses `a = 3^{n-1}` and `b = 3^n`. -/
@[expose]
noncomputable def abkAnnularLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ) :
    ℝ × Vec d → ℝ :=
  (abkScaleShell (d := d) a b).indicator (abkLogKernelProd normalization ζ ψ)

@[simp]
theorem abkAnnularLogKernelProd_apply {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ) (p : ℝ × Vec d) :
    abkAnnularLogKernelProd normalization ζ ψ a b p =
      if p.1 ∈ Set.Ioc a b then
        abkLogKernelProd normalization ζ ψ p
      else
        0 := by
  by_cases hp : p.1 ∈ Set.Ioc a b
  · have hp' : p ∈ abkScaleShell (d := d) a b := hp
    rw [ite_eq_left hp]
    exact Set.indicator_of_mem hp' (abkLogKernelProd normalization ζ ψ)
  · have hp' : p ∉ abkScaleShell (d := d) a b := hp
    rw [ite_eq_right hp]
    exact Set.indicator_of_notMem hp' (abkLogKernelProd normalization ζ ψ)

/-- The annular ABK kernel on concrete scale-space. -/
@[expose]
noncomputable def abkAnnularLogKernel {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ) :
    ScaleSpace d → ℝ :=
  abkAnnularLogKernelProd normalization ζ ψ a b ∘ scaleSpaceMeasurableEquiv d

theorem memLp_abkAnnularLogKernel_of_prod {d : Nat} {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d} {a b : ℝ}
    (hprod :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkAnnularLogKernel normalization ζ ψ a b) 2
      (volume : Measure (ScaleSpace d)) := by
  simpa [abkAnnularLogKernel] using
    hprod.comp_measurePreserving (scaleSpaceMeasurePreserving d)

/-- Annular shell kernels inherit `L²` membership from the full ABK product kernel. -/
theorem memLp_abkAnnularLogKernelProd_of_memLp_abkLogKernelProd {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d} {a b : ℝ}
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
      (volume : Measure (ℝ × Vec d)) := by
  simpa [abkAnnularLogKernelProd] using
    hprod.indicator (measurableSet_abkScaleShell (d := d) a b)

/-- Annular shell kernels are in `L²` by the ABK estimates. -/
theorem memLp_abkAnnularLogKernelProd_of_abk_estimates {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    {a b : ℝ} (hd : 0 < d) :
    MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
      (volume : Measure (ℝ × Vec d)) :=
  memLp_abkAnnularLogKernelProd_of_memLp_abkLogKernelProd
    (a := a) (b := b) (memLp_abkLogKernelProd_of_abk_estimates hd)

/-- The annular `L²(R^{1+d})` vector sent into white noise. -/
@[expose]
noncomputable def abkAnnularLogKernelLp {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ)
    (hprod :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseHilbert d :=
  (memLp_abkAnnularLogKernel_of_prod
      (normalization := normalization) (ζ := ζ) (ψ := ψ) (a := a) (b := b) hprod).toLp
    (abkAnnularLogKernel normalization ζ ψ a b)

/-- The ABK annular shell contribution, tested against `ψ`. -/
@[expose]
noncomputable def abkAnnularLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (a b : ℝ)
    (hprod :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d))) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  scaleSpaceWhiteNoiseL2 d (abkAnnularLogKernelLp normalization ζ ψ a b hprod)

/-- Covariance of two annular shell evaluations. -/
theorem covariance_abkAnnularLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (a b c e : ℝ)
    (hψ :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkAnnularLogKernelProd normalization ζ φ c e) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkAnnularLogCorrelatedFieldL2 normalization ζ ψ a b hψ,
        abkAnnularLogCorrelatedFieldL2 normalization ζ φ c e hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ⟪abkAnnularLogKernelLp normalization ζ ψ a b hψ,
        abkAnnularLogKernelLp normalization ζ φ c e hφ⟫_ℝ := by
  exact covariance_scaleSpaceWhiteNoiseL2
    (abkAnnularLogKernelLp normalization ζ ψ a b hψ)
    (abkAnnularLogKernelLp normalization ζ φ c e hφ)

/-- Product-coordinate form of the annular deterministic kernel inner product. -/
theorem inner_abkAnnularLogKernelLp_eq_prod_integral {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (a b c e : ℝ)
    (hψ :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkAnnularLogKernelProd normalization ζ φ c e) 2
        (volume : Measure (ℝ × Vec d))) :
    ⟪abkAnnularLogKernelLp normalization ζ ψ a b hψ,
        abkAnnularLogKernelLp normalization ζ φ c e hφ⟫_ℝ =
      ∫ p : ℝ × Vec d,
        abkAnnularLogKernelProd normalization ζ ψ a b p *
          abkAnnularLogKernelProd normalization ζ φ c e p := by
  change
    ⟪(memLp_abkAnnularLogKernel_of_prod
          (normalization := normalization) (ζ := ζ) (ψ := ψ) (a := a) (b := b) hψ).toLp
        (abkAnnularLogKernel normalization ζ ψ a b),
      (memLp_abkAnnularLogKernel_of_prod
          (normalization := normalization) (ζ := ζ) (ψ := φ) (a := c) (b := e) hφ).toLp
        (abkAnnularLogKernel normalization ζ φ c e)⟫_ℝ =
      ∫ p : ℝ × Vec d,
        abkAnnularLogKernelProd normalization ζ ψ a b p *
          abkAnnularLogKernelProd normalization ζ φ c e p
  rw [inner_toLp_real
    (memLp_abkAnnularLogKernel_of_prod
      (normalization := normalization) (ζ := ζ) (ψ := ψ) (a := a) (b := b) hψ)
    (memLp_abkAnnularLogKernel_of_prod
      (normalization := normalization) (ζ := ζ) (ψ := φ) (a := c) (b := e) hφ)]
  exact (scaleSpaceMeasurePreserving d).integral_comp'
    (f := scaleSpaceMeasurableEquiv d)
    (g := fun p : ℝ × Vec d =>
      abkAnnularLogKernelProd normalization ζ ψ a b p *
        abkAnnularLogKernelProd normalization ζ φ c e p)

/-- Product-coordinate covariance formula for annular ABK shell contributions. -/
theorem covariance_abkAnnularLogCorrelatedFieldL2_eq_prod_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (a b c e : ℝ)
    (hψ :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkAnnularLogKernelProd normalization ζ φ c e) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkAnnularLogCorrelatedFieldL2 normalization ζ ψ a b hψ,
        abkAnnularLogCorrelatedFieldL2 normalization ζ φ c e hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        abkAnnularLogKernelProd normalization ζ ψ a b p *
          abkAnnularLogKernelProd normalization ζ φ c e p := by
  rw [covariance_abkAnnularLogCorrelatedFieldL2,
    inner_abkAnnularLogKernelLp_eq_prod_integral]

/-- Expanded covariance formula for annular ABK shell contributions. -/
theorem covariance_abkAnnularLogCorrelatedFieldL2_eq_abk_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (a b c e : ℝ)
    (hψ :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkAnnularLogKernelProd normalization ζ φ c e) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkAnnularLogCorrelatedFieldL2 normalization ζ ψ a b hψ,
        abkAnnularLogCorrelatedFieldL2 normalization ζ φ c e hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        if p.1 ∈ Set.Ioc a b ∧ p.1 ∈ Set.Ioc c e ∧ 0 < p.1 then
          normalization ^ (2 : Nat) * p.1 ^ (-((d : ℝ) + 1)) *
            (abkSpatialConvolution ζ ψ p.1 p.2 *
              abkSpatialConvolution ζ φ p.1 p.2)
        else
          0 := by
  rw [covariance_abkAnnularLogCorrelatedFieldL2_eq_prod_integral]
  refine integral_congr_ae ?_
  filter_upwards with p
  by_cases hpab : p.1 ∈ Set.Ioc a b
  · by_cases hpce : p.1 ∈ Set.Ioc c e
    · rw [abkAnnularLogKernelProd_apply, abkAnnularLogKernelProd_apply,
        ite_eq_left hpab, ite_eq_left hpce, abkLogKernelProd_mul]
      by_cases hpos : 0 < p.1
      · rw [ite_eq_left hpos, ite_eq_left ⟨hpab, hpce, hpos⟩]
      · rw [ite_eq_right hpos, ite_eq_right]
        exact fun h => hpos h.2.2
    · rw [abkAnnularLogKernelProd_apply, abkAnnularLogKernelProd_apply,
        ite_eq_left hpab, ite_eq_right hpce]
      simp [hpce]
  · rw [abkAnnularLogKernelProd_apply, ite_eq_right hpab]
    simp [hpab]

/-- Disjoint annular kernels have zero deterministic inner product. -/
theorem inner_abkAnnularLogKernelLp_eq_zero_of_disjoint {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (a b c e : ℝ)
    (hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c e))
    (hψ :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkAnnularLogKernelProd normalization ζ φ c e) 2
        (volume : Measure (ℝ × Vec d))) :
    ⟪abkAnnularLogKernelLp normalization ζ ψ a b hψ,
        abkAnnularLogKernelLp normalization ζ φ c e hφ⟫_ℝ = 0 := by
  change
    ⟪(memLp_abkAnnularLogKernel_of_prod
          (normalization := normalization) (ζ := ζ) (ψ := ψ) (a := a) (b := b) hψ).toLp
        (abkAnnularLogKernel normalization ζ ψ a b),
      (memLp_abkAnnularLogKernel_of_prod
          (normalization := normalization) (ζ := ζ) (ψ := φ) (a := c) (b := e) hφ).toLp
        (abkAnnularLogKernel normalization ζ φ c e)⟫_ℝ = 0
  rw [inner_toLp_real
    (memLp_abkAnnularLogKernel_of_prod
      (normalization := normalization) (ζ := ζ) (ψ := ψ) (a := a) (b := b) hψ)
    (memLp_abkAnnularLogKernel_of_prod
      (normalization := normalization) (ζ := ζ) (ψ := φ) (a := c) (b := e) hφ)]
  have hzero :
      (fun z : ScaleSpace d =>
        abkAnnularLogKernel normalization ζ ψ a b z *
          abkAnnularLogKernel normalization ζ φ c e z) =
        fun _ => 0 := by
    funext z
    let p : ℝ × Vec d := scaleSpaceMeasurableEquiv d z
    change
      (abkAnnularLogKernelProd normalization ζ ψ a b p) *
        (abkAnnularLogKernelProd normalization ζ φ c e p) = 0
    unfold abkAnnularLogKernelProd
    by_cases hzab : p.1 ∈ Set.Ioc a b
    · have hzab' : p ∈ abkScaleShell (d := d) a b := hzab
      have hzce : p.1 ∉ Set.Ioc c e := by
        exact fun hzce => hdisj.le_bot ⟨hzab, hzce⟩
      have hzce' : p ∉ abkScaleShell (d := d) c e := hzce
      rw [Set.indicator_of_mem hzab', Set.indicator_of_notMem hzce']
      simp
    · have hzab' : p ∉ abkScaleShell (d := d) a b := hzab
      rw [Set.indicator_of_notMem hzab']
      simp
  rw [hzero]
  simp

theorem covariance_abkAnnularLogCorrelatedFieldL2_eq_zero_of_disjoint {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (a b c e : ℝ) (hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c e))
    (hψ :
      MemLp (abkAnnularLogKernelProd normalization ζ ψ a b) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkAnnularLogKernelProd normalization ζ φ c e) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkAnnularLogCorrelatedFieldL2 normalization ζ ψ a b hψ,
        abkAnnularLogCorrelatedFieldL2 normalization ζ φ c e hφ;
        scaleSpaceWhiteNoiseMeasure d] = 0 := by
  rw [covariance_abkAnnularLogCorrelatedFieldL2,
    inner_abkAnnularLogKernelLp_eq_zero_of_disjoint
      normalization ζ ψ φ a b c e hdisj hψ hφ]

end GaussianFields

end
