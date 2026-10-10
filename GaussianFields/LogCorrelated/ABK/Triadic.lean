/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Annular

/-!
# GaussianFields ABK triadic field

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## Triadic ABK shells -/

/-- The ABK triadic scale shell `(3^{n-1}, 3^n]`. -/
@[expose]
def abkTriadicScaleShell (n : ℤ) : Set ℝ :=
  Set.Ioc ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

noncomputable instance instDecidableMem_abkTriadicScaleShell (n : ℤ) (r : ℝ) :
    Decidable (r ∈ abkTriadicScaleShell n) := by
  unfold abkTriadicScaleShell
  infer_instance

/-- Distinct ABK triadic scale shells are disjoint. -/
theorem pairwise_disjoint_abkTriadicScaleShell :
    Pairwise (fun m n => Disjoint (abkTriadicScaleShell m) (abkTriadicScaleShell n)) := by
  intro m n hmn
  by_cases hlt : m < n
  · have hmle : m ≤ n - 1 := by omega
    exact Set.Ioc_disjoint_Ioc_of_le
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hmle)
  · have hnlt : n < m := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hmn)
    have hnle : n ≤ m - 1 := by omega
    exact (Set.Ioc_disjoint_Ioc_of_le
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hnle)).symm

/-- Triadic scale shells lie in positive scales. -/
theorem zero_lt_of_mem_abkTriadicScaleShell {n : ℤ} {r : ℝ}
    (hr : r ∈ abkTriadicScaleShell n) : 0 < r := by
  exact (zpow_pos (by norm_num : (0 : ℝ) < 3) (n - 1)).trans hr.1

/-- The `n`th ABK triadic product-coordinate shell kernel. -/
@[expose]
noncomputable def abkTriadicLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ) :
    ℝ × Vec d → ℝ :=
  abkAnnularLogKernelProd normalization ζ ψ ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

/-- Triadic ABK shell kernels are in `L²` by the ABK estimates. -/
theorem memLp_abkTriadicLogKernelProd_of_abk_estimates {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    {n : ℤ} (hd : 0 < d) :
    MemLp (abkTriadicLogKernelProd normalization ζ ψ n) 2
      (volume : Measure (ℝ × Vec d)) := by
  simpa [abkTriadicLogKernelProd] using
    memLp_abkAnnularLogKernelProd_of_abk_estimates
      (normalization := normalization) (ζ := ζ) (ψ := ψ)
      (a := (3 : ℝ) ^ (n - 1)) (b := (3 : ℝ) ^ n) hd

/-- The `n`th ABK triadic shell kernel on concrete scale-space. -/
@[expose]
noncomputable def abkTriadicLogKernel {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ) :
    ScaleSpace d → ℝ :=
  abkAnnularLogKernel normalization ζ ψ ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)

/-- The `n`th ABK triadic `L²(R^{1+d})` kernel. -/
@[expose]
noncomputable def abkTriadicLogKernelLp {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ)
    (hprod :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ n) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseHilbert d :=
  abkAnnularLogKernelLp normalization ζ ψ ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n) hprod

/-- The `n`th ABK triadic shell contribution, tested against `ψ`. -/
@[expose]
noncomputable def abkTriadicLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (n : ℤ)
    (hprod :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ n) 2
        (volume : Measure (ℝ × Vec d))) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  abkAnnularLogCorrelatedFieldL2 normalization ζ ψ
    ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n) hprod

/-- Distinct triadic ABK shell evaluations have zero covariance. -/
theorem covariance_abkTriadicLogCorrelatedFieldL2_eq_zero_of_ne {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    {m n : ℤ} (hmn : m ≠ n)
    (hψ :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ m) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkTriadicLogKernelProd normalization ζ φ n) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkTriadicLogCorrelatedFieldL2 normalization ζ ψ m hψ,
        abkTriadicLogCorrelatedFieldL2 normalization ζ φ n hφ;
        scaleSpaceWhiteNoiseMeasure d] = 0 := by
  exact covariance_abkAnnularLogCorrelatedFieldL2_eq_zero_of_disjoint
    normalization ζ ψ φ ((3 : ℝ) ^ (m - 1)) ((3 : ℝ) ^ m)
    ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n)
    (pairwise_disjoint_abkTriadicScaleShell hmn) hψ hφ

/-- Expanded covariance formula for triadic ABK shell contributions `H_m` and `H_n`. -/
theorem covariance_abkTriadicLogCorrelatedFieldL2_eq_abk_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (m n : ℤ)
    (hψ :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ m) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkTriadicLogKernelProd normalization ζ φ n) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkTriadicLogCorrelatedFieldL2 normalization ζ ψ m hψ,
        abkTriadicLogCorrelatedFieldL2 normalization ζ φ n hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        if p.1 ∈ abkTriadicScaleShell m ∧ p.1 ∈ abkTriadicScaleShell n ∧ 0 < p.1 then
          normalization ^ (2 : Nat) * p.1 ^ (-((d : ℝ) + 1)) *
            (abkSpatialConvolution ζ ψ p.1 p.2 *
              abkSpatialConvolution ζ φ p.1 p.2)
        else
          0 := by
  simpa [abkTriadicLogCorrelatedFieldL2, abkTriadicLogKernelProd, abkTriadicScaleShell]
    using covariance_abkAnnularLogCorrelatedFieldL2_eq_abk_integral
      (d := d) normalization ζ ψ φ
      ((3 : ℝ) ^ (m - 1)) ((3 : ℝ) ^ m)
      ((3 : ℝ) ^ (n - 1)) ((3 : ℝ) ^ n) hψ hφ

/-- Same-shell covariance formula for the ABK triadic contribution `H_n`. -/
theorem covariance_abkTriadicLogCorrelatedFieldL2_self_eq_abk_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (n : ℤ)
    (hψ :
      MemLp (abkTriadicLogKernelProd normalization ζ ψ n) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkTriadicLogKernelProd normalization ζ φ n) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkTriadicLogCorrelatedFieldL2 normalization ζ ψ n hψ,
        abkTriadicLogCorrelatedFieldL2 normalization ζ φ n hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        if p.1 ∈ abkTriadicScaleShell n then
          normalization ^ (2 : Nat) * p.1 ^ (-((d : ℝ) + 1)) *
            (abkSpatialConvolution ζ ψ p.1 p.2 *
              abkSpatialConvolution ζ φ p.1 p.2)
        else
          0 := by
  rw [covariance_abkTriadicLogCorrelatedFieldL2_eq_abk_integral
    (d := d) normalization ζ ψ φ n n hψ hφ]
  refine integral_congr_ae ?_
  filter_upwards with p
  by_cases hp : p.1 ∈ abkTriadicScaleShell n
  · rw [ite_eq_left ⟨hp, hp, zero_lt_of_mem_abkTriadicScaleShell hp⟩, ite_eq_left hp]
  · rw [ite_eq_right, ite_eq_right hp]
    exact fun h => hp h.1

end GaussianFields

end
