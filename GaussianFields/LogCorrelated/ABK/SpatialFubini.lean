/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Dilation

/-!
# GaussianFields.LogCorrelated/ABK/SpatialFubini

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- Product of two compactly supported functions on `Vec d` has compact support on the product. -/
theorem hasCompactSupport_prod_mul_vec {d : Nat} {f g : Vec d → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun p : Vec d × Vec d => f p.1 * g p.2) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf.isCompact.prod hg.isCompact) ?_
  intro p hp
  have hf_ne : f p.1 ≠ 0 := by
    intro hzero
    exact hp (by simp [hzero])
  have hg_ne : g p.2 ≠ 0 := by
    intro hzero
    exact hp (by simp [hzero])
  exact ⟨subset_tsupport f hf_ne, subset_tsupport g hg_ne⟩

/-- Compact support for the two-variable integrand used to pair an ABK spatial convolution
against a compactly supported test function. -/
theorem hasCompactSupport_abkSpatialConvolution_pair_integrand {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (r : ℝ)
    {F : Vec d → ℝ} (hF_cs : HasCompactSupport F) :
    HasCompactSupport
      (Function.uncurry
        (fun y x : Vec d =>
          (abkScaledCutoff ζ r (y - x) * ψ x) * F y)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hF_cs.isCompact.prod ψ.hasCompactSupport.isCompact) ?_
  intro p hp
  have hF_ne : F p.1 ≠ 0 := by
    intro hzero
    exact hp (by simp [Function.uncurry, hzero])
  have hψ_ne : ψ p.2 ≠ 0 := by
    intro hzero
    exact hp (by simp [Function.uncurry, hzero])
  exact ⟨subset_tsupport F hF_ne, subset_tsupport ψ hψ_ne⟩

/-- Pairing a fixed-scale ABK spatial convolution against a compactly supported continuous
function allows the convolution integral to be swapped by Fubini. -/
theorem integral_abkSpatialConvolution_mul_eq_integral_integral {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (r : ℝ)
    {F : Vec d → ℝ} (hF_cont : Continuous F) (hF_cs : HasCompactSupport F) :
    (∫ y : Vec d, abkSpatialConvolution ζ ψ r y * F y
        ∂(volume : Measure (Vec d))) =
      ∫ x : Vec d,
        ψ x *
          (∫ y : Vec d, abkScaledCutoff ζ r (y - x) * F y
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
  let G : Vec d → Vec d → ℝ := fun y x =>
    (abkScaledCutoff ζ r (y - x) * ψ x) * F y
  have hG_cont : Continuous (Function.uncurry G) := by
    change Continuous
      (fun p : Vec d × Vec d =>
        (abkScaledCutoff ζ r (p.1 - p.2) * ψ p.2) * F p.1)
    have hsub : Continuous (fun p : Vec d × Vec d => p.1 - p.2) :=
      continuous_fst.sub continuous_snd
    have hscaled : Continuous (fun p : Vec d × Vec d => r⁻¹ • (p.1 - p.2)) :=
      (continuous_const_smul (r⁻¹)).comp hsub
    have hcut : Continuous (fun p : Vec d × Vec d => abkScaledCutoff ζ r (p.1 - p.2)) := by
      exact ζ.continuous.comp hscaled
    exact (hcut.mul (ψ.continuous.comp continuous_snd)).mul (hF_cont.comp continuous_fst)
  have hG_cs : HasCompactSupport (Function.uncurry G) := by
    simpa [G] using
      hasCompactSupport_abkSpatialConvolution_pair_integrand ζ ψ r hF_cs
  calc
    (∫ y : Vec d, abkSpatialConvolution ζ ψ r y * F y
        ∂(volume : Measure (Vec d)))
        = ∫ y : Vec d, ∫ x : Vec d, G y x ∂(volume : Measure (Vec d))
            ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          unfold abkSpatialConvolution
          rw [integral_mul_const]
    _ = ∫ x : Vec d, ∫ y : Vec d, G y x ∂(volume : Measure (Vec d))
          ∂(volume : Measure (Vec d)) := by
          exact MeasureTheory.integral_integral_swap_of_hasCompactSupport hG_cont hG_cs
    _ = ∫ x : Vec d,
        ψ x *
          (∫ y : Vec d, abkScaledCutoff ζ r (y - x) * F y
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards with y
          dsimp [G]
          ring

/-- Pairing a translated scaled cutoff against a fixed-scale ABK spatial convolution collapses to
the scaled cutoff self-convolution. -/
theorem integral_abkScaledCutoff_mul_abkSpatialConvolution_eq_selfConvolution_integral
    {d : Nat} (ζ : ABKCutoff d) (φ : MeanZeroTestFunction d) {r : ℝ}
    (hr : r ≠ 0) (x : Vec d) :
    (∫ y : Vec d,
        abkScaledCutoff ζ r (y - x) * abkSpatialConvolution ζ φ r y
        ∂(volume : Measure (Vec d))) =
      ∫ z : Vec d,
        φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
        ∂(volume : Measure (Vec d)) := by
  let F : Vec d → ℝ := fun y => abkScaledCutoff ζ r (y - x)
  have hF_cont : Continuous F := by
    dsimp [F]
    exact (continuous_abkScaledCutoff ζ r).comp (continuous_id.sub continuous_const)
  have hF_cs : HasCompactSupport F := by
    have hbase : HasCompactSupport (abkScaledCutoff ζ r) :=
      hasCompactSupport_abkScaledCutoff ζ hr
    simpa [F, Function.comp_def] using hbase.comp_homeomorph (Homeomorph.subRight x)
  have hswap :=
    integral_abkSpatialConvolution_mul_eq_integral_integral
      (ζ := ζ) (ψ := φ) (r := r) hF_cont hF_cs
  calc
    (∫ y : Vec d,
        abkScaledCutoff ζ r (y - x) * abkSpatialConvolution ζ φ r y
        ∂(volume : Measure (Vec d)))
        = ∫ y : Vec d, abkSpatialConvolution ζ φ r y * F y
            ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          dsimp [F]
          ring
    _ = ∫ z : Vec d,
          φ z *
            (∫ y : Vec d, abkScaledCutoff ζ r (y - z) * F y
              ∂(volume : Measure (Vec d)))
          ∂(volume : Measure (Vec d)) := hswap
    _ = ∫ z : Vec d,
        φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
        ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with z
          congr 1
          dsimp [F]
          calc
            (∫ y : Vec d,
                abkScaledCutoff ζ r (y - z) * abkScaledCutoff ζ r (y - x)
                ∂(volume : Measure (Vec d)))
                = ∫ y : Vec d,
                    abkScaledCutoff ζ r (x - y) * abkScaledCutoff ζ r (z - y)
                    ∂(volume : Measure (Vec d)) := by
                  refine integral_congr_ae ?_
                  filter_upwards with y
                  have hyz : y - z = -(z - y) := by
                    ext i
                    simp only [Pi.sub_apply, Pi.neg_apply]
                    ring
                  have hyx : y - x = -(x - y) := by
                    ext i
                    simp only [Pi.sub_apply, Pi.neg_apply]
                    ring
                  rw [hyz, hyx, abkScaledCutoff_neg, abkScaledCutoff_neg]
                  ring
            _ = abkScaledCutoffSelfConvolution ζ r (x - z) := by
                  exact integral_abkScaledCutoff_mul_abkScaledCutoff_sub_eq_selfConvolution
                    ζ r x z

/-- Fixed-scale spatial covariance identity: the `L²` inner product of two ABK spatial
convolutions is the double integral against the scaled cutoff self-convolution. -/
theorem integral_abkSpatialConvolution_mul_abkSpatialConvolution_eq_selfConvolution_integral
    {d : Nat} (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) {r : ℝ}
    (hr : 0 < r) :
    (∫ y : Vec d,
        abkSpatialConvolution ζ ψ r y * abkSpatialConvolution ζ φ r y
        ∂(volume : Measure (Vec d))) =
      ∫ x : Vec d,
        ψ x *
          (∫ z : Vec d,
            φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
  have hF_cont : Continuous (fun y : Vec d => abkSpatialConvolution ζ φ r y) :=
    continuous_abkSpatialConvolution ζ φ hr.ne'
  have hF_cs : HasCompactSupport (fun y : Vec d => abkSpatialConvolution ζ φ r y) :=
    hasCompactSupport_abkSpatialConvolution ζ φ hr
  have hswap :=
    integral_abkSpatialConvolution_mul_eq_integral_integral
      (ζ := ζ) (ψ := ψ) (r := r) hF_cont hF_cs
  calc
    (∫ y : Vec d,
        abkSpatialConvolution ζ ψ r y * abkSpatialConvolution ζ φ r y
        ∂(volume : Measure (Vec d)))
        = ∫ x : Vec d,
            ψ x *
              (∫ y : Vec d,
                abkScaledCutoff ζ r (y - x) *
                  abkSpatialConvolution ζ φ r y
                ∂(volume : Measure (Vec d)))
            ∂(volume : Measure (Vec d)) := hswap
    _ = ∫ x : Vec d,
        ψ x *
          (∫ z : Vec d,
            φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [integral_abkScaledCutoff_mul_abkSpatialConvolution_eq_selfConvolution_integral
            ζ φ hr.ne' x]

end GaussianFields

end
