/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Lebesgue change of variables for local affine charts in the complex plane. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Real dilation on the complex plane scales area by the inverse square. -/
theorem complexVolume_map_smul {c : ℝ} (hc : c ≠ 0) :
    Measure.map (fun z : ℂ => c • z) (volume : Measure ℂ) =
      ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume := by
  simpa [Complex.finrank_real_complex] using
    (Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) hc)

/-- A translated dilation has the same area factor as the dilation. -/
theorem complexVolume_map_affine {a : ℂ} {c : ℝ} (hc : c ≠ 0) :
    Measure.map (fun z : ℂ => a + c • z) (volume : Measure ℂ) =
      ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume := by
  have hcomp : (fun z : ℂ => a + c • z) =
      (fun z => a + z) ∘ (fun z : ℂ => c • z) := by
    funext z
    rfl
  calc
    Measure.map (fun z : ℂ => a + c • z) volume =
        (Measure.map (fun z : ℂ => c • z) volume).map (fun z => a + z) := by
          rw [hcomp, ← Measure.map_map (measurable_const_add a) (measurable_const_smul c)]
    _ = (ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume).map (fun z => a + z) := by
          rw [complexVolume_map_smul hc]
    _ = ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume := by
          rw [Measure.map_smul _ (measurable_const_add a).aemeasurable,
            Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := volume) a]

/-- A positive complex dilation maps a centered closed disk to the disk with its scaled radius. -/
theorem complex_affine_image_closedBall {a : ℂ} {c R : ℝ} (hc : 0 < c) :
    (fun z : ℂ => a + c • z) '' Metric.closedBall (0 : ℂ) R =
      Metric.closedBall a (c * R) := by
  have hdist (x : ℂ) : dist (a + c • x) a = c * dist x 0 := by
    calc
      dist (a + c • x) a = ‖(a + c • x) - a‖ := dist_eq_norm _ _
      _ = ‖c • x‖ := by congr 1; abel
      _ = ‖c‖ * ‖x‖ := norm_smul _ _
      _ = c * dist x 0 := by
        rw [Real.norm_eq_abs, abs_of_pos hc, dist_eq_norm, sub_zero]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, hdist]
    have hx' : dist x 0 ≤ R := by simpa [Metric.mem_closedBall] using hx
    nlinarith [mul_le_mul_of_nonneg_left hx' (le_of_lt hc)]
  · intro hy
    have hy' : dist y a ≤ c * R := by simpa [Metric.mem_closedBall] using hy
    let x : ℂ := (c⁻¹ : ℝ) • (y - a)
    have hdistInv : dist x 0 = c⁻¹ * dist y a := by
      dsimp [x]
      calc
        dist ((c⁻¹ : ℝ) • (y - a)) 0 = ‖(c⁻¹ : ℝ) • (y - a)‖ := by
          rw [dist_eq_norm, sub_zero]
        _ = c⁻¹ * ‖y - a‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
        _ = c⁻¹ * dist y a := by rw [dist_eq_norm]
    have hx : x ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, hdistInv]
      calc
        c⁻¹ * dist y a ≤ c⁻¹ * (c * R) :=
          mul_le_mul_of_nonneg_left hy' (le_of_lt (inv_pos.mpr hc))
        _ = R := by field_simp [hc.ne']
    refine ⟨x, hx, ?_⟩
    dsimp [x]
    calc
      a + c • ((c⁻¹ : ℝ) • (y - a)) = a + (y - a) := by
        rw [smul_smul]
        simp [hc.ne']
      _ = y := by abel

/-- Restricting the change of variables to a measurable chart domain transports its volume to
the affine image domain with the same Jacobian factor. -/
theorem complexVolume_map_affine_restrict
    {a : ℂ} {c : ℝ} (hc : c ≠ 0) (K : Set ℂ)
    (himage : MeasurableSet ((fun z : ℂ => a + c • z) '' K)) :
    Measure.map (fun z : ℂ => a + c • z) (volume.restrict K) =
      ENNReal.ofReal (|(c ^ 2)⁻¹|) •
        volume.restrict ((fun z : ℂ => a + c • z) '' K) := by
  let f : ℂ → ℂ := fun z => a + c • z
  have hf : Measurable f := by fun_prop
  have hinj : Function.Injective f := by
    intro x y hxy
    have hsmul : c • x = c • y := add_left_cancel hxy
    exact (smul_right_injective ℂ hc) hsmul
  calc
    Measure.map f (volume.restrict K) = (Measure.map f volume).restrict (f '' K) := by
      rw [Measure.restrict_map hf himage, Set.preimage_image_eq _ hinj]
    _ = (ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume).restrict (f '' K) := by
      rw [complexVolume_map_affine hc]
    _ = ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume.restrict (f '' K) := by
      rw [Measure.restrict_smul]

/-- Integral form of the affine change of variables on a restricted planar domain. The inverse
Jacobian appears because the affine map is pushed forward. -/
theorem complex_integral_affine_restrict
    {a : ℂ} {c : ℝ} (hc : c ≠ 0) (K : Set ℂ)
    (himage : MeasurableSet ((fun z : ℂ => a + c • z) '' K))
    (g : ℂ → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) =
      (|(c ^ 2)⁻¹|)⁻¹ *
        ∫ x, g (a + c • x) ∂volume.restrict K := by
  let J : ℝ := (c ^ 2)⁻¹
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hJ : J ≠ 0 := by
    dsimp [J]
    exact inv_ne_zero (pow_ne_zero 2 hc)
  have hf : Measurable (fun z : ℂ => a + c • z) := by fun_prop
  have hmap := complexVolume_map_affine_restrict hc K himage
  have hgm : AEStronglyMeasurable g (Measure.map (fun z : ℂ => a + c • z)
      (volume.restrict K)) := hg.aestronglyMeasurable
  have hint := integral_map hf.aemeasurable hgm
  rw [hmap, integral_smul_measure] at hint
  have hcoef : (ENNReal.ofReal (|(c ^ 2)⁻¹|)).toReal = J := by
    calc
      (ENNReal.ofReal (|(c ^ 2)⁻¹|)).toReal = |(c ^ 2)⁻¹| :=
        ENNReal.toReal_ofReal (abs_nonneg _)
      _ = (c ^ 2)⁻¹ := abs_of_pos (inv_pos.mpr hc2)
      _ = J := rfl
  have hsource : J * (∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) =
      ∫ x, g (a + c • x) ∂volume.restrict K := by
    rw [hcoef, smul_eq_mul] at hint
    exact hint
  have hJabs : J = |(c ^ 2)⁻¹| := by
    dsimp [J]
    exact (abs_of_pos (inv_pos.mpr hc2)).symm
  calc
    (∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) =
        J⁻¹ * (J * ∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) := by
          field_simp [hJ]
    _ = J⁻¹ * ∫ x, g (a + c • x) ∂volume.restrict K := by rw [hsource]
    _ = (|(c ^ 2)⁻¹|)⁻¹ *
        ∫ x, g (a + c • x) ∂volume.restrict K := by rw [hJabs]

end DOZZ.Proofs
