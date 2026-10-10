/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianHeatDensity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Gaussian heat-kernel normalization identities

These identities reduce half-line Gaussian integrals to the full Gaussian mass by reflection.
They are the scalar integration layer for normalizing the explicit conditioned transition kernels.
-/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- The Brownian heat density is integrable for every positive time. -/
theorem integrable_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    Integrable (brownianHeatDensity t) (volume : Measure ℝ) := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hcoef : 0 < 1 / (2 * t) := by positivity
  have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / (2 * t)) * x ^ 2))
      (volume : Measure ℝ) := integrable_exp_neg_mul_sq hcoef
  have hmul := hbase.mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)
  refine hmul.congr ?_
  filter_upwards [] with x
  change Real.exp (-(1 / (2 * t)) * x ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹ =
    (if 0 < t then Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t)
      else 0)
  rw [ite_eq_left ht, div_eq_mul_inv]
  congr 1
  field_simp [ht.ne', hsqrt.ne']

/-- The heat density has total mass one. -/
theorem integral_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, brownianHeatDensity t x = 1 := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hfun : (fun x : ℝ => brownianHeatDensity t x) =
      (fun x => Real.exp (-(1 / (2 * t)) * x ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹) := by
    funext x
    change (if 0 < t then Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t)
        else 0) = _
    rw [ite_eq_left ht, div_eq_mul_inv]
    congr 1
    field_simp [ht.ne', hsqrt.ne']
  rw [hfun, integral_mul_const]
  rw [integral_gaussian]
  have hroot : Real.sqrt (Real.pi / (1 / (2 * t))) = Real.sqrt (2 * Real.pi * t) := by
    congr 1
    field_simp [ht.ne']
  rw [hroot]
  field_simp [hsqrt.ne']

private theorem volume_map_add_right (a : ℝ) :
    (volume : Measure ℝ).map (fun x : ℝ => x + a) = volume :=
  Measure.IsAddRightInvariant.map_add_right_eq_self a

/-- Translating a heat density does not change its full-line integral. -/
theorem integral_brownianHeatDensity_translate {t a : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, brownianHeatDensity t (x + a) = 1 := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight a).toMeasurableEquiv
  have he : MeasurableEmbedding (fun x : ℝ => x + a) :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  calc
    ∫ x : ℝ, brownianHeatDensity t (x + a) =
        ∫ y : ℝ, brownianHeatDensity t y ∂((volume : Measure ℝ).map e) := by
          symm
          exact he.integral_map (brownianHeatDensity t)
    _ = ∫ y : ℝ, brownianHeatDensity t y := by
          rw [show (volume : Measure ℝ).map e = volume by
            exact volume_map_add_right a]
    _ = 1 := integral_brownianHeatDensity ht

/-- A reflected pair of translates of a normalized even density has total half-line mass one. -/
theorem integral_brownianHeatDensity_halfline_pair {t a : ℝ} (ht : 0 < t) :
    (∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ)) +
      ∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂(volume : Measure ℝ) = 1 := by
  have hshiftInt : Integrable (fun y : ℝ => brownianHeatDensity t (y - a))
      (volume : Measure ℝ) := by
    have he : MeasurableEmbedding (fun y : ℝ => y + -a) :=
      (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + -a) = volume :=
      volume_map_add_right (-a)
    have hmapInt : Integrable (brownianHeatDensity t)
        ((volume : Measure ℝ).map (fun y : ℝ => y + -a)) := by
      rw [hmap]
      exact integrable_brownianHeatDensity ht
    exact he.integrable_map_iff.mp hmapInt
  have hreflect :
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂(volume : Measure ℝ)) =
        ∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ) := by
    calc
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂(volume : Measure ℝ)) =
          ∫ y in Set.Ioi 0, brownianHeatDensity t (-(y + a)) ∂(volume : Measure ℝ) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            simp [brownianHeatDensity, ht]
            congr 1
            field_simp [ht.ne']
            ring_nf
      _ = ∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ) := by
            simpa [sub_eq_add_neg, add_comm] using
              (integral_comp_neg_Ioi (f := fun y : ℝ => brownianHeatDensity t (y - a)) 0)
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (f := fun y : ℝ => brownianHeatDensity t (y - a))
    (s := Set.Iic 0) measurableSet_Iic hshiftInt
  calc
    (∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ)) +
        ∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂(volume : Measure ℝ) =
        (∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ)) +
          ∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ) := by
            rw [hreflect]
    _ = (∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ)) +
          ∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ) := add_comm _ _
    _ = ∫ y : ℝ, brownianHeatDensity t (y - a) := by
          simpa only [compl_Iic] using hsplit
    _ = 1 := by
          simpa [sub_eq_add_neg] using
            integral_brownianHeatDensity_translate (t := t) (a := -a) ht

end DOZZ.Proofs

end
