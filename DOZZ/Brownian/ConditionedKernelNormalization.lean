/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelGaussianIntegrals
public import DOZZ.Statements.Brownian.ConditionedPositiveTransitionDensity

/-!
# Normalization of the explicit conditioned transition kernel

The positive-drift transition density is expanded into four translated Gaussian terms. Pairing
the two terms with opposite shifts gives its total mass by the half-line Gaussian identity.
-/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- Completing the square shifts a heat density by the Gaussian exponential tilt. -/
theorem brownianHeatDensity_tilt {t ν z : ℝ} (ht : 0 < t) :
    Real.exp (ν * z - ν ^ 2 * t / 2) * brownianHeatDensity t z =
      brownianHeatDensity t (z - ν * t) := by
  have he : ν * z - ν ^ 2 * t / 2 - z ^ 2 / (2 * t) =
      -(z - ν * t) ^ 2 / (2 * t) := by
    field_simp [ht.ne']
    ring
  have hden : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp only [brownianHeatDensity, ht, ite_true]
  field_simp [hden]
  rw [← Real.exp_add, Real.exp_injective.eq_iff]
  field_simp [ht.ne']
  ring_nf

private theorem brownianHeatDensity_shift_exp {t ν z : ℝ} (ht : 0 < t) :
    Real.exp (-2 * ν * z) * brownianHeatDensity t (z - ν * t) =
      brownianHeatDensity t (z + ν * t) := by
  have he : -2 * ν * z - (z - ν * t) ^ 2 / (2 * t) =
      -(z + ν * t) ^ 2 / (2 * t) := by
    field_simp [ht.ne']
    ring
  have hden : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp only [brownianHeatDensity, ht, ite_true]
  field_simp [hden]
  rw [← Real.exp_add, Real.exp_injective.eq_iff]
  field_simp [ht.ne']
  ring_nf

private theorem integrable_brownianHeatDensity_translate {t a : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y + a)) (volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun y : ℝ => y + a) :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (brownianHeatDensity t)
      ((volume : Measure ℝ).map (fun y : ℝ => y + a)) := by
    rw [hmap]
    exact integrable_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

/-- For positive drift and positive start, the explicit transition density integrates to one. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_pos
    {ν t x : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y
      ∂(volume : Measure ℝ) = 1 := by
  have hH : conditionedH ν x = 1 - Real.exp (-2 * ν * x) := by
    simp [conditionedH, hν.ne']
  have hexpansion : ∀ y : ℝ, 0 < y →
      conditionedPositiveTransitionDensity ν t x y =
        (brownianHeatDensity t (y - (x + ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
          brownianHeatDensity t (y + (x + ν * t))) /
          conditionedH ν x := by
    intro y hy
    have htilt₁ := brownianHeatDensity_tilt (t := t) (ν := ν) (z := y - x) ht
    have htilt₂ := brownianHeatDensity_tilt (t := t) (ν := ν) (z := y + x) ht
    have hshift₁ := brownianHeatDensity_shift_exp (t := t) (ν := ν) (z := y - x) ht
    have hshift₂ := brownianHeatDensity_shift_exp (t := t) (ν := ν) (z := y + x) ht
    have hfactor₂ : Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
        brownianHeatDensity t (y + x) =
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + x - ν * t) := by
      rw [show ν * (y - x) - ν ^ 2 * t / 2 =
          (-2 * ν * x) + (ν * (y + x) - ν ^ 2 * t / 2) by ring,
        Real.exp_add]
      rw [mul_assoc, htilt₂]
    have hcross₁ : Real.exp (-2 * ν * y) *
        brownianHeatDensity t (y - x - ν * t) =
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y - x + ν * t) := by
      rw [show -2 * ν * y = (-2 * ν * x) + (-2 * ν * (y - x)) by ring,
        Real.exp_add]
      rw [mul_assoc, hshift₁]
    have hcross₂ : Real.exp (-2 * ν * (x + y)) *
        brownianHeatDensity t (y + x - ν * t) =
          brownianHeatDensity t (y + x + ν * t) := by
      simpa only [add_comm x y] using hshift₂
    have htilt₁' : Real.exp (ν * y - ν * x - ν ^ 2 * t / 2) *
        brownianHeatDensity t (y - x) =
          brownianHeatDensity t (y - (x + ν * t)) := by
      calc
        _ = Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
            brownianHeatDensity t (y - x) := by
              rw [show ν * y - ν * x - ν ^ 2 * t / 2 =
                ν * (y - x) - ν ^ 2 * t / 2 by ring]
        _ = brownianHeatDensity t (y - x - ν * t) := htilt₁
        _ = _ := by rw [show y - x - ν * t = y - (x + ν * t) by ring]
    have hfactor₂' : Real.exp (ν * y - ν * x - ν ^ 2 * t / 2) *
        brownianHeatDensity t (y + x) =
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) := by
      calc
        _ = Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
            brownianHeatDensity t (y + x) := by
              rw [show ν * y - ν * x - ν ^ 2 * t / 2 =
                ν * (y - x) - ν ^ 2 * t / 2 by ring]
        _ = Real.exp (-2 * ν * x) * brownianHeatDensity t (y + x - ν * t) := hfactor₂
        _ = _ := by rw [show y + x - ν * t = y + (x - ν * t) by ring]
    have hcross₁' : brownianHeatDensity t (y - x - ν * t) * Real.exp (-2 * ν * y) =
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) := by
      calc
        _ = Real.exp (-2 * ν * y) * brownianHeatDensity t (y - x - ν * t) := mul_comm _ _
        _ = Real.exp (-2 * ν * x) * brownianHeatDensity t (y - x + ν * t) := hcross₁
        _ = _ := by rw [show y - x + ν * t = y - (x - ν * t) by ring]
    have hcross₂' : Real.exp (-2 * ν * x) *
        brownianHeatDensity t (y + x - ν * t) * Real.exp (-2 * ν * y) =
        brownianHeatDensity t (y + x + ν * t) := by
      calc
        _ = (Real.exp (-2 * ν * x) * Real.exp (-2 * ν * y)) *
            brownianHeatDensity t (y + x - ν * t) := by ring
        _ = Real.exp (-2 * ν * x + -2 * ν * y) *
            brownianHeatDensity t (y + x - ν * t) := by rw [← Real.exp_add]
        _ = Real.exp (-2 * ν * (x + y)) * brownianHeatDensity t (y + x - ν * t) := by
          rw [show -2 * ν * x + -2 * ν * y = -2 * ν * (x + y) by ring]
        _ = _ := hcross₂
    have hcrossA : brownianHeatDensity t (y - (x + ν * t)) * Real.exp (-2 * ν * y) =
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) := by
      calc
        _ = brownianHeatDensity t (y - x - ν * t) * Real.exp (-2 * ν * y) := by
          congr 1
          rw [show y - (x + ν * t) = y - x - ν * t by ring]
        _ = Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) := hcross₁'
    have hcrossD : Real.exp (-2 * ν * x) *
        brownianHeatDensity t (y + (x - ν * t)) * Real.exp (-2 * ν * y) =
          brownianHeatDensity t (y + (x + ν * t)) := by
      calc
        _ = Real.exp (-2 * ν * x) * brownianHeatDensity t (y + x - ν * t) *
            Real.exp (-2 * ν * y) := by
          congr 2
          rw [show y + (x - ν * t) = y + x - ν * t by ring]
        _ = brownianHeatDensity t (y + x + ν * t) := hcross₂'
        _ = _ := by rw [show y + x + ν * t = y + (x + ν * t) by ring]
    rw [conditionedPositiveTransitionDensity]
    rw [ite_eq_left (show 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y by exact ⟨hν.le, ht, hx, hy⟩)]
    have hH_y : conditionedH ν y = 1 - Real.exp (-2 * ν * y) := by
      simp [conditionedH, hν.ne']
    rw [hH, hH_y]
    have hnum :
        Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
            (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
            (1 - Real.exp (-2 * ν * y)) =
          brownianHeatDensity t (y - (x + ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) := by
      simp only [mul_sub, sub_mul, mul_one]
      rw [htilt₁', hfactor₂', hcrossA, hcrossD]
      ring
    rw [hnum]
  have hAint : Integrable (fun y : ℝ => brownianHeatDensity t (y - (x + ν * t)))
      (volume : Measure ℝ) := by
    simpa only [sub_eq_add_neg] using
      integrable_brownianHeatDensity_translate (t := t) (a := -(x + ν * t)) ht
  have hBint : Integrable (fun y : ℝ => brownianHeatDensity t (y + (x - ν * t)))
      (volume : Measure ℝ) :=
    integrable_brownianHeatDensity_translate (t := t) (a := x - ν * t) ht
  have hCint : Integrable (fun y : ℝ => brownianHeatDensity t (y - (x - ν * t)))
      (volume : Measure ℝ) := by
    simpa only [sub_eq_add_neg] using
      integrable_brownianHeatDensity_translate (t := t) (a := -(x - ν * t)) ht
  have hDint : Integrable (fun y : ℝ => brownianHeatDensity t (y + (x + ν * t)))
      (volume : Measure ℝ) :=
    integrable_brownianHeatDensity_translate (t := t) (a := x + ν * t) ht
  have hA : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y - (x + ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hAint.integrableOn
  have hB : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + (x - ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hBint.integrableOn
  have hC : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y - (x - ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hCint.integrableOn
  have hD : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + (x + ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hDint.integrableOn
  have hsum :
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x + ν * t)) ∂(volume : Measure ℝ)) +
        ∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ) = 1 :=
    integral_brownianHeatDensity_halfline_pair ht (a := x + ν * t)
  have hsum' :
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x - ν * t)) ∂(volume : Measure ℝ)) +
        ∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x - ν * t)) ∂(volume : Measure ℝ) = 1 :=
    integral_brownianHeatDensity_halfline_pair ht (a := x - ν * t)
  have hB' : IntegrableOn (fun y : ℝ => Real.exp (-2 * ν * x) *
      brownianHeatDensity t (y + (x - ν * t))) (Set.Ioi 0) (volume : Measure ℝ) :=
    hB.const_mul _
  have hC' : IntegrableOn (fun y : ℝ => Real.exp (-2 * ν * x) *
      brownianHeatDensity t (y - (x - ν * t))) (Set.Ioi 0) (volume : Measure ℝ) :=
    hC.const_mul _
  have hsum'' :
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x - ν * t)) ∂(volume : Measure ℝ)) +
        ∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x - ν * t)) ∂(volume : Measure ℝ) = 1 := by
    rw [add_comm]
    exact hsum'
  have hlin :
      (∫ y in Set.Ioi 0, (brownianHeatDensity t (y - (x + ν * t)) -
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
        brownianHeatDensity t (y + (x + ν * t))) ∂(volume : Measure ℝ)) =
        1 - Real.exp (-2 * ν * x) := by
    calc
      _ = ∫ y in Set.Ioi 0,
          (brownianHeatDensity t (y - (x + ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) -
            Real.exp (-2 * ν * x) *
              (brownianHeatDensity t (y + (x - ν * t)) +
                brownianHeatDensity t (y - (x - ν * t)))) ∂(volume : Measure ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          ring
      _ = (∫ y in Set.Ioi 0,
          brownianHeatDensity t (y - (x + ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ)) -
          ∫ y in Set.Ioi 0,
            Real.exp (-2 * ν * x) *
              (brownianHeatDensity t (y + (x - ν * t)) +
                brownianHeatDensity t (y - (x - ν * t))) ∂(volume : Measure ℝ) := by
          exact integral_sub (hA.add hD) ((hB.add hC).const_mul _)
      _ = ((∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x + ν * t)) ∂(volume : Measure ℝ)) +
          ∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ)) -
          Real.exp (-2 * ν * x) *
            ((∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x - ν * t)) ∂(volume : Measure ℝ)) +
              ∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x - ν * t)) ∂(volume : Measure ℝ)) := by
          rw [integral_add hA hD, integral_const_mul, integral_add hB hC]
      _ = 1 - Real.exp (-2 * ν * x) := by rw [hsum, hsum'']; ring
  have hint :
      (∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y
        ∂(volume : Measure ℝ)) =
          (∫ y in Set.Ioi 0,
          (brownianHeatDensity t (y - (x + ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
            brownianHeatDensity t (y + (x + ν * t))) / conditionedH ν x ∂(volume : Measure ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact hexpansion y hy
  have hscale :
      (∫ y in Set.Ioi 0,
        (brownianHeatDensity t (y - (x + ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
          brownianHeatDensity t (y + (x + ν * t))) / conditionedH ν x
        ∂(volume : Measure ℝ)) =
        (∫ y in Set.Ioi 0,
          brownianHeatDensity t (y - (x + ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ)) /
          conditionedH ν x := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
  have hHpos : 0 < conditionedH ν x := by
    rw [hH]
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    have hmul : 0 < 2 * ν * x := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hν) hx
    have harg : -2 * ν * x = -(2 * ν * x) := by ring
    rw [harg]
    exact neg_lt_zero.mpr hmul
  have hHpos' : 0 < 1 - Real.exp (-(2 * ν * x)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    exact neg_lt_zero.mpr (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hν) hx)
  rw [hint, hscale, hlin, hH]
  field_simp [ne_of_gt hHpos']

end DOZZ.Proofs

end
