/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Mellin representation of negative powers by the Gamma integral. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- For a positive mass, its negative `q`th power is a normalized Laplace integral. -/
theorem ofReal_rpow_neg_eq_mellin_lintegral
    {m q : ℝ} (hm : 0 < m) (hq : 0 < q) :
    ENNReal.ofReal (m ^ (-q)) = ENNReal.ofReal (1 / Real.Gamma q) *
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m * t))) ∂volume := by
  let F : ℝ → ℝ := fun t => Real.exp (-t) * t ^ (q - 1)
  let G : ℝ → ℝ := fun t => t ^ (q - 1) * Real.exp (-(m * t))
  have hbase : IntegrableOn F (Ioi (0 : ℝ)) volume := Real.GammaIntegral_convergent hq
  have hscaled : IntegrableOn (fun t => F (m * t)) (Ioi (0 : ℝ)) volume := by
    exact (integrableOn_Ioi_comp_mul_left_iff F 0 hm).2 (by simpa using hbase)
  have hEq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      F (m * t) = m ^ (q - 1) * G t := by
    have ht0 : 0 < t := ht
    simp only [F, G, Real.exp_neg]
    rw [Real.mul_rpow hm.le ht0.le]
    ring
  have hc : m ^ (q - 1) ≠ 0 := (Real.rpow_pos_of_pos hm _).ne'
  have hGint : IntegrableOn G (Ioi (0 : ℝ)) volume := by
    have hconst : IntegrableOn (fun t => m ^ (q - 1) • G t)
        (Ioi (0 : ℝ)) volume := by
      exact (integrableOn_congr_fun hEq measurableSet_Ioi).mp hscaled
    change Integrable (fun t => m ^ (q - 1) • G t)
      (volume.restrict (Ioi (0 : ℝ))) at hconst
    exact (integrable_smul_iff hc G).mp hconst
  have hGnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _)
  have hlin : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (G t) ∂volume =
      ENNReal.ofReal ((1 / m) ^ q * Real.Gamma q) := by
    calc
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (G t) ∂volume =
          ENNReal.ofReal (∫ t in Ioi (0 : ℝ), G t ∂volume) :=
            (ofReal_integral_eq_lintegral_ofReal hGint hGnonneg).symm
      _ = ENNReal.ofReal ((1 / m) ^ q * Real.Gamma q) := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hq hm]
  have hpow : m ^ (-q) = (1 / m) ^ q := by
    rw [Real.rpow_def_of_pos hm, one_div, Real.rpow_def_of_pos (inv_pos.mpr hm),
      Real.log_inv]
    congr 1
    ring
  have hgamma : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  calc
    ENNReal.ofReal (m ^ (-q)) =
        ENNReal.ofReal ((1 / Real.Gamma q) * ((1 / m) ^ q * Real.Gamma q)) := by
          congr 1
          rw [hpow]
          field_simp
    _ = ENNReal.ofReal (1 / Real.Gamma q) *
        ENNReal.ofReal ((1 / m) ^ q * Real.Gamma q) := by
          rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (1 / Real.Gamma q) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (G t) ∂volume := by rw [← hlin]


end DOZZ.Proofs
