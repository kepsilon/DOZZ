/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.Hypergeom.PlanarMixedKernel
public import DOZZ.Hypergeom.Planar.DerivativeIntegrable
public import DOZZ.Hypergeom.Planar.RieszConvolution

/-! Normalize the Riesz convolution constant to the planar constant `DOZZ.planarGaussConstant`. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

private theorem lFun_real_argument (x : ℝ) :
    DOZZ.lFun (x : ℝ) =
      ((Real.Gamma x / Real.Gamma (1 - x) : ℝ) : ℂ) := by
  change Complex.Gamma (x : ℂ) / Complex.Gamma (1 - (x : ℂ)) = _
  have harg : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    norm_cast
  rw [harg, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div]

/-- The Riesz convolution coefficient, after the mixed derivative, is the constant
`planarGaussConstant` (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem positive_riesz_coefficient_eq_planarGaussConstant (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    ((
      ((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
        (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
          Real.Gamma ((β - k) / 2) /
            (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
              Real.Gamma (1 + (k - β) / 2)))
      : ℝ) : ℂ) =
      DOZZ.planarGaussConstant k β := by
  have hA := lFun_real_argument (β / 2)
  have hB := lFun_real_argument (-k / 2)
  have hC := lFun_real_argument (2 - β / 2 + k / 2)
  rw [DOZZ.planarGaussConstant, hA, hB, hC]
  norm_cast
  have hb : 0 < k / 2 := by linarith
  have hd : 0 < (β - k) / 2 := by linarith
  have hq : 0 < (2 + k - β) / 2 := by linarith
  have hb₁ : 0 < 1 - k / 2 := by linarith
  have ha : 0 < β / 2 := by linarith
  have ha₁ : 0 < 1 - β / 2 := by linarith
  have hgB : Real.Gamma (1 + k / 2) = (k / 2) * Real.Gamma (k / 2) := by
    rw [show 1 + k / 2 = k / 2 + 1 by ring]
    exact Real.Gamma_add_one hb.ne'
  have hgNegB : Real.Gamma (1 - k / 2) = (-k / 2) * Real.Gamma (-k / 2) := by
    have h := Real.Gamma_add_one (by linarith : -k / 2 ≠ 0)
    convert h using 1
    ring_nf
  have hgNegB' : Real.Gamma (-k / 2) =
      Real.Gamma (1 - k / 2) / (-k / 2) := by
    calc
      Real.Gamma (-k / 2) = ((-k / 2) * Real.Gamma (-k / 2)) / (-k / 2) := by
        field_simp [ne_of_gt hb]
      _ = Real.Gamma (1 - k / 2) / (-k / 2) := by rw [← hgNegB]
  have hgQ : Real.Gamma (1 + (2 + k - β) / 2) =
      ((2 + k - β) / 2) * Real.Gamma ((2 + k - β) / 2) := by
    rw [show 1 + (2 + k - β) / 2 = (2 + k - β) / 2 + 1 by ring]
    exact Real.Gamma_add_one hq.ne'
  have hgNegQ : Real.Gamma ((β - k) / 2) =
      (-((2 + k - β) / 2)) * Real.Gamma (-((2 + k - β) / 2)) := by
    have h := Real.Gamma_add_one (by linarith : -((2 + k - β) / 2) ≠ 0)
    convert h using 1
    ring_nf
  have hgNegQ' : Real.Gamma (-((2 + k - β) / 2)) =
      Real.Gamma ((β - k) / 2) / (-((2 + k - β) / 2)) := by
    calc
      Real.Gamma (-((2 + k - β) / 2)) =
          ((-((2 + k - β) / 2)) * Real.Gamma (-((2 + k - β) / 2))) /
            (-((2 + k - β) / 2)) := by
        field_simp [ne_of_gt (show 0 < 2 + k - β by linarith)]
      _ = Real.Gamma ((β - k) / 2) / (-((2 + k - β) / 2)) := by rw [← hgNegQ]
  rw [show 1 - (2 - β / 2 + k / 2) = -((2 + k - β) / 2) by ring,
    show 1 + (k - β) / 2 = (2 + k - β) / 2 by ring,
    show 2 - β / 2 + k / 2 = 1 + (2 + k - β) / 2 by ring,
    show 1 - -k / 2 = 1 + k / 2 by ring,
    hgB, hgNegB', hgQ, hgNegQ']
  field_simp [
    ne_of_gt (Real.Gamma_pos_of_pos ha),
    ne_of_gt (Real.Gamma_pos_of_pos ha₁),
    ne_of_gt (Real.Gamma_pos_of_pos hb),
    ne_of_gt (Real.Gamma_pos_of_pos hb₁),
    ne_of_gt (Real.Gamma_pos_of_pos hd),
    ne_of_gt (Real.Gamma_pos_of_pos hq)]

/-- The mixed-kernel integral is the positive Riesz convolution, with its constant normalized to the
coefficient `planarGaussConstant` (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem planar_mixed_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, z ≠ 0 → Integrable (DOZZ.planarMixedKernel k β z) volume ∧
      (((k / 2) ^ 2 * (∫ u : ℂ, DOZZ.planarMixedKernel k β z u)) : ℝ) =
        (((2 + k - β) / 2) ^ 2 * ‖z‖ ^ (k - β) : ℝ) *
          DOZZ.planarGaussConstant k β := by
  intro z hz
  have hInt := positive_riesz_convolution_integrable k β hk hβ hβ₂ z hz
  have heq : (fun u : ℂ => DOZZ.planarMixedKernel k β z u) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with u hu
    change ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β = _
    rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
    ring
  have hkernelInt : Integrable (DOZZ.planarMixedKernel k β z) volume := by
    rw [integrable_congr heq]
    exact hInt
  have hRiesz := positive_riesz_convolution_integral k β hk hβ hβ₂ z hz
  have hconv : (∫ u : ℂ, DOZZ.planarMixedKernel k β z u) =
      Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β) := by
    calc
      _ = ∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := integral_congr_ae heq
      _ = _ := hRiesz
  let q : ℝ := (2 + k - β) / 2
  let C : ℝ := Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
    Real.Gamma ((β - k) / 2) /
      (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
        Real.Gamma (1 + (k - β) / 2)))
  let N : ℝ := ‖z‖ ^ (k - β)
  have hq : 0 < q := by dsimp [q]; linarith
  have hC : (((k / 2) ^ 2 / q ^ 2 * C : ℝ) : ℂ) = DOZZ.planarGaussConstant k β := by
    calc
      _ = ((((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
          (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
            Real.Gamma ((β - k) / 2) /
              (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
                Real.Gamma (1 + (k - β) / 2))) : ℝ) : ℂ) := by
            apply congrArg Complex.ofReal
            dsimp [q, C]
            ring
      _ = DOZZ.planarGaussConstant k β :=
            positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂
  have halg : (k / 2) ^ 2 * C * N = (q ^ 2 * N) * ((k / 2) ^ 2 / q ^ 2 * C) := by
    field_simp [ne_of_gt hq]
  refine ⟨hkernelInt, ?_⟩
  change Complex.ofReal ((k / 2) ^ 2 * (∫ u : ℂ, DOZZ.planarMixedKernel k β z u)) =
    Complex.ofReal (q ^ 2 * N) * DOZZ.planarGaussConstant k β
  calc
    _ = Complex.ofReal ((k / 2) ^ 2 * C * N) := by
      rw [hconv]
      exact congrArg Complex.ofReal (by dsimp [C, N]; ring)
    _ = ((q ^ 2 * N : ℝ) : ℂ) * ((k / 2) ^ 2 / q ^ 2 * C : ℝ) := by
      rw [← Complex.ofReal_mul]
      exact congrArg Complex.ofReal halg
    _ = _ := by rw [hC]

end DOZZ.Proofs
