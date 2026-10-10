/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
public import DOZZ.Hypergeom.Planar.DifferenceDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.TaylorNormalization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The KRV difference integral follows from scaling and its Riesz discrete Laplacian. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The coefficient of the first-subtracted parent, recovered from its dominated discrete
Laplacian. -/
theorem planarDifference_constant_from_discrete_laplacian (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) :
    ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u : ℝ) : ℂ) =
      DOZZ.planarGaussConstant k β := by
  let α : ℝ := 2 + k - β
  let A : ℝ := ∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u
  let l : Filter ℝ := 𝓝[≠] (0 : ℝ)
  let P : ℝ → ℝ := fun t =>
    ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u) +
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u) +
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u) +
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u) -
      4 * A) / t ^ 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hscale (z : ℂ) :
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) = ‖z‖ ^ α * A := by
    simpa [α, A] using
      planarDifferenceKernel_integral_scale_norm k β hk hβ hβ₂ z
  have hParentEq : P =ᶠ[l]
      fun t => A * normPowerDiscreteLaplacian α t 1 := by
    filter_upwards [] with t
    have h₁ := hscale (1 + (t : ℂ))
    have h₂ := hscale (1 - (t : ℂ))
    have h₃ := hscale (1 + (t : ℂ) * Complex.I)
    have h₄ := hscale (1 - (t : ℝ) * Complex.I)
    change ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u) +
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u) +
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u) +
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u) -
      4 * A) / t ^ 2 = _
    rw [h₁, h₂, h₃, h₄]
    simp only [normPowerDiscreteLaplacian, norm_one, Real.one_rpow]
    ring
  have hRad := norm_rpow_discrete_laplacian_tendsto α 1 (by norm_num)
  have hScaled : Tendsto (fun t : ℝ => A * normPowerDiscreteLaplacian α t 1) l
      (𝓝 (A * (α ^ 2 * ‖(1 : ℂ)‖ ^ (α - 2)))) :=
    tendsto_const_nhds.mul hRad
  have hParentLimit : Tendsto P l (𝓝 (α ^ 2 * A)) := by
    have h := hScaled.congr' hParentEq.symm
    simpa [norm_one, Real.one_rpow, mul_assoc, mul_left_comm, mul_comm] using h
  have hDct := planarDifferenceDiscreteQuotient_integral_tendsto
    k β hk hβ hβ₂ hβtail
  have hQEq :
      (fun t : ℝ => ∫ u : ℂ, planarDifferenceDiscreteQuotient k β t u) =ᶠ[l] P := by
    filter_upwards [] with t
    simpa [P, A] using
      integral_planarDifferenceDiscreteQuotient k β hk hβ hβ₂ hβtail t
  have hDctP := hDct.congr' hQEq
  have hDctP' : Tendsto P l
      (𝓝 (k ^ 2 * (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
    simpa only [MeasureTheory.integral_const_mul] using hDctP
  have hCoeff := tendsto_nhds_unique hDctP' hParentLimit
  have hRiesz := positive_riesz_convolution_integral k β hk hβ hβ₂ 1 (by norm_num)
  let G : ℝ := Real.pi *
    (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) * Real.Gamma ((β - k) / 2) /
      (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
        Real.Gamma (1 + (k - β) / 2)))
  have hRieszVal :
      (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) = G := by
    simpa [G, norm_one, Real.one_rpow] using hRiesz
  have hRealCoeff : k ^ 2 * G = α ^ 2 * A := by
    simpa [hRieszVal] using hCoeff
  have hαsq : α ^ 2 ≠ 0 := pow_ne_zero 2 hα.ne'
  have hA : A = (k ^ 2 / α ^ 2) * G := by
    calc
      A = α ^ 2 * A / α ^ 2 := by field_simp [hαsq]
      _ = k ^ 2 * G / α ^ 2 := by rw [hRealCoeff]
      _ = (k ^ 2 / α ^ 2) * G := by ring
  have hratio : k ^ 2 / α ^ 2 = (k / 2) ^ 2 / (α / 2) ^ 2 := by
    field_simp [hαsq]
  have hconst := positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂
  calc
    (A : ℂ) = (((k ^ 2 / α ^ 2) * G : ℝ) : ℂ) := congrArg Complex.ofReal hA
    _ = ((((k / 2) ^ 2 / (α / 2) ^ 2) * G : ℝ) : ℂ) := by rw [hratio]
    _ = DOZZ.planarGaussConstant k β := by
      dsimp [G, α]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hconst

/-- Proof of the difference-integral statement `DOZZ.planar_difference_integral`. -/
theorem planar_difference_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k + 1 < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, Integrable (DOZZ.planarDifferenceKernel k β z) volume ∧
      ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) : ℂ) =
        (‖z‖ ^ (2 + k - β) : ℝ) * DOZZ.planarGaussConstant k β := by
  have hInt := integrable_planarDifferenceKernel k β hk (by linarith) hβ₂ hβ
  have hA := planarDifference_constant_from_discrete_laplacian k β hk (by linarith) hβ₂ hβ
  have hscale := planarDifferenceKernel_integral_scale_norm k β hk (by linarith) hβ₂
  intro z
  refine ⟨hInt z, ?_⟩
  have hval : (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
      ‖z‖ ^ (2 + k - β) *
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := hscale z
  rw [integral_complex_ofReal]
  calc
    ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u : ℝ) : ℂ) =
        ((‖z‖ ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) : ℝ) : ℂ) :=
            congrArg Complex.ofReal hval
    _ = Complex.ofReal (‖z‖ ^ (2 + k - β)) *
        Complex.ofReal (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
          rw [Complex.ofReal_mul]
    _ = Complex.ofReal (‖z‖ ^ (2 + k - β)) * DOZZ.planarGaussConstant k β := by rw [hA]

end DOZZ.Proofs
