/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.DifferenceScale
public import DOZZ.Hypergeom.Planar.TaylorDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.RieszConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A dominated discrete-Laplacian limit for the difference parent integral. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The four-direction discrete Laplacian of the first-order-subtracted difference kernel. -/
noncomputable def planarDifferenceDiscreteQuotient (k β : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  (DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
    DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u +
    DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u +
    DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u -
    4 * DOZZ.planarDifferenceKernel k β 1 u) / t ^ 2

private theorem integrable_planarDifferenceDiscreteNumerator (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) (t : ℝ) :
    Integrable (fun u : ℂ =>
      DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
        DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u +
        DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u +
        DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u -
        4 * DOZZ.planarDifferenceKernel k β 1 u) volume := by
  have h₁ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 + (t : ℂ))
  have h₂ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 - (t : ℂ))
  have h₃ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail
    (1 + (t : ℂ) * Complex.I)
  have h₄ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail
    (1 - (t : ℝ) * Complex.I)
  have h₀ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail 1
  exact (((h₁.add h₂).add h₃).add h₄).sub (h₀.const_mul 4)

/-- The difference discrete quotient is integrable at every step, including the totalized zero step. -/
theorem integrable_planarDifferenceDiscreteQuotient (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) (t : ℝ) :
    Integrable (planarDifferenceDiscreteQuotient k β t) volume := by
  have hN := integrable_planarDifferenceDiscreteNumerator k β hk hβ hβ₂ hβtail t
  change Integrable (fun u : ℂ =>
    (DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
      DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u +
      DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u +
      DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u -
      4 * DOZZ.planarDifferenceKernel k β 1 u) / t ^ 2)
  simpa [div_eq_mul_inv, mul_comm] using hN.const_mul ((t ^ 2)⁻¹)

/-- Integrating the difference quotient gives the corresponding quotient of parent integrals. -/
theorem integral_planarDifferenceDiscreteQuotient (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) (t : ℝ) :
    (∫ u : ℂ, planarDifferenceDiscreteQuotient k β t u) =
      ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u)) / t ^ 2 := by
  have h₁ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 + (t : ℂ))
  have h₂ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 - (t : ℂ))
  have h₃ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail
    (1 + (t : ℂ) * Complex.I)
  have h₄ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail
    (1 - (t : ℝ) * Complex.I)
  have h₀ := integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail 1
  let f₁ : ℂ → ℝ := DOZZ.planarDifferenceKernel k β (1 + (t : ℂ))
  let f₂ : ℂ → ℝ := DOZZ.planarDifferenceKernel k β (1 - (t : ℂ))
  let f₃ : ℂ → ℝ := DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I)
  let f₄ : ℂ → ℝ := DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I)
  let f₀ : ℂ → ℝ := DOZZ.planarDifferenceKernel k β 1
  have hf₁ : Integrable f₁ volume := by simpa [f₁] using h₁
  have hf₂ : Integrable f₂ volume := by simpa [f₂] using h₂
  have hf₃ : Integrable f₃ volume := by simpa [f₃] using h₃
  have hf₄ : Integrable f₄ volume := by simpa [f₄] using h₄
  have hf₀ : Integrable f₀ volume := by simpa [f₀] using h₀
  let N : ℂ → ℝ := fun u => f₁ u + f₂ u + f₃ u + f₄ u - 4 * f₀ u
  have hN : Integrable N volume := integrable_planarDifferenceDiscreteNumerator
    k β hk hβ hβ₂ hβtail t
  have hsum : (∫ u : ℂ, N u) =
      (∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u) + (∫ u : ℂ, f₃ u) +
        (∫ u : ℂ, f₄ u) - 4 * (∫ u : ℂ, f₀ u) := by
    have h₁₂ : (∫ u : ℂ, f₁ u + f₂ u) =
        (∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u) := integral_add hf₁ hf₂
    have h₁₂₃ : (∫ u : ℂ, (f₁ u + f₂ u) + f₃ u) =
        ((∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u)) + (∫ u : ℂ, f₃ u) := by
      calc
        _ = (∫ u : ℂ, f₁ u + f₂ u) + (∫ u : ℂ, f₃ u) := by
          simpa only [Pi.add_apply] using integral_add (hf₁.add hf₂) hf₃
        _ = _ := by rw [h₁₂]
    have h₁₂₃₄ : (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) =
        (((∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u)) + (∫ u : ℂ, f₃ u)) +
          (∫ u : ℂ, f₄ u) := by
      calc
        _ = (∫ u : ℂ, (f₁ u + f₂ u) + f₃ u) + (∫ u : ℂ, f₄ u) := by
          simpa only [Pi.add_apply] using integral_add ((hf₁.add hf₂).add hf₃) hf₄
        _ = _ := by rw [h₁₂₃]
    calc
      (∫ u : ℂ, N u) =
          (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u - 4 * f₀ u) := by
            apply congrArg (fun f : ℂ → ℝ => ∫ u : ℂ, f u)
            funext u
            dsimp [N]
      _ = (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) -
          (∫ u : ℂ, 4 * f₀ u) := integral_sub
            (((hf₁.add hf₂).add hf₃).add hf₄) (hf₀.const_mul 4)
      _ = _ := by rw [h₁₂₃₄, integral_const_mul]
  have hQ : (fun u : ℂ => planarDifferenceDiscreteQuotient k β t u) =
      fun u => (t ^ 2)⁻¹ * N u := by
    funext u
    simp [planarDifferenceDiscreteQuotient, N, f₁, f₂, f₃, f₄, f₀,
      div_eq_mul_inv, mul_comm]
  rw [hQ, integral_const_mul, hsum]
  simp only [div_eq_mul_inv]
  ring

/-- The difference quotient is the positive radial Laplacian kernel after cancellation. -/
theorem planarDifferenceDiscreteQuotient_eq_kernel (k β : ℝ) (t : ℝ) (ht : t ≠ 0)
    (u : ℂ) :
    planarDifferenceDiscreteQuotient k β t u =
      ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
  have hnum :
      DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
        DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u +
        DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u +
        DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u -
        4 * DOZZ.planarDifferenceKernel k β 1 u =
      (‖u - (1 + (t : ℂ))‖ ^ k + ‖u - (1 - (t : ℂ))‖ ^ k +
        ‖u - (1 + (t : ℂ) * Complex.I)‖ ^ k +
        ‖u - (1 - (t : ℝ) * Complex.I)‖ ^ k - 4 * ‖u - 1‖ ^ k) /
        ‖u‖ ^ β := by
    simp only [DOZZ.planarDifferenceKernel]
    ring
  have h₁ : u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) := by ring
  have h₂ : u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) := by ring
  have h₃ : u - (1 + (t : ℂ) * Complex.I) = (u - 1) - (t : ℂ) * Complex.I := by ring
  have h₄ : u - (1 - (t : ℝ) * Complex.I) = (u - 1) + (t : ℝ) * Complex.I := by ring
  rw [planarDifferenceDiscreteQuotient, hnum, h₁, h₂, h₃, h₄]
  rw [Real.rpow_neg (norm_nonneg u)]
  simp only [normPowerDiscreteLaplacian]
  field_simp [show t ^ 2 ≠ 0 by exact pow_ne_zero 2 ht]
  ring

/-- The first-subtraction quotient coincides with the corrected Taylor quotient after the
counterterm cancels under the four-direction Laplacian. -/
theorem planarDifferenceDiscreteQuotient_eq_taylor (k β : ℝ) (t : ℝ) (ht : t ≠ 0)
    (u : ℂ) :
    planarDifferenceDiscreteQuotient k β t u = planarTaylorDiscreteQuotient k β t u := by
  rw [planarDifferenceDiscreteQuotient_eq_kernel k β t ht,
    planarTaylorDiscreteQuotient_eq_kernel]

/-- The pointwise limit of the difference-parent quotient is the positive Riesz kernel. -/
theorem planarDifferenceDiscreteQuotient_tendsto (k β : ℝ) (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarDifferenceDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  have htEvent : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht
  have hEq : (fun t : ℝ => planarDifferenceDiscreteQuotient k β t u) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => planarTaylorDiscreteQuotient k β t u := by
    filter_upwards [htEvent] with t ht
    exact planarDifferenceDiscreteQuotient_eq_taylor k β t ht u
  exact (planarTaylorDiscreteQuotient_tendsto k β u hu).congr' hEq.symm

/-- Dominated convergence identifies the limiting integral with the positive Riesz convolution. -/
theorem planarDifferenceDiscreteQuotient_integral_tendsto (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarDifferenceDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  let K : ℝ := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) + 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => K * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  have hK : 0 ≤ K := by
    dsimp [K]
    have hk₂ : 0 < 1 - k / 2 := by linarith [hβ, hβ₂]
    positivity
  have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
  have hboundInt : Integrable bound volume := by
    simpa [bound, K, mul_assoc] using hRiesz.const_mul K
  have hmeas : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (planarDifferenceDiscreteQuotient k β t) volume := by
    filter_upwards [] with t
    exact (integrable_planarDifferenceDiscreteQuotient k β hk hβ hβ₂ hβtail t).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarDifferenceDiscreteQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    rw [planarDifferenceDiscreteQuotient_eq_taylor k β t ht0 u]
    simpa [bound, K] using
      planarTaylorDiscreteQuotient_norm_le k β hk hβ hβ₂ u t hu ht0
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun t : ℝ => planarDifferenceDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    exact planarDifferenceDiscreteQuotient_tendsto k β u hu
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    hmeas hbound hboundInt hlim

end DOZZ.Proofs
