/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import DOZZ.Statements.FourPoint.FourPointSExp

/-! # Gauss-parameter algebra for the BPZ equation

For `χ = γ/2` or `χ = 2/γ`, the scalar Ward relation among `J`, `E₁`, `D₁`, `D₂` (hypothesis
`hward` of `bpz_gauss_of_ward`) implies the Gauss hypergeometric relation
`W2 + (C - z (A + B + 1)) / (z (1 - z)) W1 - A B / (z (1 - z)) T = 0`, where `A`, `B`, `C` are
the physical Gauss parameters. The argument is pure algebra. After clearing the denominator
`z (1 - z)`, the defect is an explicit combination of the Ward relation and four scalar
identities in `γ`, `χ`, `α₁`, `α₂`, `α₃`: the relation `χ Q = χ² + 1`, which gives `C` and
`A + B + 1` in closed form, the vanishing of `(χ² - γ χ / 2) (1 - γ χ / 2)`, and the
`J`-coefficient identity. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Clearing the common denominator in a three-term combination. -/
theorem bpz_gauss_div_combo {d W2 X W1 Y T : ℂ} (hd : d ≠ 0)
    (h : d * W2 + X * W1 - Y * T = 0) : W2 + X / d * W1 - Y / d * T = 0 := by
  have e : W2 + X / d * W1 - Y / d * T = (d * W2 + X * W1 - Y * T) / d := by
    field_simp
  rw [e, h, zero_div]

/-- The quadratic relation `χ Q = χ² + 1` for both degenerate values of `χ`. -/
theorem bpz_gauss_chi_relation {γ χ : ℝ} (hγ : γ ≠ 0) (hχ : χ = γ / 2 ∨ χ = 2 / γ) :
    χ * Q γ = χ ^ 2 + 1 := by
  rcases hχ with rfl | rfl
  · unfold Q
    field_simp
    ring
  · unfold Q
    field_simp

/-- The `z`-independent Gauss parameter `C` in terms of `χ`. -/
theorem bpz_gauss_C_eq {γ χ α₁ : ℝ} (hQ : χ * Q γ = χ ^ 2 + 1) :
    gaussParameterC γ χ α₁ = χ * (α₁ - χ) := by
  unfold gaussParameterC
  linear_combination (-1 : ℝ) * hQ

/-- The combination `A + B + 1` of Gauss parameters in terms of `χ`. -/
theorem bpz_gauss_sum_eq {γ χ α₁ α₂ α₃ : ℝ} (hQ : χ * Q γ = χ ^ 2 + 1) :
    gaussParameterA γ χ α₁ α₂ α₃ + gaussParameterB γ χ α₁ α₂ α₃ + 1 =
      χ * (α₁ + α₂ - 2 * χ) := by
  unfold gaussParameterA gaussParameterB
  linear_combination (-1 : ℝ) * hQ

/-- The factor identity that kills the `D₁` residual: either `χ = γ / 2` or `γ χ / 2 = 1`. -/
theorem bpz_gauss_factor {γ χ : ℝ} (hγ : γ ≠ 0) (hχ : χ = γ / 2 ∨ χ = 2 / γ) :
    (χ ^ 2 - γ * χ / 2) * (1 - γ * χ / 2) = 0 := by
  rcases hχ with rfl | rfl
  · ring
  · field_simp
    ring

/-- The `J`-coefficient identity `-s χ² ((s + 1) γ² / 4 - c₀) - A B = 0`, where
`s = fourPointSExp γ (-χ) α₁ α₂ α₃` and `c₀ = -1 - γ χ / 2 + γ (α₁ + α₂) / 2`. -/
theorem bpz_gauss_J_coeff {γ χ α₁ α₂ α₃ : ℝ} (hγ : γ ≠ 0) (hχ : χ = γ / 2 ∨ χ = 2 / γ) :
    -(fourPointSExp γ (-χ) α₁ α₂ α₃ * χ ^ 2) *
      ((fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) * (γ ^ 2 / 4) -
        (-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2)) -
      gaussParameterA γ χ α₁ α₂ α₃ * gaussParameterB γ χ α₁ α₂ α₃ = 0 := by
  rcases hχ with rfl | rfl <;>
  · unfold fourPointSExp gaussParameterA gaussParameterB Q
    field_simp
    ring

/-- The Gauss hypergeometric relation from the Ward identity. Multiplying the target by
`z (1 - z)`, the defect equals `-s K χ²` times the Ward relation, plus multiples of the scalar
identities `bpz_gauss_factor`, `bpz_gauss_C_eq`, `bpz_gauss_sum_eq` and `bpz_gauss_J_coeff`. -/
theorem bpz_gauss_of_ward {γ χ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ) (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (K J T : ℝ) (E₁ D₁ D₂ W1 W2 : ℂ)
    (hT : T = K * J)
    (hW1 : W1 = -((fourPointSExp γ (-χ) α₁ α₂ α₃ * K * (γ * χ / 2) : ℝ) : ℂ) * E₁)
    (hW2 : W2 = ((fourPointSExp γ (-χ) α₁ α₂ α₃ * (fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) * K *
        (γ * χ / 2) ^ 2 : ℝ) : ℂ) * D₂ -
      ((fourPointSExp γ (-χ) α₁ α₂ α₃ * K * (γ * χ / 2) * (γ * χ / 2 - 1) : ℝ) : ℂ) * D₁)
    (hward : ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) * (J : ℂ) +
        (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
          ((γ * α₂ / 2 : ℝ) : ℂ) * z) * E₁ +
        ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) * D₁ =
      ((fourPointSExp γ (-χ) α₁ α₂ α₃ + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        ((J : ℂ) - z * (z - 1) * D₂)) :
    W2 + (((gaussParameterC γ χ α₁ : ℝ) : ℂ) - z * (((gaussParameterA γ χ α₁ α₂ α₃ : ℝ) : ℂ) +
        ((gaussParameterB γ χ α₁ α₂ α₃ : ℝ) : ℂ) + 1)) / (z * (1 - z)) * W1 -
      ((gaussParameterA γ χ α₁ α₂ α₃ : ℝ) : ℂ) * ((gaussParameterB γ χ α₁ α₂ α₃ : ℝ) : ℂ) /
        (z * (1 - z)) * (T : ℂ) = 0 := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hd : z * (1 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))
  have hQ := bpz_gauss_chi_relation hγ0 hχ
  have hC := congrArg (fun x : ℝ => (x : ℂ)) (bpz_gauss_C_eq (α₁ := α₁) hQ)
  have hAB := congrArg (fun x : ℝ => (x : ℂ)) (bpz_gauss_sum_eq (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) hQ)
  have hF := congrArg (fun x : ℝ => (x : ℂ)) (bpz_gauss_factor hγ0 hχ)
  have hJ := congrArg (fun x : ℝ => (x : ℂ)) (bpz_gauss_J_coeff (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) hγ0 hχ)
  push_cast at hC hAB hF hJ
  refine bpz_gauss_div_combo hd ?_
  subst hT hW1 hW2
  push_cast at hward ⊢
  linear_combination (-(↑(fourPointSExp γ (-χ) α₁ α₂ α₃) * (K : ℂ) * (χ : ℂ) ^ 2)) * hward +
    (↑(fourPointSExp γ (-χ) α₁ α₂ α₃) * (K : ℂ) * (z * (z - 1)) * D₁) * hF +
    (↑(fourPointSExp γ (-χ) α₁ α₂ α₃) * (K : ℂ) * E₁ * (-((γ : ℂ) * χ / 2))) * hC +
    (↑(fourPointSExp γ (-χ) α₁ α₂ α₃) * (K : ℂ) * E₁ * ((γ : ℂ) * χ / 2) * z) * hAB +
    ((K : ℂ) * J) * hJ

end DOZZ.Proofs
