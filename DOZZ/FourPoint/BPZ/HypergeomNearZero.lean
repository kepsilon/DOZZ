/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
public import DOZZ.Statements.Hypergeom.GaussFMinus
public import DOZZ.Statements.Hypergeom.GaussFPlus
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Hypergeometric basis functions near the origin

Elementary properties of a Gauss hypergeometric family `H` that are used when the two zero-basis
functions `F₋ = H a b c` and `F₊ = z ^ (1 - c) * H (a - c + 1) (b - c + 1) (2 - c)` are evaluated
on the real axis near `0`.

* `bpzHG_eq_one_at_zero`: `H a b c 0 = 1`, since `H a b c` agrees with the series on the unit disc.
* `bpzHG_contDiffOn_normSq`: `u ↦ ‖H a b c u‖²` is smooth on the real interval `(-1, 1)`, because
  `H a b c` is holomorphic on the open slit plane, which contains this interval.
* `bpzHG_normSq_gaussFPlus`, `bpzHG_normSq_gaussFMinus`: the squared moduli of `F₊` and `F₋` at
  real points, the former with the real power `u ^ (2 * (1 - c))` for `u > 0`.
* `bpzHG_norm_sq_eq_normSq`: the `‖·‖ ^ 2` form of `Complex.normSq`, as used in the statements. -/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- The hypergeometric function is `1` at the origin. -/
theorem bpzHG_eq_one_at_zero {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {a b c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) : H a b c 0 = 1 := by
  rw [(hH a b c hc).2 0 (by simp)]
  exact ordinaryHypergeometric_zero a b c

/-- The slit plane `ℂ \ [1, ∞)` is open. -/
theorem bpzHG_isOpen_gaussSlitPlane : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z : ℂ | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

/-- The real interval `(-1, 1)` lies in the slit plane. -/
theorem bpzHG_mapsTo_ofReal_gaussSlitPlane :
    Set.MapsTo (fun u : ℝ => (u : ℂ)) (Set.Ioo (-1) 1) gaussSlitPlane := fun u hu =>
  Or.inr (by simpa using hu.2)

/-- On the real interval `(-1, 1)`, `u ↦ ‖H a b c u‖²` is smooth. -/
theorem bpzHG_contDiffOn_normSq {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {a b c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ContDiffOn ℝ 2 (fun u : ℝ => Complex.normSq (H a b c (u : ℂ))) (Set.Ioo (-1) 1) := by
  have hC : ContDiffOn ℂ 2 (H a b c) gaussSlitPlane :=
    (hH a b c hc).1.contDiffOn bpzHG_isOpen_gaussSlitPlane
  have hR : ContDiffOn ℝ 2 (fun u : ℝ => H a b c (u : ℂ)) (Set.Ioo (-1) 1) :=
    (hC.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff.contDiffOn
      bpzHG_mapsTo_ofReal_gaussSlitPlane
  simpa only [Complex.normSq_eq_norm_sq] using hR.norm_sq ℂ

/-- The norm square of `F₊` at a positive real point. -/
theorem bpzHG_normSq_gaussFPlus (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c : ℝ) {u : ℝ} (hu : 0 < u) :
    Complex.normSq (gaussFPlus H a b c (u : ℂ)) =
      u ^ (2 * (1 - c)) *
        Complex.normSq (H ((a : ℂ) - c + 1) ((b : ℂ) - c + 1) (2 - (c : ℂ)) (u : ℂ)) := by
  unfold gaussFPlus
  rw [map_mul]
  congr 1
  have h1 : (u : ℂ) ^ ((1 : ℂ) - (c : ℂ)) = ((u ^ (1 - c) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_cpow hu.le (1 - c)).symm
  rw [h1, Complex.normSq_ofReal, ← Real.rpow_add hu]
  ring_nf

/-- The norm square of `F₋` is `‖H a b c u‖²`. -/
theorem bpzHG_normSq_gaussFMinus (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c : ℝ) (u : ℝ) :
    Complex.normSq (gaussFMinus H a b c (u : ℂ)) = Complex.normSq (H a b c (u : ℂ)) :=
  rfl

/-- `‖x‖ ^ 2 = Complex.normSq x`, restated for the `‖·‖ ^ 2` form used in the statements. -/
theorem bpzHG_norm_sq_eq_normSq (w : ℂ) : ‖w‖ ^ 2 = Complex.normSq w :=
  (Complex.normSq_eq_norm_sq w).symm

end DOZZ.Proofs
