/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.Complex
import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.Complex.Basic

/-!
# Meromorphic germs for the gluing identities

The shift coefficient `z ↦ 𝒜(χ, z, α₂, α₃)` is meromorphic on `ℂ`; real translations and the
reflection `z ↦ c - z` preserve horizontal strips and meromorphy. Identities between such germs
that hold frequently near one point of a strip hold near every point of it.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- **The shift coefficient is meromorphic in its first charge.** -/
theorem meromorphic_shiftCoeffA (γ : ℝ) (χ α₂ α₃ : ℂ) :
    Meromorphic (fun z => shiftCoeffA γ χ z α₂ α₃) := by
  intro x
  unfold shiftCoeffA
  have h1 : MeromorphicAt (fun _ : ℂ => lFun (-χ ^ 2)) x := MeromorphicAt.const _ _
  have h2 := meromorphicAt_lFun_comp (f := fun z : ℂ => χ * z) (z := x) (by fun_prop)
  have h3 := meromorphicAt_lFun_comp (f := fun z : ℂ => χ * z - χ ^ 2) (z := x) (by fun_prop)
  have h4 := meromorphicAt_lFun_comp (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - 2 * z - χ))
    (z := x) (by fun_prop)
  have h5 := meromorphicAt_lFun_comp
    (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - χ - 2 * Q γ)) (z := x) (by fun_prop)
  have h6 := meromorphicAt_lFun_comp
    (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - 2 * α₃ - χ)) (z := x) (by fun_prop)
  have h7 := meromorphicAt_lFun_comp
    (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - 2 * α₂ - χ)) (z := x) (by fun_prop)
  exact (((h1.mul h2).mul h3).mul h4).div ((h5.mul h6).mul h7)

/-- Real translations preserve horizontal strips. -/
theorem add_ofReal_mem_horizontalStrip_glue {h : ℝ} {z : ℂ} (hz : z ∈ horizontalStrip h) (t : ℝ) :
    z + (t : ℂ) ∈ horizontalStrip h := by
  have hz' : |z.im| < h := hz
  change |(z + (t : ℂ)).im| < h
  simpa using hz'

/-- Reflections across real points preserve horizontal strips. -/
theorem ofReal_sub_mem_horizontalStrip_glue {h : ℝ} {z : ℂ} (hz : z ∈ horizontalStrip h) (t : ℝ) :
    (t : ℂ) - z ∈ horizontalStrip h := by
  have hz' : |z.im| < h := hz
  change |((t : ℂ) - z).im| < h
  simpa [abs_neg] using hz'

/-- Meromorphy is preserved by a real translation of the variable. -/
theorem MeromorphicOn.comp_add_ofReal {f : ℂ → ℂ} {h : ℝ} (hf : MeromorphicOn f (horizontalStrip h))
    (t : ℝ) : MeromorphicOn (fun z => f (z + t)) (horizontalStrip h) := fun z hz =>
  (hf _ (add_ofReal_mem_horizontalStrip_glue hz t)).comp_analyticAt (g := fun w => w + (t : ℂ))
    (by fun_prop)

/-- Meromorphy is preserved by a reflection of the variable across a real point. -/
theorem MeromorphicOn.comp_ofReal_sub {f : ℂ → ℂ} {h : ℝ} (hf : MeromorphicOn f (horizontalStrip h))
    (t : ℝ) : MeromorphicOn (fun z => f ((t : ℂ) - z)) (horizontalStrip h) := fun z hz =>
  (hf _ (ofReal_sub_mem_horizontalStrip_glue hz t)).comp_analyticAt (g := fun w => (t : ℂ) - w)
    (by fun_prop)

/-- Horizontal strips are preconnected. -/
theorem isPreconnected_horizontalStrip (h : ℝ) : IsPreconnected (horizontalStrip h) := by
  have hconv : Convex ℝ (horizontalStrip h) := by
    intro x hx y hy a b ha hb hab
    change |(a • x + b • y).im| < h
    have hx' : |x.im| < h := hx
    have hy' : |y.im| < h := hy
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < a * h + b * h := by
          rcases ha.lt_or_eq with ha' | ha'
          · nlinarith [mul_le_mul_of_nonneg_left hy'.le hb]
          · subst ha'
            simp only [zero_add, zero_mul] at hab ⊢
            rw [hab]
            linarith
      _ = h := by rw [← add_mul, hab, one_mul]
  exact hconv.isPreconnected

end DOZZ.Proofs

end
