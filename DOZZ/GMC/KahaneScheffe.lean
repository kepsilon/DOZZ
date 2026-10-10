/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Convergence of nonnegative masses in mean from almost everywhere convergence and convergence
of their expectations. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- Scheffé's argument for nonnegative real masses, on an arbitrary measure space. -/
theorem nonneg_integral_abs_sub_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, Integrable (f n) P) (hg : Integrable g P)
    (hfn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ f n ω) (hgn : ∀ᵐ ω ∂P, 0 ≤ g ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hmean : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, g ω ∂P))) :
    Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂P) atTop (𝓝 0) := by
  have hminInt (n : ℕ) : Integrable (fun ω => min (f n ω) (g ω)) P :=
    hg.mono ((hf n).aemeasurable.min hg.aemeasurable).aestronglyMeasurable (by
      filter_upwards [hfn n, hgn] with ω hfω hgω
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_min hfω hgω),
        abs_of_nonneg hgω]
      exact min_le_right _ _)
  have hmin : Tendsto (fun n => ∫ ω, min (f n ω) (g ω) ∂P) atTop
      (𝓝 (∫ ω, g ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence g
    · intro n
      exact (hminInt n).aestronglyMeasurable
    · exact hg
    · intro n
      filter_upwards [hfn n, hgn] with ω hfω hgω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfω hgω)]
      exact min_le_right _ _
    · filter_upwards [hlim] with ω hω
      simpa using hω.min (tendsto_const_nhds (x := g ω))
  have heq (n : ℕ) : (∫ ω, |f n ω - g ω| ∂P) =
      (∫ ω, f n ω ∂P) + (∫ ω, g ω ∂P) - 2 * (∫ ω, min (f n ω) (g ω) ∂P) := by
    have hid : (fun ω => |f n ω - g ω|) =
        (fun ω => f n ω + g ω - 2 * min (f n ω) (g ω)) := by
      funext ω
      rcases le_total (f n ω) (g ω) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    rw [hid]
    rw [integral_sub (f := fun ω => f n ω + g ω)
      (g := fun ω => 2 * min (f n ω) (g ω))
      ((hf n).add hg) ((hminInt n).const_mul 2),
      integral_add (hf n) hg, integral_const_mul]
  simp_rw [heq]
  convert (hmean.add tendsto_const_nhds).sub (hmin.const_mul 2) using 1; ring_nf

end DOZZ.Proofs
