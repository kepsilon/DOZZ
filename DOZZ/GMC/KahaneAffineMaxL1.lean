/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneFiniteAffineMax

/-! Affine maxima preserve convergence in mean. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- A maximum of finitely many affine functions has a global Lipschitz bound. -/
theorem affineMax_abs_sub_le
    {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      |affineMax a b x - affineMax a b y| ≤ C * |x - y| := by
  classical
  let C := ∑ i : κ, |a i|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha (i : κ) : |a i| ≤ C :=
    Finset.single_le_sum (f := fun j => |a j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hbound (x y : ℝ) : affineMax a b x ≤ affineMax a b y + C * |x - y| := by
    apply Finset.sup'_le
    intro i hi
    have hline := affineMax_le a b y i
    have hdiff : a i * (x - y) ≤ C * |x - y| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _))
    linarith only [hline, hdiff]
  refine ⟨C, hC, fun x y => ?_⟩
  rw [abs_le]
  have hxy := hbound x y
  have hyx := hbound y x
  rw [abs_sub_comm y x] at hyx
  constructor <;> linarith only [hxy, hyx]

/-- Convergence in mean of real masses implies convergence of affine-max expectations. -/
theorem affineMax_integral_tendsto_of_L1
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [Nonempty κ]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, Integrable (f n) P) (hg : Integrable g P)
    (hL1 : Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂P) atTop (𝓝 0))
    (a b : κ → ℝ) :
    Tendsto (fun n => ∫ ω, affineMax a b (f n ω) ∂P) atTop
      (𝓝 (∫ ω, affineMax a b (g ω) ∂P)) := by
  obtain ⟨C, hC, hbound⟩ := affineMax_abs_sub_le a b
  have hI (n : ℕ) := affineMax_comp_integrable P (f n) (hf n) a b
  have hJ := affineMax_comp_integrable P g hg a b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hL1.const_mul C)
  rw [← integral_sub (hI n) hJ]
  calc
    _ ≤ ∫ ω, ‖affineMax a b (f n ω) - affineMax a b (g ω)‖ ∂P :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, C * |f n ω - g ω| ∂P :=
      integral_mono ((hI n).sub hJ).norm (((hf n).sub hg).abs.const_mul C)
        (fun ω => by simpa only [Real.norm_eq_abs] using hbound (f n ω) (g ω))
    _ = C * ∫ ω, |f n ω - g ω| ∂P := integral_const_mul _ _

end DOZZ.Proofs
