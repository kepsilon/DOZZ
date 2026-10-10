/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneAffineSoftMax
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Uniform bounds and convergence for finite affine soft maxima. -/

@[expose] public section

open Filter Topology
open scoped BigOperators

namespace DOZZ.Proofs

/-- The maximum of a nonempty finite family of affine functions. -/
noncomputable def affineMax {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => a i * x + b i)

theorem affineMax_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (x : ℝ) (i : ι) : a i * x + b i ≤ affineMax a b x := by
  classical
  exact Finset.le_sup' (fun j => a j * x + b j) (Finset.mem_univ i)

theorem affineMax_continuous {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) : Continuous (affineMax a b) := by
  classical
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => by fun_prop)

/-- Soft maxima lie between the true maximum and the maximum plus the logarithmic cardinal error. -/
theorem affineSoftMax_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (β x : ℝ) (hβ : 0 < β) :
    affineMax a b x ≤ affineSoftMax a b β x ∧
      affineSoftMax a b β x ≤ affineMax a b x + Real.log (Fintype.card ι : ℝ) / β := by
  classical
  have hSpos := affineSoftMaxSum_pos a b β x
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · apply Finset.sup'_le
    intro i hi
    have hE : Real.exp (β * (a i * x + b i)) ≤ affineSoftMaxSum a b β x := by
      exact Finset.single_le_sum (f := fun j => Real.exp (β * (a j * x + b j)))
        (fun j _ => Real.exp_nonneg _) hi
    have h := Real.log_le_log (Real.exp_pos _) hE
    rw [Real.log_exp] at h
    exact (le_div_iff₀ hβ).mpr (by simpa [mul_comm] using h)
  · have hsum : affineSoftMaxSum a b β x ≤
        (Fintype.card ι : ℝ) * Real.exp (β * affineMax a b x) := by
      calc
        _ ≤ ∑ i : ι, Real.exp (β * affineMax a b x) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (affineMax_le a b x i) hβ.le)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h := Real.log_le_log hSpos hsum
    rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    apply (div_le_iff₀ hβ).mpr
    calc
      _ ≤ Real.log (Fintype.card ι : ℝ) + β * affineMax a b x := h
      _ = _ := by field_simp; ring

/-- Finite affine maxima have at most linear growth. -/
theorem affineMax_linear_growth {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖affineMax a b x‖ ≤ C * (‖x‖ + 1) := by
  classical
  let C : ℝ := 1 + ∑ i, |a i| + ∑ i, |b i|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha (i : ι) : |a i| ≤ C := by
    have h := Finset.single_le_sum (f := fun i => |a i|)
      (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    have hb := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) => abs_nonneg (b j))
    dsimp [C]
    linarith
  have hb (i : ι) : |b i| ≤ C := by
    have h := Finset.single_le_sum (f := fun i => |b i|)
      (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i)
    have ha := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) => abs_nonneg (a j))
    dsimp [C]
    linarith
  have hline (i : ι) (x : ℝ) : |a i * x + b i| ≤ C * (|x| + 1) := by
    calc
      _ ≤ |a i * x| + |b i| := abs_add_le _ _
      _ = |a i| * |x| + |b i| := by rw [abs_mul]
      _ ≤ C * |x| + C := add_le_add
        (mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)) (hb i)
      _ = _ := by ring
  refine ⟨C, hC, ?_⟩
  intro x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
  constructor
  · have h := (abs_le.mp (hline (Classical.arbitrary ι) x)).1
    exact h.trans (affineMax_le a b x _)
  · exact Finset.sup'_le _ _ (fun i _ => (abs_le.mp (hline i x)).2)

/-- Increasing the inverse smoothing scale recovers the finite affine maximum pointwise. -/
theorem affineSoftMax_tendsto {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (x : ℝ) :
    Tendsto (fun n : ℕ => affineSoftMax a b ((n : ℝ) + 1) x) atTop (𝓝 (affineMax a b x)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have herr := hden.const_div_atTop (Real.log (Fintype.card ι : ℝ))
  have hu : Tendsto (fun n : ℕ => affineMax a b x +
      Real.log (Fintype.card ι : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (affineMax a b x)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (affineSoftMax_bounds a b _ x (by positivity)).1)
    (fun n => (affineSoftMax_bounds a b _ x (by positivity)).2)

end DOZZ.Proofs
