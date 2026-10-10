/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CountableRandomTestLimit
public import DOZZ.Correlations.Tails.RandomTestL1Approximation
public import Mathlib.MeasureTheory.Function.Floor

/-! Correlated real parameters in cutoff test functions. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- A countable grid approximating a real parameter from below. -/
noncomputable def parameterGrid (k : ℕ) (t : ℝ) : ℝ :=
  (Int.floor (((k : ℝ) + 1) * t) : ℝ) / ((k : ℝ) + 1)

theorem parameter_grid_error (k : ℕ) (t : ℝ) :
    |t - parameterGrid k t| ≤ 1 / ((k : ℝ) + 1) := by
  have hd : 0 < (k : ℝ) + 1 := by positivity
  have hlo := Int.floor_le (((k : ℝ) + 1) * t)
  have hhi := Int.lt_floor_add_one (((k : ℝ) + 1) * t)
  have hle : parameterGrid k t ≤ t := by
    dsimp [parameterGrid]
    exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hlo)
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  dsimp [parameterGrid]
  have heq : t - (Int.floor (((k : ℝ) + 1) * t) : ℝ) / ((k : ℝ) + 1) =
      (t * ((k : ℝ) + 1) - (Int.floor (((k : ℝ) + 1) * t) : ℝ)) / ((k : ℝ) + 1) := by
    field_simp
  rw [heq, div_le_div_iff_of_pos_right hd]
  nlinarith

/-- A random parameter can be substituted into deterministic cutoff limits when the
parameter approximation has a uniform integrable error envelope. Neither the parameter
nor the envelope is required to be independent of the random measures. -/
theorem tendstoInMeasure_random_parameter
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
    (θ : Ω → ℝ) (hθ : Measurable θ)
    (hcoord : ∀ t, TendstoInMeasure P (fun n ω => f n ω t) atTop (fun ω => g ω t))
    (L : ℕ → Ω → ℝ≥0∞) (Llim : Ω → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hL : ∀ n, ∫⁻ ω, L n ω ∂P ≤ C) (hLlim : ∫⁻ ω, Llim ω ∂P ≤ C)
    (hmeas : ∀ k n, AEMeasurable (fun ω => ENNReal.ofReal
      ‖f n ω (θ ω) - f n ω (parameterGrid k (θ ω))‖) P)
    (hmeaslim : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal
      ‖g ω (parameterGrid k (θ ω)) - g ω (θ ω)‖) P)
    (herror : ∀ k n ω, ENNReal.ofReal
      ‖f n ω (θ ω) - f n ω (parameterGrid k (θ ω))‖ ≤
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) * L n ω)
    (herrorlim : ∀ k ω, ENNReal.ofReal
      ‖g ω (parameterGrid k (θ ω)) - g ω (θ ω)‖ ≤
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) * Llim ω) :
    TendstoInMeasure P (fun n ω => f n ω (θ ω)) atTop (fun ω => g ω (θ ω)) := by
  let a : ℕ → ℕ → Ω → ℝ := fun k n ω => f n ω (parameterGrid k (θ ω))
  let b : ℕ → Ω → ℝ := fun k ω => g ω (parameterGrid k (θ ω))
  have hab (k : ℕ) : TendstoInMeasure P (a k) atTop (b k) := by
    let choice : Ω → ℕ := fun ω => Encodable.encode
      (Int.floor (((k : ℝ) + 1) * θ ω))
    let param : ℕ → ℝ := fun i =>
      (((Encodable.decode (α := ℤ) i).getD 0 : ℤ) : ℝ) / ((k : ℝ) + 1)
    have hc : Measurable choice :=
      (measurable_of_countable (Encodable.encode : ℤ → ℕ)).comp
        (Int.measurable_floor.comp (hθ.const_mul _))
    have hp (ω : Ω) : param (choice ω) = parameterGrid k (θ ω) := by
      change (((Encodable.decode (α := ℤ) (Encodable.encode
        (Int.floor (((k : ℝ) + 1) * θ ω)))).getD 0 : ℤ) : ℝ) / ((k : ℝ) + 1) = _
      rw [Encodable.encodek]
      rfl
    have h := tendstoInMeasure_countable_selection P
      (fun n ω i => f n ω (param i)) (fun ω i => g ω (param i)) choice hc
        (fun i => hcoord (param i))
    simpa only [hp] using h
  have ht : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have he : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1)) * C)
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, zero_mul, Function.comp_def] using
      ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0 |>.comp hi) (Or.inr hC)
  apply tendstoInMeasure_L1_approximation P _ _ a b hab _ he hmeas hmeaslim
  · intro k n
    exact (lintegral_mono (herror k n)).trans (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (hL n))
  · intro k
    exact (lintegral_mono (herrorlim k)).trans (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl hLlim)


end DOZZ.Proofs
