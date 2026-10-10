/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalEnergyBound
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# DOZZ.GFF.TorusModeTests

Compactly supported real sine and cosine modes for the concrete periodic boxes used in G5.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped InnerProductSpace Topology

namespace DOZZ

/-- A smooth cutoff which equals one on the ball of radius `R + 1` and vanishes outside the ball
of radius `R + 2`. -/
noncomputable def localTorusCutoff (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℂ) where
  rIn := R + 1
  rOut := R + 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem localTorusCutoff_eq_one (R : ℝ) (hR : 0 < R) {z : ℂ}
    (hz : z ∈ closedBall 0 (R + 1)) : localTorusCutoff R hR z = 1 := by
  apply (localTorusCutoff R hR).one_of_mem_closedBall
  simpa [localTorusCutoff] using hz

theorem localTorusCutoff_tsupport (R : ℝ) (hR : 0 < R) :
    tsupport (localTorusCutoff R hR : ℂ → ℝ) = closedBall 0 (R + 2) := by
  simpa [localTorusCutoff] using (localTorusCutoff R hR).tsupport_eq

/-- The physical phase of the `k`th Fourier mode on a square of side `L`. -/
noncomputable def torusModePhase (L : ℝ) (k : Fin 2 → ℤ) (z : ℂ) : ℝ :=
  (2 * Real.pi / L) * ((k 0 : ℝ) * z.re + (k 1 : ℝ) * z.im)

theorem torusModePhase_contDiff (L : ℝ) (k : Fin 2 → ℤ) :
    ContDiff ℝ ⊤ (torusModePhase L k) := by
  have hre : ContDiff ℝ ⊤ (fun z : ℂ => z.re) := by
    change ContDiff ℝ ⊤ (fun z : ℂ => (Complex.reCLM : ℂ → ℝ) z)
    exact Complex.reCLM.contDiff
  have him : ContDiff ℝ ⊤ (fun z : ℂ => z.im) := by
    change ContDiff ℝ ⊤ (fun z : ℂ => (Complex.imCLM : ℂ → ℝ) z)
    exact Complex.imCLM.contDiff
  unfold torusModePhase
  fun_prop (disch := assumption)

noncomputable def localTorusCosFunction (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) : ℂ → ℝ :=
  (localTorusCutoff R hR) * fun z => Real.cos (torusModePhase L k z)

noncomputable def localTorusSinFunction (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) : ℂ → ℝ :=
  (localTorusCutoff R hR) * fun z => Real.sin (torusModePhase L k z)

theorem localTorusCosFunction_hasCompactSupport (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) : HasCompactSupport (localTorusCosFunction R L hR k) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (R + 2))
  calc
    Function.support (localTorusCosFunction R L hR k) ⊆
        tsupport (localTorusCosFunction R L hR k) := subset_tsupport _
    _ ⊆ tsupport (localTorusCutoff R hR : ℂ → ℝ) := tsupport_mul_subset_left
    _ = closedBall 0 (R + 2) := localTorusCutoff_tsupport R hR

theorem localTorusSinFunction_hasCompactSupport (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) : HasCompactSupport (localTorusSinFunction R L hR k) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (R + 2))
  calc
    Function.support (localTorusSinFunction R L hR k) ⊆
        tsupport (localTorusSinFunction R L hR k) := subset_tsupport _
    _ ⊆ tsupport (localTorusCutoff R hR : ℂ → ℝ) := tsupport_mul_subset_left
    _ = closedBall 0 (R + 2) := localTorusCutoff_tsupport R hR

/-- The cosine mode, multiplied by the local compact cutoff. -/
noncomputable def localTorusCosTest (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) : TestFn :=
  TestFunction.mk (localTorusCosFunction R L hR k)
    ((localTorusCutoff R hR).contDiff.mul (by
      exact ((torusModePhase_contDiff L k).cos).of_le (by simp)))
    (localTorusCosFunction_hasCompactSupport R L hR k)
    (by simp)

/-- The sine mode, multiplied by the local compact cutoff. -/
noncomputable def localTorusSinTest (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) : TestFn :=
  TestFunction.mk (localTorusSinFunction R L hR k)
    ((localTorusCutoff R hR).contDiff.mul (by
      exact ((torusModePhase_contDiff L k).sin).of_le (by simp)))
    (localTorusSinFunction_hasCompactSupport R L hR k)
    (by simp)

@[simp]
theorem localTorusCosTest_apply (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) (z : ℂ) :
    localTorusCosTest R L hR k z =
      localTorusCutoff R hR z * Real.cos (torusModePhase L k z) := rfl

@[simp]
theorem localTorusSinTest_apply (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) (z : ℂ) :
    localTorusSinTest R L hR k z =
      localTorusCutoff R hR z * Real.sin (torusModePhase L k z) := rfl

theorem localTorusCosTest_support_subset (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) :
    Function.support (localTorusCosTest R L hR k) ⊆ ball (0 : ℂ) (R + 3) := by
  change Function.support (localTorusCosFunction R L hR k) ⊆ ball (0 : ℂ) (R + 3)
  calc
    Function.support (localTorusCosTest R L hR k) ⊆
        tsupport (localTorusCosFunction R L hR k) := subset_tsupport _
    _ ⊆ tsupport (localTorusCutoff R hR : ℂ → ℝ) := tsupport_mul_subset_left
    _ = closedBall 0 (R + 2) := localTorusCutoff_tsupport R hR
    _ ⊆ ball 0 (R + 3) := closedBall_subset_ball (by linarith)

theorem localTorusSinTest_support_subset (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) :
    Function.support (localTorusSinTest R L hR k) ⊆ ball (0 : ℂ) (R + 3) := by
  change Function.support (localTorusSinFunction R L hR k) ⊆ ball (0 : ℂ) (R + 3)
  calc
    Function.support (localTorusSinTest R L hR k) ⊆
        tsupport (localTorusSinFunction R L hR k) := subset_tsupport _
    _ ⊆ tsupport (localTorusCutoff R hR : ℂ → ℝ) := tsupport_mul_subset_left
    _ = closedBall 0 (R + 2) := localTorusCutoff_tsupport R hR
    _ ⊆ ball 0 (R + 3) := closedBall_subset_ball (by linarith)

theorem localTorusCosTest_abs_le_one (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ)
    (z : ℂ) : |localTorusCosTest R L hR k z| ≤ 1 := by
  rw [localTorusCosTest_apply, abs_mul]
  have hcut : |localTorusCutoff R hR z| ≤ 1 := by
    rw [abs_le]
    have h0 : 0 ≤ localTorusCutoff R hR z :=
      (localTorusCutoff R hR).nonneg' z
    exact ⟨by linarith, (localTorusCutoff R hR).le_one⟩
  calc
    |localTorusCutoff R hR z| * |Real.cos (torusModePhase L k z)| ≤ 1 * 1 :=
      mul_le_mul hcut (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem localTorusSinTest_abs_le_one (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ)
    (z : ℂ) : |localTorusSinTest R L hR k z| ≤ 1 := by
  rw [localTorusSinTest_apply, abs_mul]
  have hcut : |localTorusCutoff R hR z| ≤ 1 := by
    rw [abs_le]
    have h0 : 0 ≤ localTorusCutoff R hR z :=
      (localTorusCutoff R hR).nonneg' z
    exact ⟨by linarith, (localTorusCutoff R hR).le_one⟩
  calc
    |localTorusCutoff R hR z| * |Real.sin (torusModePhase L k z)| ≤ 1 * 1 :=
      mul_le_mul hcut (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem localTorusCosTest_integral_sq_le_volume (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) :
    ∫ z in ball (0 : ℂ) (R + 3), ‖localTorusCosTest R L hR k z‖ ^ 2 ≤
      (volume (ball (0 : ℂ) (R + 3))).toReal := by
  let B : Set ℂ := ball 0 (R + 3)
  let μ : Measure ℂ := (volume : Measure ℂ).restrict B
  have hBlt : volume B < ⊤ := by
    dsimp [B]
    exact measure_ball_lt_top
  have hμfin : IsFiniteMeasure μ := (MeasureTheory.isFiniteMeasure_restrict).2 hBlt.ne
  have hf : MemLp (localTorusCosTest R L hR k) 2 μ := by
    exact (localTorusCosTest R L hR k).continuous.memLp_of_hasCompactSupport
      (localTorusCosTest R L hR k).hasCompactSupport |>.mono_measure Measure.restrict_le_self
  have hfint : Integrable (fun z => (localTorusCosTest R L hR k z) ^ 2) μ := hf.integrable_sq
  have hconst : Integrable (fun _ : ℂ => (1 : ℝ)) μ :=
    (integrable_const_iff_isFiniteMeasure (by norm_num)).2 hμfin
  have hle : (fun z => (localTorusCosTest R L hR k z) ^ 2) ≤ᵐ[μ] fun _ => 1 :=
    ae_of_all _ fun z => by
      have habs := localTorusCosTest_abs_le_one R L hR k z
      rw [sq_le_one_iff_abs_le_one]
      exact habs
  have h := integral_mono_ae hfint hconst hle
  calc
    ∫ z in B, ‖localTorusCosTest R L hR k z‖ ^ 2 ∂volume =
        ∫ z, (localTorusCosTest R L hR k z) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change |localTorusCosTest R L hR k z| ^ 2 = _
        exact sq_abs _
    _ ≤ ∫ z, (1 : ℝ) ∂μ := h
    _ = (volume B).toReal := by
      rw [integral_const]
      simp [μ, B, Measure.real_def, Measure.restrict_apply MeasurableSet.univ]

theorem localTorusSinTest_integral_sq_le_volume (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) :
    ∫ z in ball (0 : ℂ) (R + 3), ‖localTorusSinTest R L hR k z‖ ^ 2 ≤
      (volume (ball (0 : ℂ) (R + 3))).toReal := by
  let B : Set ℂ := ball 0 (R + 3)
  let μ : Measure ℂ := (volume : Measure ℂ).restrict B
  have hBlt : volume B < ⊤ := by
    dsimp [B]
    exact measure_ball_lt_top
  have hμfin : IsFiniteMeasure μ := (MeasureTheory.isFiniteMeasure_restrict).2 hBlt.ne
  have hf : MemLp (localTorusSinTest R L hR k) 2 μ := by
    exact (localTorusSinTest R L hR k).continuous.memLp_of_hasCompactSupport
      (localTorusSinTest R L hR k).hasCompactSupport |>.mono_measure Measure.restrict_le_self
  have hfint : Integrable (fun z => (localTorusSinTest R L hR k z) ^ 2) μ := hf.integrable_sq
  have hconst : Integrable (fun _ : ℂ => (1 : ℝ)) μ :=
    (integrable_const_iff_isFiniteMeasure (by norm_num)).2 hμfin
  have hle : (fun z => (localTorusSinTest R L hR k z) ^ 2) ≤ᵐ[μ] fun _ => 1 :=
    ae_of_all _ fun z => by
      have habs := localTorusSinTest_abs_le_one R L hR k z
      rw [sq_le_one_iff_abs_le_one]
      exact habs
  have h := integral_mono_ae hfint hconst hle
  calc
    ∫ z in B, ‖localTorusSinTest R L hR k z‖ ^ 2 ∂volume =
        ∫ z, (localTorusSinTest R L hR k z) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change |localTorusSinTest R L hR k z| ^ 2 = _
        exact sq_abs _
    _ ≤ ∫ z, (1 : ℝ) ∂μ := h
    _ = (volume B).toReal := by
      rw [integral_const]
      simp [μ, B, Measure.real_def, Measure.restrict_apply MeasurableSet.univ]

end DOZZ

end
