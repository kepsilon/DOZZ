/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalEnergyBound
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

/-!
# DOZZ.GFF.KernelLimitContinuity

The local Schur estimate makes the deterministic G4 kernel map continuous on every compact
support piece, hence continuous on the test-function inductive limit.
-/

@[expose] public section

open MeasureTheory Set Metric TopologicalSpace
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Topology Distributions

namespace DOZZ

abbrev GFFLocalTest (K : TopologicalSpace.Compacts ℂ) :=
  𝓓_{K}(ℂ, ℝ)

/-- The local L² norm of a compactly supported smooth function is controlled by its zeroth
compact-support seminorm on any ball. -/
theorem integral_sq_localTest_le_seminorm (K : TopologicalSpace.Compacts ℂ)
    (f : GFFLocalTest K) (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, ‖f z‖ ^ 2) ≤
      (volume (ball (0 : ℂ) R)).toReal * ‖(f : ℂ →ᵇ ℝ)‖ ^ 2 := by
  let B : Set ℂ := ball 0 R
  let μ : Measure ℂ := (volume : Measure ℂ).restrict B
  let C : ℝ := ‖(f : ℂ →ᵇ ℝ)‖
  have hfinite : volume B < ⊤ := by
    dsimp [B]
    exact measure_ball_lt_top
  have hpoint (z : ℂ) : ‖f z‖ ^ 2 ≤ C ^ 2 := by
    dsimp [C]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (BoundedContinuousFunction.norm_coe_le_norm (f : ℂ →ᵇ ℝ) z)
  have hfint : Integrable (fun z : ℂ => ‖f z‖ ^ 2)
      μ := by
    have hfmem : MemLp f 2 μ :=
      f.continuous.memLp_of_hasCompactSupport f.compact_supp
    simpa [Real.norm_eq_abs, sq_abs] using hfmem.integrable_sq
  have hconst : Integrable (fun _ : ℂ => C ^ 2) μ := by
    by_cases hC : C ^ 2 = 0
    · simp [hC]
    · exact (integrable_const_iff_isFiniteMeasure hC).2
        (MeasureTheory.isFiniteMeasure_restrict.mpr hfinite.ne)
  have hmono :
      (∫ z in B, ‖f z‖ ^ 2) ≤ ∫ z in B, C ^ 2 :=
    integral_mono_ae hfint hconst (ae_of_all _ hpoint)
  calc
    (∫ z in ball (0 : ℂ) R, ‖f z‖ ^ 2) = ∫ z in B, ‖f z‖ ^ 2 := by rfl
    _ ≤ ∫ z in B, C ^ 2 := hmono
    _ = (volume B).toReal * C ^ 2 := by
      rw [integral_const]
      simp [B, Measure.real_def, Measure.restrict_apply MeasurableSet.univ]
    _ = (volume (ball (0 : ℂ) R)).toReal *
          ‖(f : ℂ →ᵇ ℝ)‖ ^ 2 := by
      simp [B, C]

/-- The G4 kernel map extends continuously from test functions into the noise Hilbert space. -/
noncomputable def equatorKernelLimitMapCLM :
    TestFn →L[ℝ] GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 := by
  classical
  refine TestFunction.mkCLM ℝ equatorKernelLimitMap ?_ ?_ ?_
  · intro f g
    exact equatorKernelLimitMap.map_add f g
  · intro c f
    exact equatorKernelLimitMap.map_smul c f
  · intro K hK
    obtain ⟨R, hRpos, hKR⟩ := K.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
    let A : GFFLocalTest K → GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 := fun f =>
      equatorKernelLimitMap (TestFunction.ofSupportedIn hK f)
    have hAadd : ∀ f g, A (f + g) = A f + A g := by
      intro f g
      change equatorKernelLimitMap (TestFunction.ofSupportedIn hK (f + g)) =
        equatorKernelLimitMap (TestFunction.ofSupportedIn hK f) +
          equatorKernelLimitMap (TestFunction.ofSupportedIn hK g)
      have hsum : TestFunction.ofSupportedIn hK (f + g) =
          TestFunction.ofSupportedIn hK f + TestFunction.ofSupportedIn hK g := by
        ext z
        rfl
      rw [hsum]
      exact equatorKernelLimitMap.map_add
        (TestFunction.ofSupportedIn hK f) (TestFunction.ofSupportedIn hK g)
    have hAsmul : ∀ (c : ℝ) (f : GFFLocalTest K), A (c • f) = c • A f := by
      intro c f
      change equatorKernelLimitMap (TestFunction.ofSupportedIn hK (c • f)) =
        c • equatorKernelLimitMap (TestFunction.ofSupportedIn hK f)
      have hsmul : TestFunction.ofSupportedIn hK (c • f) =
          c • TestFunction.ofSupportedIn hK f := by
        ext z
        rfl
      rw [hsmul]
      exact equatorKernelLimitMap.map_smul c (TestFunction.ofSupportedIn hK f)
    have hbound : ∃ (s : Finset ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f,
        ‖A f‖ ≤ C * ((s.sup fun j =>
          ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ (↑(⊤ : ENat)) K j) f) := by
      let Q : ℝ := (∫ p : ℂ × ℂ in ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R,
        ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ)
      let V : ℝ := (volume (ball (0 : ℂ) R)).toReal
      let C : ℝ := Real.sqrt (Q * V)
      have hC : 0 ≤ C := by positivity
      refine ⟨{0}, C, hC, fun f => ?_⟩
      have hsupp : Function.support (TestFunction.ofSupportedIn hK f) ⊆ ball (0 : ℂ) R := by
        exact (subset_closure.trans (f.tsupport_subset.trans hKR))
      have hsq := norm_sq_equatorKernelLimitMap_le_localL2 R
        (TestFunction.ofSupportedIn hK f) hsupp
      have hL2 := integral_sq_localTest_le_seminorm K f R
      have hQ : 0 ≤ Q := by positivity
      have hest : ‖A f‖ ^ 2 ≤ Q * (V *
          ‖(f : ℂ →ᵇ ℝ)‖ ^ 2) := by
        dsimp [A, Q, V]
        exact hsq.trans (mul_le_mul_of_nonneg_left hL2 hQ)
      have hCsq : C ^ 2 = Q * V := by
        dsimp [C]
        have hV : 0 ≤ V := by dsimp [V]; positivity
        rw [Real.sq_sqrt (mul_nonneg hQ hV)]
      have hseminorm : ‖(f : ℂ →ᵇ ℝ)‖ =
          ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ (↑(⊤ : ENat)) K 0 f :=
        ContDiffMapSupportedIn.norm_toBoundedContinuousFunction ℝ f
      have hnonnegSemi : 0 ≤
          ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ (↑(⊤ : ENat)) K 0 f :=
        by rw [← hseminorm]; positivity
      have htarget : ‖A f‖ ≤ C *
          ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ (↑(⊤ : ENat)) K 0 f := by
        have hprod : 0 ≤ C * ‖(f : ℂ →ᵇ ℝ)‖ := mul_nonneg hC (norm_nonneg _)
        have hsqprod : ‖A f‖ ^ 2 ≤ (C * ‖(f : ℂ →ᵇ ℝ)‖) ^ 2 := by
          calc
            ‖A f‖ ^ 2 ≤ Q * (V * ‖(f : ℂ →ᵇ ℝ)‖ ^ 2) := hest
            _ = (Q * V) * ‖(f : ℂ →ᵇ ℝ)‖ ^ 2 := by ring
            _ = (C * ‖(f : ℂ →ᵇ ℝ)‖) ^ 2 := by rw [← hCsq]; ring
        have hnormle := (sq_le_sq₀ (norm_nonneg _) hprod).1 hsqprod
        rw [← hseminorm]
        exact hnormle
      simpa using htarget
    exact (ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ A hAadd hAsmul hbound).continuous

@[simp]
theorem equatorKernelLimitMapCLM_apply (f : TestFn) :
    equatorKernelLimitMapCLM f = equatorKernelLimitMap f := rfl

end DOZZ

end
