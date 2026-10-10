/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.HaarCommonLimit
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# DOZZ.GFF.LocalModeFunctional

Square-summable random Fourier coordinates are packaged as concrete `ℓ²` vectors. Their inner
products provide the continuous local Sobolev-dual functionals used by the distribution version.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

/-- A square-summable real sequence as an element of the concrete `ℓ²` space. -/
noncomputable def gffLpOfSummableSquares {ι : Type*} (f : ι → ℝ)
    (h : Summable fun i => (f i) ^ 2) : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞) := by
  have hmem : Memℓp f (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [Real.norm_eq_abs, sq_abs] using h
  exact ⟨f, hmem⟩

@[simp]
theorem gffLpOfSummableSquares_apply {ι : Type*} (f : ι → ℝ)
    (h : Summable fun i => (f i) ^ 2) (i : ι) :
    gffLpOfSummableSquares f h i = f i := rfl

/-- The Riesz functional associated to one local square-summable mode sequence. -/
noncomputable def gffLpInnerCLM {ι : Type*}
    (b : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞)) :
    lp (fun _ : ι => ℝ) (2 : ℝ≥0∞) →L[ℝ] ℝ :=
  innerSL ℝ b

@[simp]
theorem gffLpInnerCLM_apply {ι : Type*}
    (b c : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞)) :
    gffLpInnerCLM b c = ⟪b, c⟫_ℝ := by
  rfl

/-- The cosine mode limits on a chart, packaged as an `ℓ²` vector whenever their square sum is
finite. -/
noncomputable def equatorHaarCommonCosEvalLp (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (h : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2) :
    lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) :=
  gffLpOfSummableSquares
    (fun k => equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) h

/-- The sine mode limits on a chart, packaged as an `ℓ²` vector whenever their square sum is
finite. -/
noncomputable def equatorHaarCommonSinEvalLp (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (h : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) :=
  gffLpOfSummableSquares
    (fun k => equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) h

@[simp]
theorem equatorHaarCommonCosEvalLp_apply (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (h : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (k : Fin 2 → ℤ) :
    equatorHaarCommonCosEvalLp R ω h k =
      equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω := rfl

@[simp]
theorem equatorHaarCommonSinEvalLp_apply (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (h : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2)
    (k : Fin 2 → ℤ) :
    equatorHaarCommonSinEvalLp R ω h k =
      equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω := rfl

/-- A square-summable pair of local mode coefficients defines a continuous functional on the
corresponding pair of weighted Fourier coefficient spaces. -/
noncomputable def equatorLocalModePairingCLM (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    (lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) ×
      lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞)) →L[ℝ] ℝ := by
  let bcos := equatorHaarCommonCosEvalLp R ω hcos
  let bsin := equatorHaarCommonSinEvalLp R ω hsin
  let F : (lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) ×
      lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞)) →ₗ[ℝ] ℝ :=
    { toFun := fun c => ⟪bcos, c.1⟫_ℝ + ⟪bsin, c.2⟫_ℝ
      map_add' := by
        intro c d
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
        abel
      map_smul' := by
        intro a c
        change ⟪bcos, a • c.1⟫_ℝ + ⟪bsin, a • c.2⟫_ℝ =
          a • (⟪bcos, c.1⟫_ℝ + ⟪bsin, c.2⟫_ℝ)
        rw [inner_smul_right, inner_smul_right]
        simp only [smul_eq_mul]
        ring }
  have hcont : Continuous F := by
    have h₁ : Continuous fun c :
        lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) ×
          lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) => ⟪bcos, c.1⟫_ℝ := by
      exact (innerSL ℝ bcos).continuous.comp continuous_fst
    have h₂ : Continuous fun c :
        lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) ×
          lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) => ⟪bsin, c.2⟫_ℝ := by
      exact (innerSL ℝ bsin).continuous.comp continuous_snd
    exact h₁.add h₂
  exact ⟨F, hcont⟩

@[simp]
theorem equatorLocalModePairingCLM_apply (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2)
    (c : lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞) ×
      lp (fun _ : Fin 2 → ℤ => ℝ) (2 : ℝ≥0∞)) :
    equatorLocalModePairingCLM R ω hcos hsin c =
      ⟪equatorHaarCommonCosEvalLp R ω hcos, c.1⟫_ℝ +
        ⟪equatorHaarCommonSinEvalLp R ω hsin, c.2⟫_ℝ := rfl

end DOZZ

end
