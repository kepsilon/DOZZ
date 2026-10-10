/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftLimitA

/-! # Real forms of rooted bounds for the softened four-point mass

`bpzSoftI ε m z` is the softened four-point mass `∫ (|x - z|² + ε²)^{γχ/2} base(x) dm(x)` as a real
number. A bound on the lintegral `E[bpzMass^{-p} ∫⁻ f dM]` gives integrability and the same bound
for the real expectation `E[I^{-p} ∫ f dM]`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The softened four-point mass as a real number. -/
noncomputable def bpzSoftI (γ χ α₁ α₂ α₃ ε : ℝ) (m : Measure ℂ) (z : ℂ) : ℝ :=
  bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) m z

theorem bpzSoftI_eq_integral (ε : ℝ) (m : Measure ℂ) (z : ℂ) :
    bpzSoftI γ χ α₁ α₂ α₃ ε m z = ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ ε z x ∂m := rfl

theorem bpzSoftI_eq_toReal (ε : ℝ) (m : Measure ℂ) (z : ℂ) :
    bpzSoftI γ χ α₁ α₂ α₃ ε m z = (bpzMass γ χ α₁ α₂ α₃ ε m z).toReal := by
  rw [bpzSoftI_eq_integral, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => bpzSoftWeight_nonneg ε z x)
    (measurable_bpzSoftWeight ε z).aestronglyMeasurable]
  rfl

theorem bpzSoftI_nonneg (ε : ℝ) (m : Measure ℂ) (z : ℂ) : 0 ≤ bpzSoftI γ χ α₁ α₂ α₃ ε m z := by
  rw [bpzSoftI_eq_toReal]; exact ENNReal.toReal_nonneg

/-- A lintegral bound on `E[bpzMass^{-p} ∫⁻ f dM]` gives the real bound. -/
theorem bpz_real_bound_of_lintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) {p : ℝ} {f : ℂ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) *
      ∫⁻ x, ENNReal.ofReal (f x) ∂M ω ∂P ≤ ENNReal.ofReal B) :
    Integrable (fun ω => bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) * ∫ x, f x ∂M ω) P ∧
      ∫ ω, bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) * ∫ x, f x ∂M ω ∂P ≤ B ∧
      ∀ᵐ ω ∂P, Integrable f (M ω) := by
  have hIm : Measurable fun ω => bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z :=
    (measurable_integral_measure (measurable_bpzSoftWeight ε z)).comp hMm
  have hJm : Measurable fun ω => ∫ x, f x ∂M ω := (measurable_integral_measure hf).comp hMm
  have hmeasL : AEMeasurable (fun ω => bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) *
      ∫⁻ x, ENNReal.ofReal (f x) ∂M ω) P :=
    ((gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (ENNReal.measurable_ofReal.comp (measurable_bpzSoftWeight ε z))).pow_const _).mul
      (gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _ (ENNReal.measurable_ofReal.comp hf))
  have hfinL := ae_lt_top' hmeasL (lt_of_le_of_lt hB ENNReal.ofReal_lt_top).ne
  have hgood : ∀ᵐ ω ∂P, Integrable f (M ω) ∧
      ENNReal.ofReal (bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) * ∫ x, f x ∂M ω) =
        bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) * ∫⁻ x, ENNReal.ofReal (f x) ∂M ω := by
    filter_upwards [hfinL, bpzMass_pos_ae P X hX hγ hγ2 M hM ε hε0 hε1 z,
      bpzMass_lt_top_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ ε z hz0 hz1] with ω h1 h2 h3
    have hpow : bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) ≠ 0 := (ENNReal.rpow_pos h2 h3.ne).ne'
    have hJfin : ∫⁻ x, ENNReal.ofReal (f x) ∂M ω < ⊤ := by
      by_contra hinf
      rw [not_lt, top_le_iff] at hinf
      rw [hinf, ENNReal.mul_top hpow] at h1
      exact lt_irrefl _ h1
    have hfi : Integrable f (M ω) := ⟨hf.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)]; exact hJfin⟩
    refine ⟨hfi, ?_⟩
    have hIpos : 0 < bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z := by
      rw [bpzSoftI_eq_toReal]; exact ENNReal.toReal_pos h2.ne' h3.ne
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hIpos.le _), ← ENNReal.ofReal_rpow_of_pos hIpos,
      bpzSoftI_eq_toReal, ENNReal.ofReal_toReal h3.ne,
      ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hf0)]
  have hnn : ∀ ω, 0 ≤ bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) * ∫ x, f x ∂M ω := fun ω =>
    mul_nonneg (Real.rpow_nonneg (bpzSoftI_nonneg ε _ z) _) (integral_nonneg hf0)
  have hlin : ∫⁻ ω, ENNReal.ofReal (bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) *
      ∫ x, f x ∂M ω) ∂P ≤ ENNReal.ofReal B := by
    refine le_of_eq_of_le (lintegral_congr_ae ?_) hB
    filter_upwards [hgood] with ω hω
    exact hω.2
  have hint : Integrable (fun ω => bpzSoftI γ χ α₁ α₂ α₃ ε (M ω) z ^ (-p) * ∫ x, f x ∂M ω) P :=
    ⟨((hIm.pow_const _).mul hJm).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)).mpr
        (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_, hgood.mono fun ω h => h.1⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hint.1]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hlin

end DOZZ.Proofs
