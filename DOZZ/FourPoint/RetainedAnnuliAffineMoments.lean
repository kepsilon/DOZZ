/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliAffineLaw
public import DOZZ.FourPoint.RetainedAnnuliJoint

/-! Joint moment scaling with the common outer-scale Gaussian integrated exactly. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The outer scale acts on the sum `p+q`, retaining its cross term in the exponent. -/
theorem affine_open_set_joint_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (U : Fin 2 → Set ℂ) (hU : ∀ j, IsOpen (U j))
    (hUR : ∀ j, U j ⊆ Metric.closedBall 0 R) (p q : ℝ) :
    (∫⁻ ω, (M ω ((fun y => a + c • y) '' U 0)) ^ p *
      (M ω ((fun y => a + c • y) '' U 1)) ^ q ∂P) =
      ENNReal.ofReal (c ^ (γ * Q γ * (p + q) - γ ^ 2 * (p + q) ^ 2 / 2)) *
        ∫⁻ ω, (M ω (U 0)) ^ p * (M ω (U 1)) ^ q ∂P := by
  have : IsProbabilityMeasure P := hX.1
  let G : Measure ℝ := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have : IsProbabilityMeasure G := instIsProbabilityMeasureGaussianReal 0 _
  let s : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have hs : Measurable s := by dsimp only [s]; fun_prop
  have hspos (w : ℝ) : 0 < s w := by dsimp only [s]; positivity
  let A : Fin 2 → Set ℂ := fun j => (fun y => a + c • y) '' U j
  let t : Ω → Fin 2 → ℝ := fun ω j => (M ω (A j)).toReal
  let t' : Ω × ℝ → Fin 2 → ℝ := fun w j => s w.2 * (M w.1 (U j)).toReal
  have hmass (j : Fin 2) : AEMeasurable (fun ω => M ω (U j)) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (U j) (hU j).measurableSet
  have ht : AEMeasurable t P := aemeasurable_pi_iff.2 fun j =>
    ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (A j)
        (openSetScale_image_isOpen hc.ne' a (hU j)).measurableSet)
  have ht' : AEMeasurable t' (P.prod G) := aemeasurable_pi_iff.2 fun j =>
    ((hs.comp measurable_snd).aemeasurable).mul
      (ENNReal.measurable_toReal.comp_aemeasurable (hmass j)).comp_fst
  let ψ : (Fin 2 → ℝ) → ℝ≥0∞ := fun v => ENNReal.ofReal (v 0) ^ p * ENNReal.ofReal (v 1) ^ q
  have hψ : Measurable ψ := by dsimp only [ψ]; fun_prop
  have hlaw : Measure.map t P = Measure.map t' (P.prod G) :=
    affine_open_set_vector_law P X hX γ hγ hγ2 M hM hc hc1 hR hRsmall hTsmall U hU hUR
  have hfinite (ω : Ω) (D : Set ℂ) : M ω D ≠ ⊤ := by
    let _ := hM.1 ω
    exact measure_ne_top _ _
  have hleft : (∫⁻ v, ψ v ∂Measure.map t P) =
      ∫⁻ ω, (M ω (A 0)) ^ p * (M ω (A 1)) ^ q ∂P := by
    rw [lintegral_map' hψ.aemeasurable ht]
    congr 1
    funext ω
    simp only [ψ, t, ENNReal.ofReal_toReal (hfinite ω _)]
  have hpoint (w : Ω × ℝ) : ψ (t' w) =
      ((M w.1 (U 0)) ^ p * (M w.1 (U 1)) ^ q) * ENNReal.ofReal (s w.2) ^ (p + q) := by
    dsimp only [ψ, t']
    rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
      ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfinite w.1 _), ENNReal.ofReal_toReal (hfinite w.1 _),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hfinite w.1 _) p,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hfinite w.1 _) q,
      ENNReal.rpow_add p q (ENNReal.ofReal_pos.mpr (hspos w.2)).ne' ENNReal.ofReal_ne_top]
    ac_rfl
  have hfactor : AEMeasurable (fun w => ENNReal.ofReal (s w) ^ (p + q)) G :=
    (ENNReal.measurable_ofReal.comp hs).aemeasurable.pow_const _
  have hprod : (∫⁻ v, ψ v ∂Measure.map t' (P.prod G)) =
      (∫⁻ ω, (M ω (U 0)) ^ p * (M ω (U 1)) ^ q ∂P) *
        ∫⁻ w, ENNReal.ofReal (s w) ^ (p + q) ∂G := by
    rw [lintegral_map' hψ.aemeasurable ht']
    simp_rw [hpoint]
    exact lintegral_prod_mul ((hmass 0).pow_const p |>.mul ((hmass 1).pow_const q)) hfactor
  have hexp : 2 * (p + q) + γ ^ 2 * (p + q) / 2 - γ ^ 2 * (p + q) ^ 2 / 2 =
      γ * Q γ * (p + q) - γ ^ 2 * (p + q) ^ 2 / 2 := by
    unfold Q
    field_simp
  rw [← hleft, hlaw, hprod]
  have hg : (∫⁻ w, ENNReal.ofReal (s w) ^ (p + q) ∂G) =
      ENNReal.ofReal (c ^ (γ * Q γ * (p + q) - γ ^ 2 * (p + q) ^ 2 / 2)) := by
    have hh := gaussianScaleFactor_rpow_integral γ c (p + q) hc hc1
    rw [hexp] at hh
    exact hh
  rw [hg, mul_comm]

end DOZZ.Proofs
