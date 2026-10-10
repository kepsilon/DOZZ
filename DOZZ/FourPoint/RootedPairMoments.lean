/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TwoRootedDomination
public import DOZZ.GMC.SharpMoments.SeibergWeight

/-! The positive Taylor square as an exact two-root integral, preserving both density factors. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A measurable square of a weighted mass equals its double integral, for any measure. -/
theorem weighted_mass_square_identity (μ : Measure ℂ)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) :
    a * (∫⁻ u, f u ∂μ) ^ 2 = ∫⁻ u, ∫⁻ v, f u * f v * a ∂μ ∂μ := by
  rw [pow_two]
  calc
    a * ((∫⁻ u, f u ∂μ) * ∫⁻ u, f u ∂μ) =
        (∫⁻ u, f u ∂μ) * ((∫⁻ u, f u ∂μ) * a) := by ring
    _ = ∫⁻ u, f u * ((∫⁻ v, f v ∂μ) * a) ∂μ :=
      (lintegral_mul_const _ hf).symm
    _ = ∫⁻ u, ∫⁻ v, f u * f v * a ∂μ ∂μ := by
      apply lintegral_congr
      intro u
      have hfu : Measurable (fun v : ℂ => f u * f v) := measurable_const.mul hf
      rw [lintegral_mul_const a hfu, lintegral_const_mul (f u) hf]
      ring

/-- Iterated rooted identity for a positive weighted square and a measurable mass functional. -/
theorem rooted_square_weight_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ ω, G (M ω) * (∫⁻ u, f u ∂M ω) ^ 2 ∂P) =
      ∫⁻ u, ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u v)) *
        (f u * f v * G (gmcRootedMeasure γ u (gmcRootedMeasure γ v (M ω)))) ∂P
          ∂gmcReferenceMeasure ∂gmcReferenceMeasure := by
  have hH : Measurable (fun q : ℂ × (ℂ × Measure ℂ) => f q.1 * f q.2.1 * G q.2.2) :=
    ((hf.comp measurable_fst).mul (hf.comp (measurable_fst.comp measurable_snd))).mul
      (hG.comp (measurable_snd.comp measurable_snd))
  rw [show (∫⁻ ω, G (M ω) * (∫⁻ u, f u ∂M ω) ^ 2 ∂P) =
    ∫⁻ ω, ∫⁻ u, ∫⁻ v, f u * f v * G (M ω) ∂M ω ∂M ω ∂P from
      lintegral_congr (fun ω => weighted_mass_square_identity (M ω) f hf (G (M ω)))]
  exact rooted_pair_identity P X hX γ hγ hγ2 M hM
    (fun u v μ => f u * f v * G μ) hH

/-- The positive absolute kernel is measurable, with its prescribed values at the roots. -/
theorem gammaHalf_absolute_kernel_measurable (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    Measurable (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖)) := by
  apply ENNReal.measurable_ofReal.comp
  have hn : Measurable (normPlus : ℂ → ℝ) := measurable_const.max measurable_norm
  have hxz : Measurable (fun x : ℂ => ‖x - z‖) := (measurable_id.sub_const z).norm
  have hx1 : Measurable (fun x : ℂ => ‖x - 1‖) := (measurable_id.sub_const 1).norm
  exact (((hxz.pow_const _).mul (hn.pow_const _)).div
    ((measurable_norm.pow_const _).mul (hx1.pow_const _))).div hxz

/-- The exact Coulomb mass is a measurable functional on all measures; no clipping is used. -/
theorem coulombMass_measure_measurable {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    Measurable (fun μ : Measure ℂ => coulombMass γ μ α z αinf) :=
  Measure.measurable_lintegral (measurable_coulombWeight γ α z αinf)

/-- [KRV, (idefin)] in its exact rooted form. The reference measures retain both normalization
 densities; the displayed kernel retains two absolute denominators (erratum K19, see
 docs/ERRATA-AND-DEVIATIONS.md). -/
theorem twoRooted_majorant_rooted_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (z : ℂ) :
    gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p z =
      ∫⁻ u, ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u v)) *
        (ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z u / ‖u - z‖) *
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z v / ‖v - z‖) *
            (coulombMass γ (gmcRootedMeasure γ u (gmcRootedMeasure γ v (M ω)))
              ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 2)) ∂P
          ∂gmcReferenceMeasure ∂gmcReferenceMeasure := by
  exact rooted_square_weight_identity P X hX γ hγ hγ2 M hM
    (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖))
    (gammaHalf_absolute_kernel_measurable γ α₁ α₂ α₃ z)
    (fun μ => (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 2))
    ((coulombMass_measure_measurable γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).pow_const _)

end DOZZ.Proofs
