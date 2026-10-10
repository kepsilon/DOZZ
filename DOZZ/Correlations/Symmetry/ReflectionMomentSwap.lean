/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionRho
public import DOZZ.Correlations.Symmetry.InversionSwap
public import DOZZ.Statements.GMC.EquatorGFFGMCLawTransport
@[expose] public section
open MeasureTheory Filter
open scoped Distributions Topology ENNReal
namespace DOZZ.Proofs

/-- Reflection exchanges the first two charges through correlated re-pinning and Gaussian tilt.
The identity holds for extended nonnegative moments, without a finiteness premise. -/
theorem rho_moment_swap12
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (∫⁻ ω, rho γ (M ω) a b c ^ (-sExp γ a b c) ∂P) =
      ∫⁻ ω, rho γ (M ω) b a c ^ (-sExp γ a b c) ∂P := by
  obtain ⟨Xc, hXc, _⟩ := hM.2
  let L := fun ω => Xc ω 1 0
  let Y := symmetryRepinnedField X L
  let N := symmetryRepinnedChaos γ M L
  let Z := fun ω x r => Xc ω (1 - x) r - L ω
  let s := sExp γ a b c
  let t := -γ * s
  let A := γ ^ 2 * s ^ 2 * symmetryReflectionKappa
  let E := ENNReal.ofReal (Real.exp (-A))
  have hY : IsEquatorGFF P Y := isEquatorGFF_symmetryRepinnedField P X hX Xc hXc
  have hN : IsGMCOf P Y γ N := isGMCOf_symmetryRepinnedChaos P X hX Xc hXc γ M hM
  have hZ : IsCircleAverage P Y Z := isCircleAverage_symmetryRepinned P X hX Xc hXc
  have hL : IsGaussianL2Limit P Y (fun ω => t * L ω) :=
    IsGaussianL2Limit_const_mul_symmetry P Y L
      (reflection_normalization_in_repinned_closure P X hX Xc hXc) t
  have hV : gaussianVariance P (fun ω => t * L ω) / 2 = A := by
    rw [symmetry_gaussianVariance_mul, reflection_normalization_variance P X hX Xc hXc]
    dsimp [t, A]
    ring
  let H := fun (_ : TestFn → ℝ) (μ : Measure ℂ) => symmetryCorrectedRho γ a b c μ ^ (-s)
  have hHm : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2) := by
    simpa only [ENNReal.rpow_eq_pow, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp
        ((symmetryCorrectedRho_measurable γ a b c).comp measurable_snd))
  have htilt := DOZZ.equatorGFF_GMC_tilt P Y hY γ hγ hγ2 N hN Z hZ
    (fun ω => t * L ω) hL (symmetryTiltPotential t)
    (symmetryTiltPotential_uniform P X hX Xc hXc t) H hHm
  have hleft (ω : Ω) : ENNReal.ofReal
      (Real.exp (t * L ω - gaussianVariance P (fun ω => t * L ω) / 2)) *
        H (fun f => Y ω f) (N ω) = E * rho γ (M ω) a b c ^ (-s) := by
    change ENNReal.ofReal (Real.exp (t * L ω - gaussianVariance P (fun ω => t * L ω) / 2)) *
      symmetryCorrectedRho γ a b c (symmetryRepinnedChaos γ M L ω) ^ (-s) = _
    rw [hV, symmetryCorrectedRho_repinned γ a b c hγ.ne', symmetry_exp_mul_rpow,
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have hex : t * L ω - A + (-γ * L ω) * (-s) = -A := by
      dsimp [t]
      ring
    rw [hex]
  have hright (ω : Ω) :
      H (fun f => Y ω f + gaussianCovariance P (fun ω => Y ω f) (fun ω => t * L ω))
        ((N ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * symmetryTiltPotential t x)))) =
      E * rho γ (N ω) b a c ^ (-s) := by
    change symmetryCorrectedRho γ a b c
      ((N ω).withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * symmetryTiltPotential (-γ * sExp γ a b c) x)))) ^ (-s) = _
    rw [symmetryCorrectedRho_tilt, symmetry_exp_mul_rpow]
    have hex : (γ ^ 2 * sExp γ a b c * symmetryReflectionKappa) * (-s) = -A := by
      dsimp [A, s]
      ring
    rw [hex]
  have ht : (∫⁻ ω, E * rho γ (M ω) a b c ^ (-s) ∂P) =
      ∫⁻ ω, E * rho γ (N ω) b a c ^ (-s) ∂P := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal
          (Real.exp (t * L ω - gaussianVariance P (fun ω => t * L ω) / 2)) *
            H (fun f => Y ω f) (N ω) ∂P :=
        lintegral_congr_ae (ae_of_all _ (fun ω => (hleft ω).symm))
      _ = _ := htilt
      _ = _ := lintegral_congr_ae (ae_of_all _ hright)
  have hE0 : E ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hEt : E ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel := congrArg (fun v : ℝ≥0∞ => E⁻¹ * v) ht
  rw [lintegral_const_mul' _ _ hEt, lintegral_const_mul' _ _ hEt,
    ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hE0 hEt, one_mul, one_mul] at hcancel
  have hRmeas : Measurable (fun μ : Measure ℂ => rho γ μ b a c ^ (-s)) := by
    simpa only [ENNReal.rpow_eq_pow, Function.comp_def] using
      ENNReal.continuous_rpow_const.measurable.comp (rho_measure_measurable γ b a c)
  exact hcancel.trans (DOZZ.equatorGFF_GMC_law_transport P Y hY P X hX γ hγ hγ2 N hN M hM
    (fun _ μ => rho γ μ b a c ^ (-s)) (hRmeas.comp measurable_snd))

theorem unitVolumeStructureConstant_swap12
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    unitVolumeStructureConstant P M γ a b c = unitVolumeStructureConstant P M γ b a c := by
  have hs : sExp γ b a c = sExp γ a b c := by unfold sExp; ring
  unfold unitVolumeStructureConstant
  rw [hs, rho_moment_swap12 P X M γ a b c hγ hγ2 hX hM]
end DOZZ.Proofs
