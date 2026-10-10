/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.IndependentInnerTransport
public import DOZZ.FourPoint.Dual.PathLikelihood
public import DOZZ.FourPoint.Reflected.CopiedPolarTransport
import Mathlib.Tactic
/-! The full radial-path/exterior law transports the actual independent restarted polar mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Transport a restarted polar increment with its full radial path and exterior mass.
Local finiteness discharges the measurable polar-code identification on both source spaces. -/
theorem dual_path_outer_polar_integral_transport
    {Ω Λ Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace Ξ]
    (P : Measure Ω) (R : Measure Λ) (S : Measure Ξ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R] [IsProbabilityMeasure S]
    (A : Ω → TwoSidedPath) (A' : Λ → TwoSidedPath)
    (O : Ω → ℝ≥0∞) (O' : Λ → ℝ≥0∞) (Z : Ξ → Measure ℝ)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' R)
    (hO : AEMeasurable O P) (hO' : AEMeasurable O' R)
    (hZ : AEMeasurable Z S) (hfin : ∀ᵐ ω ∂S, ∀ a b : ℝ, Z ω (Icc a b) < ⊤)
    (hlaw : P.map (fun ω => (A ω,O ω)) = R.map (fun ω => (A' ω,O' ω)))
    (γ ν h p : ℝ) (z : ℂ) (T : ℝ≥0) :
    (∫ ω : Ω × Ξ,
      ((O ω.1).toReal + dualPathRadialScale γ ν h z (A ω.1)*
        (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
          (brownianShiftPath T (radialPositiveHalf (A ω.1)) (Real.toNNReal t)-ν*t))) else 0)
          ∂Z ω.2).toReal)^(-p)-(O ω.1).toReal^(-p) ∂P.prod S) =
    ∫ ω : Λ × Ξ,
      ((O' ω.1).toReal + dualPathRadialScale γ ν h z (A' ω.1)*
        (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
          (brownianShiftPath T (radialPositiveHalf (A' ω.1)) (Real.toNNReal t)-ν*t))) else 0)
          ∂Z ω.2).toReal)^(-p)-(O' ω.1).toReal^(-p) ∂R.prod S := by
  let D : TwoSidedPath → BrownianPath := fun a => brownianShiftPath T (radialPositiveHalf a)
  have hD : Measurable D := continuous_brownianShiftPath.measurable.comp
    (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  let H : (TwoSidedPath × ℝ≥0∞) × Measure ℝ → ℝ := fun v =>
    (v.1.2.toReal + dualPathRadialScale γ ν h z v.1.1*
      (reflectedInwardPolarMassCode γ ν (D v.1.1,v.2)).toReal)^(-p)-v.1.2.toReal^(-p)
  have hHm : Measurable H := by
    have hm : Measurable (fun v : (TwoSidedPath × ℝ≥0∞) × Measure ℝ =>
        reflectedInwardPolarMassCode γ ν (D v.1.1,v.2)) := (reflected_measurable_inwardPolarMassCode γ ν).comp
      ((hD.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    have hb : Measurable (fun v : (TwoSidedPath × ℝ≥0∞) × Measure ℝ =>
        dualPathRadialScale γ ν h z v.1.1) := (dual_path_radial_scale_measurable γ ν h z).comp
      (measurable_fst.comp measurable_fst)
    exact (((measurable_snd.comp measurable_fst).ennreal_toReal.add
      (hb.mul hm.ennreal_toReal)).pow_const (-p)).sub
        ((measurable_snd.comp measurable_fst).ennreal_toReal.pow_const (-p))
  have he := dual_joint_law_independent_inner_integral P R S
    (fun ω => (A ω,O ω)) (fun ω => (A' ω,O' ω)) Z
    (hA.prodMk hO) (hA'.prodMk hO') hZ hlaw H hHm
  have hidP : (∫ ω : Ω × Ξ, H ((A ω.1,O ω.1),Z ω.2) ∂P.prod S) =
      ∫ ω : Ω × Ξ,
        ((O ω.1).toReal + dualPathRadialScale γ ν h z (A ω.1)*
          (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
            (brownianShiftPath T (radialPositiveHalf (A ω.1)) (Real.toNNReal t)-ν*t))) else 0)
            ∂Z ω.2).toReal)^(-p)-(O ω.1).toReal^(-p) ∂P.prod S := by
    apply integral_congr_ae
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω
    dsimp only [H]
    rw [reflected_inwardPolarMassCode_eq γ ν (D (A ω.1)) (Z ω.2) hω]
  have hidR : (∫ ω : Λ × Ξ, H ((A' ω.1,O' ω.1),Z ω.2) ∂R.prod S) =
      ∫ ω : Λ × Ξ,
        ((O' ω.1).toReal + dualPathRadialScale γ ν h z (A' ω.1)*
          (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
            (brownianShiftPath T (radialPositiveHalf (A' ω.1)) (Real.toNNReal t)-ν*t))) else 0)
            ∂Z ω.2).toReal)^(-p)-(O' ω.1).toReal^(-p) ∂R.prod S := by
    apply integral_congr_ae
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω
    dsimp only [H]
    rw [reflected_inwardPolarMassCode_eq γ ν (D (A' ω.1)) (Z ω.2) hω]
  rw [hidP, hidR] at he
  exact he

/-- Finiteness of the actual polar mass transfers under the full-path/exterior law,
using the locally finite measurable polar code before taking real values. -/
theorem dual_path_outer_polar_finite_transport
    {Ω Λ Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace Ξ]
    (P : Measure Ω) (R : Measure Λ) (S : Measure Ξ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R] [IsProbabilityMeasure S]
    (A : Ω → TwoSidedPath) (A' : Λ → TwoSidedPath)
    (O : Ω → ℝ≥0∞) (O' : Λ → ℝ≥0∞) (Z : Ξ → Measure ℝ)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' R)
    (hO : AEMeasurable O P) (hO' : AEMeasurable O' R)
    (hZ : AEMeasurable Z S) (hfin : ∀ᵐ ω ∂S, ∀ a b : ℝ, Z ω (Icc a b) < ⊤)
    (hlaw : P.map (fun ω => (A ω,O ω)) = R.map (fun ω => (A' ω,O' ω)))
    (γ ν : ℝ) (T : ℝ≥0) :
    (∀ᵐ ω : Ω × Ξ ∂P.prod S, (∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*
        (brownianShiftPath T (radialPositiveHalf (A ω.1)) (Real.toNNReal t)-ν*t))) else 0)
        ∂Z ω.2) ≠ ⊤) ↔
    ∀ᵐ ω : Λ × Ξ ∂R.prod S, (∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*
        (brownianShiftPath T (radialPositiveHalf (A' ω.1)) (Real.toNNReal t)-ν*t))) else 0)
        ∂Z ω.2) ≠ ⊤ := by
  let D : TwoSidedPath → BrownianPath := fun a => brownianShiftPath T (radialPositiveHalf a)
  have hD : Measurable D := continuous_brownianShiftPath.measurable.comp
    (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  let K : (TwoSidedPath × ℝ≥0∞) × Measure ℝ → ℝ≥0∞ := fun v =>
    reflectedInwardPolarMassCode γ ν (D v.1.1,v.2)
  have hK : Measurable K := (reflected_measurable_inwardPolarMassCode γ ν).comp
    ((hD.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have he := dual_joint_law_independent_inner_ae P R S
    (fun ω => (A ω,O ω)) (fun ω => (A' ω,O' ω)) Z
    (hA.prodMk hO) (hA'.prodMk hO') hZ hlaw (fun v => K v ≠ ⊤)
    (hK (measurableSet_singleton ⊤)).compl
  constructor
  · intro hf
    have hc : ∀ᵐ ω : Ω × Ξ ∂P.prod S, K ((A ω.1,O ω.1),Z ω.2) ≠ ⊤ := by
      filter_upwards [hf, measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω hloc
      dsimp only [K]
      rw [reflected_inwardPolarMassCode_eq γ ν (D (A ω.1)) (Z ω.2) hloc]
      exact hω
    filter_upwards [he.mp hc, measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω hloc
    dsimp only [K] at hω
    rw [reflected_inwardPolarMassCode_eq γ ν (D (A' ω.1)) (Z ω.2) hloc] at hω
    exact hω
  · intro hf
    have hc : ∀ᵐ ω : Λ × Ξ ∂R.prod S, K ((A' ω.1,O' ω.1),Z ω.2) ≠ ⊤ := by
      filter_upwards [hf, measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω hloc
      dsimp only [K]
      rw [reflected_inwardPolarMassCode_eq γ ν (D (A' ω.1)) (Z ω.2) hloc]
      exact hω
    filter_upwards [he.mpr hc, measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω hloc
    dsimp only [K] at hω
    rw [reflected_inwardPolarMassCode_eq γ ν (D (A ω.1)) (Z ω.2) hloc] at hω
    exact hω

end DOZZ.Proofs
