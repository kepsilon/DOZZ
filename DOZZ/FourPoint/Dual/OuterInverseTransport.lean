/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.JointLawExpectation
/-! Transfer genuine retained inverse integrability through the full radial-path joint law. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The copied exterior inherits positive real mass and its integrable inverse power
from the actual source exterior, with exact expectation equality. -/
theorem dual_joint_law_outer_inverse_data
    {Ω Λ α : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace α]
    (P : Measure Ω) (R : Measure Λ) (A : Ω → α) (A' : Λ → α)
    (O : Ω → ℝ≥0∞) (O' : Λ → ℝ≥0∞)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' R)
    (hO : AEMeasurable O P) (hO' : AEMeasurable O' R)
    (hlaw : P.map (fun ω => (A ω,O ω)) = R.map (fun ω => (A' ω,O' ω)))
    (p : ℝ) (hpos : ∀ᵐ ω ∂P, 0 < (O ω).toReal)
    (hInv : Integrable (fun ω => (O ω).toReal^(-p)) P) :
    (∀ᵐ ω ∂R, 0 < (O' ω).toReal) ∧
    Integrable (fun ω => (O' ω).toReal^(-p)) R ∧
    (∫ ω, (O ω).toReal^(-p) ∂P) = ∫ ω, (O' ω).toReal^(-p) ∂R := by
  have hpair := hA.prodMk hO
  have hpair' := hA'.prodMk hO'
  have hs : MeasurableSet {v : α × ℝ≥0∞ | 0 < v.2.toReal} :=
    measurableSet_lt measurable_const measurable_snd.ennreal_toReal
  have hp := (ae_map_iff hpair hs).mpr hpos
  rw [hlaw] at hp
  let H : α × ℝ≥0∞ → ℝ := fun v => v.2.toReal^(-p)
  have hHm : Measurable H := measurable_snd.ennreal_toReal.pow_const (-p)
  have hi : Integrable H (P.map (fun ω => (A ω,O ω))) :=
    (integrable_map_measure hHm.aestronglyMeasurable hpair).mpr hInv
  rw [hlaw] at hi
  have hi' := (integrable_map_measure hHm.aestronglyMeasurable hpair').mp hi
  refine ⟨(ae_map_iff hpair' hs).mp hp, hi', ?_⟩
  rw [← integral_map hpair hHm.aestronglyMeasurable,
    ← integral_map hpair' hHm.aestronglyMeasurable, hlaw]

/-- The extended-valued retained inverse expectation is preserved before real conversion. -/
theorem dual_joint_law_outer_inverse_lintegral
    {Ω Λ α : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace α]
    (P : Measure Ω) (R : Measure Λ) (A : Ω → α) (A' : Λ → α)
    (O : Ω → ℝ≥0∞) (O' : Λ → ℝ≥0∞)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' R)
    (hO : AEMeasurable O P) (hO' : AEMeasurable O' R)
    (hlaw : P.map (fun ω => (A ω,O ω)) = R.map (fun ω => (A' ω,O' ω)))
    (p : ℝ) :
    (∫⁻ ω, O ω^(-p) ∂P) = ∫⁻ ω, O' ω^(-p) ∂R := by
  let H : α × ℝ≥0∞ → ℝ≥0∞ := fun v => v.2^(-p)
  have hH : Measurable H := measurable_snd.pow_const (-p)
  rw [← lintegral_map' hH.aemeasurable (hA.prodMk hO),
    ← lintegral_map' hH.aemeasurable (hA'.prodMk hO'), hlaw]

end DOZZ.Proofs
