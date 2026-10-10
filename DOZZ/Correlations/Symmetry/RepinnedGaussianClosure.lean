/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.RepinnedLaw
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Topology.Instances.ENNReal.Lemmas
@[expose] public section
open MeasureTheory Filter Set
open scoped Distributions Topology ENNReal
namespace DOZZ.Proofs

/-- The correlated normalization is also in the re-pinned field's Gaussian closure. -/
theorem reflection_normalization_in_repinned_closure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    IsGaussianL2Limit P (symmetryRepinnedField X (fun ω => Xc ω 1 0))
      (fun ω => Xc ω 1 0) := by
  let : IsProbabilityMeasure P := hX.1
  let L := fun ω => Xc ω 1 0
  have hL : MemLp L 2 P := hXc.2.1 1 0
  obtain ⟨f, hgap, hint⟩ := exists_testFn_circleEnergyGap_and_integral_tendsto 0 0
  have hmass : Tendsto (fun n => testMass (f n)) atTop (𝓝 1) := by
    have h := hint (fun _ => (1 : ℝ)) continuous_const
    let := circleMeasure_isProbability (0 : ℂ) 0
    simpa [testMass] using h
  have hsource : Tendsto (fun n => eLpNorm (fun ω => X ω (f n)) 2 P) atTop (𝓝 0) := by
    have h := hXc.2.2 0 0 f hgap
    have he n : eLpNorm (fun ω => X ω (f n) - Xc ω 0 0) 2 P =
        eLpNorm (fun ω => X ω (f n)) 2 P := by
      apply eLpNorm_congr_ae
      filter_upwards [circleAverage_equator_ae_eq_zero X Xc hXc] with ω hω
      simp only [hω, Pi.zero_apply, sub_zero]
    simpa only [he] using h
  have hc : Tendsto (fun n => ‖1 - testMass (f n)‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hm : Tendsto (fun n => 1 - testMass (f n)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hmass
    simpa only [enorm_zero, Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp hm
  have hscalar : Tendsto (fun n => eLpNorm (fun ω =>
      (1 - testMass (f n)) * L ω) 2 P) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hc (Or.inr hL.eLpNorm_ne_top)
    simp only [zero_mul] at h
    have he n : eLpNorm (fun ω => (1 - testMass (f n)) * L ω) 2 P =
        ‖1 - testMass (f n)‖ₑ * eLpNorm L 2 P := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        eLpNorm_const_smul (1 - testMass (f n)) L 2 P
    simpa only [he] using h
  let g := fun n => -(symmetryReflectionTest (f n))
  refine ⟨hL, g, ?_⟩
  have he n : (fun ω => L ω - symmetryRepinnedField X L ω (g n)) =
      fun ω => X ω (f n) + (1 - testMass (f n)) * L ω := by
    have hg : symmetryReflectionTest (g n) = -(f n) := by
      ext x
      change -(f n (1 - (1 - x))) = -(f n x)
      rw [show (1 : ℂ) - (1 - x) = x by ring]
    have hm : (∫ x, g n x) = -testMass (f n) := by
      change (∫ x, -(symmetryReflectionTest (f n) x)) = _
      rw [integral_neg]
      exact congrArg Neg.neg (symmetryReflection_testMass (f n))
    funext ω
    rw [symmetryRepinnedField_apply, hg, hm, map_neg]
    ring
  change Tendsto (fun n => eLpNorm (fun ω => L ω - symmetryRepinnedField X L ω (g n)) 2 P)
    atTop (𝓝 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    (by simpa only [zero_add] using hsource.add hscalar)
    (fun _ => bot_le)
  intro n
  change eLpNorm (fun ω => L ω - symmetryRepinnedField X L ω (g n)) 2 P ≤ _
  rw [he]
  have h := eLpNorm_add_le (μ := P) (p := (2 : ℝ≥0∞))
    (f := fun ω => X ω (f n)) (g := fun ω => (1 - testMass (f n)) * L ω) (by norm_num)
  simpa only [Pi.add_def] using h
end DOZZ.Proofs
