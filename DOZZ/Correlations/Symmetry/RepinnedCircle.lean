/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.RepinnedGaussianClosure
public import DOZZ.Correlations.Symmetry.ReflectionCircleEnergy
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import DOZZ.GFFStructure.CircleVersion
@[expose] public section
open MeasureTheory Filter
open scoped Distributions Topology ENNReal
namespace DOZZ.Proofs

/-- The ordinary circles of the correlated re-pinning are the reflected source circles
minus their equator normalization. -/
theorem isCircleAverage_symmetryRepinned
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    IsCircleAverage P (symmetryRepinnedField X (fun ω => Xc ω 1 0))
      (fun ω x r => Xc ω (1 - x) r - Xc ω 1 0) := by
  let L := fun ω => Xc ω 1 0
  let Y := symmetryRepinnedField X L
  let Z := fun ω x r => Xc ω (1 - x) r - L ω
  have hY : IsEquatorGFF P Y := isEquatorGFF_symmetryRepinnedField P X hX Xc hXc
  obtain ⟨Yc, hYc⟩ := exists_equatorGFF_circle_average_witness Y hY
  have hLmeas : Measurable L := (hXc.1 0).comp (measurable_id.prodMk measurable_const)
  have hL : MemLp L 2 P := hXc.2.1 1 0
  apply isCircleAverage_of_ae_eq P Y Yc Z hYc
  · intro r
    exact ((hXc.1 r).comp (measurable_fst.prodMk
      (measurable_const.sub measurable_snd))).sub (hLmeas.comp measurable_fst)
  intro x r
  obtain ⟨f, hgap, hint⟩ := exists_testFn_circleEnergyGap_and_integral_tendsto x r
  let D := ∫ z, symmetryReflectionPotential z ∂circleMeasure x r
  have hm : Tendsto (fun n => testMass (f n)) atTop (𝓝 1) := by
    let := circleMeasure_isProbability x r
    simpa [testMass] using hint (fun _ => (1 : ℝ)) continuous_const
  have hd : Tendsto (fun n => ∫ z, f n z * symmetryReflectionPotential z) atTop (𝓝 D) :=
    hint _ symmetryReflectionPotential_continuous
  have hg : Tendsto (fun n => circleEnergyGap (1 - x) r (symmetryReflectionTest (f n)))
      atTop (𝓝 0) := by
    simp_rw [reflection_circle_energy_gap]
    have h := hgap.add (((hm.sub_const 1).const_mul 2).mul (hd.sub_const D))
    simpa only [sub_self, mul_zero, zero_mul, add_zero] using h
  have ha := hXc.2.2 (1 - x) r (fun n => symmetryReflectionTest (f n)) hg
  have hc : Tendsto (fun n => ‖1 - testMass (f n)‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
    have h : Tendsto (fun n => 1 - testMass (f n)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hm
    simpa only [enorm_zero, Function.comp_def] using
      (continuous_enorm.tendsto (0 : ℝ)).comp h
  have hb : Tendsto (fun n => eLpNorm (fun ω => (1 - testMass (f n)) * L ω) 2 P)
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hc (Or.inr hL.eLpNorm_ne_top)
    simp only [zero_mul] at h
    have he n : eLpNorm (fun ω => (1 - testMass (f n)) * L ω) 2 P =
        ‖1 - testMass (f n)‖ₑ * eLpNorm L 2 P := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        eLpNorm_const_smul (1 - testMass (f n)) L 2 P
    simpa only [he] using h
  have he n : (fun ω => Y ω (f n) - Z ω x r) =
      (fun ω => X ω (symmetryReflectionTest (f n)) - Xc ω (1 - x) r) +
        (fun ω => (1 - testMass (f n)) * L ω) := by
    funext ω
    dsimp [Y, Z]
    rw [symmetryRepinnedField_apply]
    dsimp [testMass]
    ring
  have hz : Tendsto (fun n => eLpNorm (fun ω => Y ω (f n) - Z ω x r) 2 P)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      (by simpa only [zero_add] using ha.add hb) (fun _ => bot_le)
    intro n
    change eLpNorm (fun ω => Y ω (f n) - Z ω x r) 2 P ≤ _
    rw [he]
    exact eLpNorm_add_le (by norm_num)
  have hcanon := hYc.2.2 x r f hgap
  have hzm : TendstoInMeasure P (fun n ω => Y ω (f n)) atTop (fun ω => Z ω x r) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simpa only [Pi.sub_def] using hz)
  have hym : TendstoInMeasure P (fun n ω => Y ω (f n)) atTop (fun ω => Yc ω x r) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simpa only [Pi.sub_def] using hcanon)
  exact tendstoInMeasure_ae_unique hzm hym
end DOZZ.Proofs
