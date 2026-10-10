/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.AffinePush
public import DOZZ.ShiftEquations.Mobius.RepinPotential
public import DOZZ.ShiftEquations.Mobius.RepinChaos
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.GFFStructure.MarkovCommonEvents
import DOZZ.ShiftEquations.Mobius.RepinCovariance
import DOZZ.GFFStructure.GaussianClosure
import DOZZ.GFFStructure.CircleCovariance
import DOZZ.GMC.CircleAverage
import DOZZ.GMC.CircleAverageLimits
import DOZZ.GMC.GaussianInputs

/-!
# The repinned field of an affine map

For `ψ(y) = a y + b` with `a ≠ 0`, let `L` be the average of the equator field over the circle
`ψ(S¹)` (center `b`, radius `|a|`). The repinned field `X̂ = X ∘ ψ - L`, acting on tests by
`X̂(f) = X(ψ_* f) - L ∫ f`, is again an equator GFF, and `X̂_r(y) = X_{r - log|a|}(ψ y) - L` is a
circle-average process for it. All covariances reduce to those of `X` through the kernel identity
`G(ψy, ψy') = G(y,y') + d(y) + d(y')`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The repinned field as a continuous test functional. -/
noncomputable def repinFieldCLM {Ω : Type*} (X : Ω → Distr) (L : Ω → ℝ) (a b : ℂ) (ω : Ω) :
    TestFn →L[ℝ] ℝ :=
  (distributionToTestCLM (X ω)).comp (affinePushTestFn a b) - L ω • testAreaIntegralCLM

/-- The repinned field `X̂ = X ∘ ψ - L`. -/
noncomputable def repinField {Ω : Type*} (X : Ω → Distr) (L : Ω → ℝ) (a b : ℂ) : Ω → Distr :=
  repinFieldCLM X L a b

theorem repinField_apply {Ω : Type*} (X : Ω → Distr) (L : Ω → ℝ) (a b : ℂ) (ω : Ω)
    (f : TestFn) :
    repinField X L a b ω f = X ω (affinePushTestFn a b f) - L ω * ∫ z, f z := by
  change (distributionToTestCLM (X ω)) (affinePushTestFn a b f) - L ω * testAreaIntegralCLM f = _
  rw [testAreaIntegralCLM_apply, distributionToTestCLM_apply]

section Covariances

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
  (Xc : Ω → ℂ → ℝ → ℝ)

/-- Centered covariance of two circle averages is their double circle energy. -/
theorem covariance_circleAverage_eq (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (x y : ℂ) (r s : ℝ) :
    cov[fun ω => Xc ω x r, fun ω => Xc ω y s; P] =
      ∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r := by
  obtain ⟨_, hMean⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  rw [← isCircleAverage_covariance P X hX Xc hXc x y r s]
  simp only [covariance, gaussianCovariance, hMean, sub_zero]

/-- A circle average and the unit-circle average are uncorrelated (the equator pin). -/
theorem integral_integral_gffKernel_unit_right (y : ℂ) (r : ℝ) :
    ∫ u, ∫ v, gffKernel u v ∂circleMeasure 0 0 ∂circleMeasure y r = 0 := by
  simp_rw [integral_gffKernel_circleMeasure_unit, integral_zero]

/-- The unit-circle average is uncorrelated with every circle average. -/
theorem integral_integral_gffKernel_unit_left (hX : IsEquatorGFF P X)
    (hXc : IsCircleAverage P X Xc) (y : ℂ) (r : ℝ) :
    ∫ u, ∫ v, gffKernel u v ∂circleMeasure y r ∂circleMeasure 0 0 = 0 := by
  rw [← covariance_circleAverage_eq P X Xc hX hXc 0 y 0 r, covariance_comm,
    covariance_circleAverage_eq P X Xc hX hXc y 0 r 0,
    integral_integral_gffKernel_unit_right]

end Covariances

section Repin

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
  (Xc : Ω → ℂ → ℝ → ℝ) (a b : ℂ)

/-- The repinning circle average. -/
local notation "Lr" => fun ω => Xc ω b (-Real.log ‖a‖)

/-- The covariance of the repinning average with a pushed circle average. -/
theorem covariance_repin_circle (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (ha : a ≠ 0) (y : ℂ) (r : ℝ) :
    cov[Lr, fun ω => Xc ω (a * y + b) (r - Real.log ‖a‖); P] =
      repinKappa a b + ∫ u, affineDefect a b u ∂circleMeasure y r := by
  rw [covariance_circleAverage_eq P X Xc hX hXc]
  have h := circleEnergy_affine a b ha 0 y 0 r
  simp only [mul_zero, zero_add, zero_sub] at h
  rw [h, integral_integral_gffKernel_unit_left P X Xc hX hXc y r, zero_add]
  rfl

/-- **The variance of the repinned field.** -/
theorem variance_repinField (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (ha : a ≠ 0) (f : TestFn) :
    Var[fun ω => repinField X (Lr) a b ω f; P] = gffCov f f := by
  have _ := hX.1
  have hXm := equatorGFF_test_memLp X hX (affinePushTestFn a b f)
  have hLm : MemLp (Lr) 2 P := hXc.2.1 b _
  have hY : (fun ω => repinField X (Lr) a b ω f) =
      fun ω => X ω (affinePushTestFn a b f) - (∫ z, f z) * Xc ω b (-Real.log ‖a‖) := by
    funext ω
    rw [repinField_apply]
    ring
  have hmY : AEMeasurable (fun ω => X ω (affinePushTestFn a b f) -
      (∫ z, f z) * Xc ω b (-Real.log ‖a‖)) P :=
    hXm.aestronglyMeasurable.aemeasurable.sub (hLm.aestronglyMeasurable.aemeasurable.const_mul _)
  rw [hY, ← covariance_self hmY,
    covariance_fun_sub_fun_sub hXm (hLm.const_mul _) hXm (hLm.const_mul _),
    covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_left,
    covariance_const_mul_right, equatorGFF_test_covariance X hX,
    covariance_comm (X := fun ω => X ω (affinePushTestFn a b f)),
    circleAverage_test_covariance P X Xc hX hXc b _ (affinePushTestFn a b f),
    covariance_circleAverage_eq P X Xc hX hXc, repin_selfEnergy a b ha,
    gffCov_affinePush a b ha f f, circleCross_repin_affinePush a b ha f]
  ring

/-- **The repinned field is an equator GFF.** -/
theorem isEquatorGFF_repinField (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (ha : a ≠ 0) :
    IsEquatorGFF P (repinField X (Lr) a b) := by
  have _ := hX.1
  have hLmeas : Measurable (Lr) :=
    (hXc.1 (-Real.log ‖a‖)).comp (measurable_id.prodMk measurable_const)
  refine ⟨hX.1, fun f => ⟨?_, ?_⟩⟩
  · simp_rw [repinField_apply]
    exact (hX.2 _).1.sub (hLmeas.mul measurable_const)
  · have hL := isCircleAverage_isGaussianL2Limit P X hX Xc hXc b (-Real.log ‖a‖)
    have hJ := equatorGFF_finite_evaluations_with_L_jointly_gaussian P X hX _ hL
      (fun _ : Unit => affinePushTestFn a b f)
    obtain ⟨-, v, hv⟩ := hJ.2.2 (fun i => match i with
      | none => -(∫ z, f z)
      | some _ => 1)
    have hv' : P.map (fun ω => repinField X (Lr) a b ω f) = gaussianReal 0 v := by
      rw [← hv]
      congr 1
      funext ω
      rw [Fintype.sum_option, Fintype.sum_unique, repinField_apply]
      simp only
      ring
    refine ⟨v, ?_, hv'⟩
    have hmeas : AEMeasurable (fun ω => repinField X (Lr) a b ω f) P := by
      simp_rw [repinField_apply]
      exact ((hX.2 _).1.sub (hLmeas.mul measurable_const)).aemeasurable
    rw [← variance_repinField P X Xc a b hX hXc ha f, ← variance_id_map hmeas, hv',
      variance_id_gaussianReal]

/-- Covariance of the repinned field with a repinned circle average. -/
theorem covariance_repinField_repinCircle (hX : IsEquatorGFF P X)
    (hXc : IsCircleAverage P X Xc) (ha : a ≠ 0) (g : TestFn) (y : ℂ) (r : ℝ) :
    cov[fun ω => repinField X (Lr) a b ω g, fun ω => repinCircle Xc (Lr) a b ω y r; P] =
      circleCross y r g := by
  have _ := hX.1
  have hXm := equatorGFF_test_memLp X hX (affinePushTestFn a b g)
  have hLm : MemLp (Lr) 2 P := hXc.2.1 b _
  have hCm := hXc.2.1 (a * y + b) (r - Real.log ‖a‖)
  have hY : (fun ω => repinField X (Lr) a b ω g) =
      fun ω => X ω (affinePushTestFn a b g) - (∫ z, g z) * Xc ω b (-Real.log ‖a‖) := by
    funext ω
    rw [repinField_apply]
    ring
  rw [hY]
  simp only [repinCircle]
  rw [covariance_fun_sub_fun_sub hXm (hLm.const_mul _) hCm hLm,
    covariance_const_mul_left, covariance_const_mul_left,
    covariance_comm (X := fun ω => X ω (affinePushTestFn a b g)),
    circleAverage_test_covariance P X Xc hX hXc _ _ (affinePushTestFn a b g),
    covariance_comm (X := fun ω => X ω (affinePushTestFn a b g)),
    circleAverage_test_covariance P X Xc hX hXc b _ (affinePushTestFn a b g),
    covariance_repin_circle P X Xc a b hX hXc ha y r,
    covariance_circleAverage_eq P X Xc hX hXc, repin_selfEnergy a b ha,
    circleCross_affinePush a b ha g y r, circleCross_repin_affinePush a b ha g]
  ring

/-- Variance of a repinned circle average. -/
theorem variance_repinCircle (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (ha : a ≠ 0) (y : ℂ) (r : ℝ) :
    Var[fun ω => repinCircle Xc (Lr) a b ω y r; P] = circleSelfEnergy y r := by
  have _ := hX.1
  have hLm : MemLp (Lr) 2 P := hXc.2.1 b _
  have hCm := hXc.2.1 (a * y + b) (r - Real.log ‖a‖)
  have hm : AEMeasurable (fun ω => repinCircle Xc (Lr) a b ω y r) P :=
    (hCm.sub hLm).aestronglyMeasurable.aemeasurable
  rw [← covariance_self hm]
  simp only [repinCircle]
  rw [covariance_fun_sub_fun_sub hCm hLm hCm hLm,
    covariance_comm (X := fun ω => Xc ω (a * y + b) (r - Real.log ‖a‖))
      (Y := fun ω => Xc ω b (-Real.log ‖a‖)),
    covariance_repin_circle P X Xc a b hX hXc ha y r,
    covariance_circleAverage_eq P X Xc hX hXc (a * y + b) (a * y + b),
    covariance_circleAverage_eq P X Xc hX hXc b b,
    repin_selfEnergy a b ha, circleEnergy_affine a b ha y y r r]
  unfold circleSelfEnergy
  ring

/-- **The repinned circle averages are a circle-average process for the repinned field.** -/
theorem isCircleAverage_repinField (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (ha : a ≠ 0) :
    IsCircleAverage P (repinField X (Lr) a b) (repinCircle Xc (Lr) a b) := by
  have _ := hX.1
  have hLmeas : Measurable (Lr) :=
    (hXc.1 (-Real.log ‖a‖)).comp (measurable_id.prodMk measurable_const)
  have hLm : MemLp (Lr) 2 P := hXc.2.1 b _
  obtain ⟨_, hMean⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  refine ⟨fun r => measurable_repinCircle Xc _ hXc.1 hLmeas a b r,
    fun y r => (hXc.2.1 _ _).sub hLm, fun y r f hf => ?_⟩
  -- the L² distance is the energy gap
  have hFm : ∀ g : TestFn, MemLp (fun ω => repinField X (Lr) a b ω g) 2 P := fun g => by
    simp_rw [repinField_apply]
    exact (equatorGFF_test_memLp X hX _).sub (hLm.mul_const _)
  have hCm : MemLp (fun ω => repinCircle Xc (Lr) a b ω y r) 2 P := (hXc.2.1 _ _).sub hLm
  have hgap : ∀ g : TestFn,
      ∫ ω, (repinField X (Lr) a b ω g - repinCircle Xc (Lr) a b ω y r) ^ 2 ∂P =
        circleEnergyGap y r g := by
    intro g
    have hmean : ∫ ω, (repinField X (Lr) a b ω g - repinCircle Xc (Lr) a b ω y r) ∂P = 0 := by
      simp only [repinField_apply, repinCircle]
      have i1 : Integrable (fun ω => X ω (affinePushTestFn a b g)) P :=
        (equatorGFF_test_memLp X hX _).integrable one_le_two
      have i2 : Integrable (fun ω => Xc ω b (-Real.log ‖a‖) * ∫ z, g z) P :=
        (hLm.integrable one_le_two).mul_const _
      have i3 : Integrable (fun ω => Xc ω (a * y + b) (r - Real.log ‖a‖)) P :=
        (hXc.2.1 _ _).integrable one_le_two
      have i4 : Integrable (fun ω => Xc ω b (-Real.log ‖a‖)) P := hLm.integrable one_le_two
      have i12 : Integrable (fun ω => X ω (affinePushTestFn a b g) -
          Xc ω b (-Real.log ‖a‖) * ∫ z, g z) P := i1.sub i2
      have i34 : Integrable (fun ω => Xc ω (a * y + b) (r - Real.log ‖a‖) -
          Xc ω b (-Real.log ‖a‖)) P := i3.sub i4
      rw [integral_sub i12 i34, integral_sub i1 i2, integral_sub i3 i4,
        integral_mul_const, equatorGFF_test_integral X hX, hMean, hMean]
      ring
    have hm : AEMeasurable (fun ω => repinField X (Lr) a b ω g -
        repinCircle Xc (Lr) a b ω y r) P := ((hFm g).sub hCm).aestronglyMeasurable.aemeasurable
    rw [← variance_of_integral_eq_zero hm hmean, ← covariance_self hm,
      covariance_fun_sub_fun_sub (hFm g) hCm (hFm g) hCm,
      covariance_self (hFm g).aestronglyMeasurable.aemeasurable,
      covariance_self hCm.aestronglyMeasurable.aemeasurable,
      covariance_comm (X := fun ω => repinCircle Xc (Lr) a b ω y r),
      variance_repinField P X Xc a b hX hXc ha g,
      covariance_repinField_repinCircle P X Xc a b hX hXc ha g y r,
      variance_repinCircle P X Xc a b hX hXc ha y r]
    unfold circleEnergyGap
    ring
  have hnorm : ∀ n, eLpNorm (fun ω => repinField X (Lr) a b ω (f n) -
      repinCircle Xc (Lr) a b ω y r) 2 P =
        ENNReal.ofReal (circleEnergyGap y r (f n) ^ (1 / 2 : ℝ)) := by
    intro n
    have hW : MemLp (fun ω => repinField X (Lr) a b ω (f n) -
        repinCircle Xc (Lr) a b ω y r) 2 P := (hFm (f n)).sub hCm
    rw [hW.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ← hgap (f n)]
    congr 2
    · congr 1
      funext ω
      simp [Real.norm_eq_abs, sq_abs]
    · norm_num
  simp_rw [hnorm]
  have h0 : Tendsto (fun n => circleEnergyGap y r (f n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hc
    exact hc.comp hf
  have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h0
  rw [ENNReal.ofReal_zero] at h1
  exact h1

end Repin

end DOZZ.Proofs

end
