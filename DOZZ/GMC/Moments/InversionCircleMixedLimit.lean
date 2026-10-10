/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionMixedCovariance
public import DOZZ.GMC.Moments.InversionCircleWeakApproximation
public import DOZZ.GMC.Moments.InversionPotentialExtension

/-! Mixed covariance of the actual coupled transformed circles and source circles. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs

/-- The coupled transformed circle has the exact inverse point/source-circle covariance. -/
theorem inversionCircle_source_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (x : ℂ) (r : ℝ) (hsmall : 2 * Real.exp (-r) < ‖x‖)
    (Z : Ω → ℝ) (hZ : MemLp Z 2 P)
    (f : ℕ → TestFn) (hf : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0))
    (hlim : Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f n) (hf n)) - Z ω) 2 P) atTop (𝓝 0))
    (y : ℂ) (s : ℝ) :
    covariance (fun ω => Xc ω y s) Z P =
      ∫ u, CirclePotential.innerPot y s u⁻¹ ∂circleMeasure x r := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨g, hg, hggap, hweak⟩ := exists_inversionChart_circle_weak_approximation x r hsmall
  have hfLp n := equatorGFF_test_memLp X hX (inversionTest (f n) (hf n))
  have ht : Tendsto (fun n => (hfLp n).toLp
      (fun ω => X ω (inversionTest (f n) (hf n)))) atTop (𝓝 (hZ.toLp Z)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hfLp Z hZ).mpr hlim
  have hgt := equatorGFF_inversion_testL2_tendsto_to_circle_limit X hX x r
    f hgap hf (hZ.toLp Z) ht g hggap hg
  have hglim := tendsto_eLpNorm_sub_of_L2_versions P _ (hZ.toLp Z)
    (fun n ω => X ω (inversionTest (g n) (hg n))) Z
    (fun n => (equatorGFF_test_memLp X hX (inversionTest (g n) (hg n))).coeFn_toLp.symm)
    hZ.coeFn_toLp.symm hgt
  have hzero : Tendsto (fun _ : ℕ => eLpNorm
      (fun ω => Xc ω y s - Xc ω y s) 2 P) atTop (𝓝 0) := by
    simpa only [sub_self, ← Pi.zero_def, eLpNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hc := tendsto_covariance_of_eLpNorm_sub
    (fun _ => hXc.2.1 y s)
    (fun n => equatorGFF_test_memLp X hX (inversionTest (g n) (hg n)))
    (hXc.2.1 y s) hZ hzero hglim
  have he n : covariance (fun ω => Xc ω y s)
      (fun ω => X ω (inversionTest (g n) (hg n))) P =
      ∫ u, g n u * inversionCirclePotential y s u := by
    rw [circleAverage_inversionTest_covariance P X hX Xc hXc]
    apply integral_congr_ae
    filter_upwards [(volume : Measure ℂ).ae_ne 0] with u hu
    rw [inversionCirclePotential_eq_innerPot y s hu]
  have hcl := hc.congr' (Eventually.of_forall he)
  have hval := tendsto_nhds_unique hcl
    (hweak (inversionCirclePotential y s) (continuous_inversionCirclePotential y s))
  refine hval.trans (integral_congr_ae ?_)
  filter_upwards [ae_norm_sub_center_circleMeasure x r] with u hu
  apply inversionCirclePotential_eq_innerPot
  intro hu0
  have h := hu
  simp only [hu0, zero_sub, norm_neg] at h
  linarith [Real.exp_pos (-r)]

/-- The same mixed identity in the second-moment and angular-average form used by the
admissible-regularization compatibility bounds. -/
theorem inversionCircle_source_gaussianCovariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (x : ℂ) (r : ℝ) (hsmall : 2 * Real.exp (-r) < ‖x‖)
    (Z : Ω → ℝ) (hZ : MemLp Z 2 P)
    (f : ℕ → TestFn) (hf : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0))
    (hlim : Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f n) (hf n)) - Z ω) 2 P) atTop (𝓝 0))
    (y : ℂ) (s : ℝ) :
    gaussianCovariance P (fun ω => Xc ω y s) Z =
      Real.circleAverage (fun u => CirclePotential.innerPot y s u⁻¹) x (Real.exp (-r)) := by
  let : IsProbabilityMeasure P := hX.1
  have hmeanZ : (∫ ω, Z ω ∂P) = 0 :=
    integral_eq_zero_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (inversionTest (f n) (hf n))) hZ
      (fun n => equatorGFF_test_integral X hX _) hlim
  obtain ⟨_hg, hmeanXc⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  have hc := inversionCircle_source_covariance X hX Xc hXc x r hsmall Z hZ
    f hf hgap hlim y s
  have he : gaussianCovariance P (fun ω => Xc ω y s) Z =
      covariance (fun ω => Xc ω y s) Z P := by
    simp only [gaussianCovariance, covariance, hmeanZ, hmeanXc, sub_zero]
  rw [he, hc, integral_circleMeasure_eq_circleAverage]
  exact (CirclePotential.continuous_innerPot y s).measurable.comp measurable_inv

end DOZZ.Proofs
