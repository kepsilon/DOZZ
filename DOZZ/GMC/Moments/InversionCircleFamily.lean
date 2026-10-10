/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCircleL2
public import DOZZ.GMC.Construction.CircleAverageJointVersion

/-! Coupled Gaussian circle limits for the inverted local field. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Distributions

namespace DOZZ.Proofs

/-- Inverted test limits form a measurable centered Gaussian family with the ordinary circle
covariance, on the original field probability space. -/
theorem exists_equatorGFF_inversion_circle_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    ∃ f : (ℂ × ℝ) → ℕ → TestFn,
    ∃ hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart,
    ∃ Y : (ℂ × ℝ) → Ω → ℝ,
      (∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0)) ∧
      (∀ p, Measurable[equatorGFFRawDistributionSigma X] (Y p) ∧
        Measurable (Y p) ∧ MemLp (Y p) 2 P ∧
        Tendsto (fun n => eLpNorm (fun ω => X ω (inversionTest (f p n) (hf p n)) -
          Y p ω) 2 P) atTop (𝓝 0)) ∧
      IsGaussianProcess Y P ∧
      (∀ p, (∫ ω, Y p ω ∂P) = 0) ∧
      (∀ p q, covariance (Y p) (Y q) P =
        ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2) := by
  let : IsProbabilityMeasure P := hX.1
  have hex (p : ℂ × ℝ) :=
    exists_equatorGFF_inversion_circle_test_L2_limit_all X hX p.1 p.2
  choose f hf W hgap hW using hex
  have hrep p := exists_measurable_equatorGFF_circle_L2_limit X hX
    (fun n => inversionTest (f p n) (hf p n)) (W p) (hW p)
  choose Y hYraw hYm hYmem hYae hYlim using hrep
  have hproc : IsGaussianProcess Y P := by
    apply isGaussianProcess_of_eLpNorm_sub
      (fun n p ω => X ω (inversionTest (f p n) (hf p n))) Y
    · intro n
      exact equatorGFF_test_family_isGaussianProcess X hX
        (fun p => inversionTest (f p n) (hf p n))
    · exact hYmem
    · exact hYlim
  have hmean p : (∫ ω, Y p ω ∂P) = 0 :=
    integral_eq_zero_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (inversionTest (f p n) (hf p n)))
      (hYmem p) (fun n => equatorGFF_test_integral X hX _) (hYlim p)
  refine ⟨f, hf, Y, hgap, fun p => ⟨hYraw p, hYm p, hYmem p, hYlim p⟩,
    hproc, hmean, ?_⟩
  obtain ⟨f0, W0, Y0, hgap0, _hcross0, hW0, hY0, _hproc0, _hmean0, hcov0⟩ :=
    exists_equatorGFF_circle_L2_geometry X hX
  have hlim0 p : Tendsto (fun n => eLpNorm (fun ω => X ω (f p n) - Y0 p ω) 2 P)
      atTop (𝓝 0) := by
    have ht := equatorGFF_testL2_tendsto_to_circle_limit X hX p.1 p.2
      (f0 p) (hgap0 p) (W0 p) (hW0 p) (f p) (hgap p)
    exact tendsto_eLpNorm_sub_of_L2_versions P _ (W0 p)
      (fun n ω => X ω (f p n)) (Y0 p)
      (fun n => (equatorGFF_test_memLp X hX (f p n)).coeFn_toLp.symm)
      (hY0 p).2.2.2.1 ht
  intro p q
  have hi := tendsto_covariance_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX (inversionTest (f p n) (hf p n)))
    (fun n => equatorGFF_test_memLp X hX (inversionTest (f q n) (hf q n)))
    (hYmem p) (hYmem q) (hYlim p) (hYlim q)
  have ho := tendsto_covariance_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX (f p n))
    (fun n => equatorGFF_test_memLp X hX (f q n))
    (hY0 p).2.2.1 (hY0 q).2.2.1 (hlim0 p) (hlim0 q)
  have he n : covariance (fun ω => X ω (inversionTest (f p n) (hf p n)))
      (fun ω => X ω (inversionTest (f q n) (hf q n))) P =
      covariance (fun ω => X ω (f p n)) (fun ω => X ω (f q n)) P := by
    rw [equatorGFF_test_covariance X hX, equatorGFF_test_covariance X hX,
      gffCov_inversionTest]
  have hi' := hi.congr' (Eventually.of_forall he)
  exact (tendsto_nhds_unique hi' ho).trans (hcov0 p q)

/-- The transformed circle family admits joint measurability in the sample and center at every
radius, while retaining its coupled inverted-test L² approximation. -/
theorem exists_equatorGFF_inversion_circle_joint_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    ∃ f : (ℂ × ℝ) → ℕ → TestFn,
    ∃ hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart,
    ∃ Z : Ω → ℂ → ℝ → ℝ,
      (∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0)) ∧
      (∀ r, Measurable (fun p : Ω × ℂ => Z p.1 p.2 r)) ∧
      (∀ x r, MemLp (fun ω => Z ω x r) 2 P) ∧
      (∀ p, Tendsto (fun n => eLpNorm (fun ω =>
        X ω (inversionTest (f p n) (hf p n)) - Z ω p.1 p.2) 2 P) atTop (𝓝 0)) ∧
      IsGaussianProcess (fun p : ℂ × ℝ => fun ω => Z ω p.1 p.2) P ∧
      (∀ p : ℂ × ℝ, (∫ ω, Z ω p.1 p.2 ∂P) = 0) ∧
      (∀ p q : ℂ × ℝ, covariance (fun ω => Z ω p.1 p.2)
        (fun ω => Z ω q.1 q.2) P =
        ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨f, hf, Y, hgap, hY, hproc, hmean, hcov⟩ :=
    exists_equatorGFF_inversion_circle_family X hX
  have hmod r := exists_continuous_circleL2_modification_at_radius
    Y (fun p => (hY p).2.1) (fun p => (hY p).2.2.1) hproc hmean hcov r
  choose V hVm hVc hVeq using hmod
  have hjoint r := exists_raw_joint_continuous_modification P
    (equatorGFFRawDistributionSigma X)
    (fun ω x => V r x ω) (ae_of_all P (hVc r))
    (fun x => ⟨Y (x, r), (hY (x, r)).1, (hVeq r x).symm⟩)
  choose G hGj hGae using hjoint
  let Z : Ω → ℂ → ℝ → ℝ := fun ω x r => G r ω x
  have hmap : Measurable[mΩ] (fun ω => fun g : TestFn => X ω g) :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := hmap.comap_le
  have hprod : (equatorGFFRawDistributionSigma X).prod (borel ℂ) ≤
      mΩ.prod (borel ℂ) := by
    rw [MeasurableSpace.prod, MeasurableSpace.prod]
    exact sup_le_sup (MeasurableSpace.comap_mono hm0) le_rfl
  have hZae (p : ℂ × ℝ) : (fun ω => Z ω p.1 p.2) =ᵐ[P] Y p := by
    filter_upwards [hGae p.2, hVeq p.2 p.1] with ω hG hV
    exact (hG p.1).trans hV
  refine ⟨f, hf, Z, hgap, fun r => (hGj r).mono hprod le_rfl,
    fun x r => MemLp.ae_eq (hZae (x, r)).symm (hY (x, r)).2.2.1, ?_, ?_, ?_, ?_⟩
  · intro p
    have he n : eLpNorm (fun ω => X ω (inversionTest (f p n) (hf p n)) -
        Z ω p.1 p.2) 2 P =
        eLpNorm (fun ω => X ω (inversionTest (f p n) (hf p n)) - Y p ω) 2 P := by
      apply eLpNorm_congr_ae
      filter_upwards [hZae p] with ω hω
      rw [hω]
    simpa only [he] using (hY p).2.2.2
  · exact hproc.congr (fun p => (hZae p).symm)
  · intro p
    exact (integral_congr_ae (hZae p)).trans (hmean p)
  · intro p q
    exact (covariance_congr_ae (hZae p) (hZae q)).trans (hcov p q)

end DOZZ.Proofs
