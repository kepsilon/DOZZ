/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.AnnularEnergyConvergence
public import GaussianFields.LogCorrelated.ABK.TestFunctionAlgebra

/-!
# DOZZ.GFF.EquatorField

The annular finite-energy realization of the equator-pinned Gaussian field.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace DOZZ

/-- The mass functional is linear on compactly supported test functions. -/
theorem testMass_add (f g : TestFn) :
    testMass (f + g) = testMass f + testMass g := by
  have hf : Integrable f (volume : Measure ℂ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable g (volume : Measure ℂ) :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  change (∫ z : ℂ, f z + g z) =
    (∫ z : ℂ, f z) + (∫ z : ℂ, g z)
  exact integral_add hf hg

theorem testMass_smul (a : ℝ) (f : TestFn) :
    testMass (a • f) = a * testMass f := by
  have hf : Integrable f (volume : Measure ℂ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  change (∫ z : ℂ, a * f z) = a * (∫ z : ℂ, f z)
  exact integral_const_mul a f

/-- The centered annular test as a function on `Vec 2`. -/
theorem annularCenteredTestFn_eq_testFnVec_sub (f : TestFn) (n : ℕ)
    (x : GaussianFields.Vec 2) :
    annularCenteredTestFn f n x =
      testFnVec f x - testMass f * annularProbabilityDensityVec n x := by
  have h := testFnVec_eq_annularCenteredTestFn_add f n x
  linarith

theorem annularCenteredTestFn_add (f g : TestFn) (n : ℕ) :
    annularCenteredTestFn (f + g) n =
      annularCenteredTestFn f n + annularCenteredTestFn g n := by
  apply GaussianFields.MeanZeroTestFunction.ext
  intro x
  change annularCenteredTestFn (f + g) n x =
    annularCenteredTestFn f n x + annularCenteredTestFn g n x
  rw [annularCenteredTestFn_eq_testFnVec_sub,
    annularCenteredTestFn_eq_testFnVec_sub,
    annularCenteredTestFn_eq_testFnVec_sub]
  simp [testFnVec, testMass_add]
  ring

theorem annularCenteredTestFn_smul (a : ℝ) (f : TestFn) (n : ℕ) :
    annularCenteredTestFn (a • f) n = a • annularCenteredTestFn f n := by
  apply GaussianFields.MeanZeroTestFunction.ext
  intro x
  change annularCenteredTestFn (a • f) n x =
    a * annularCenteredTestFn f n x
  rw [annularCenteredTestFn_eq_testFnVec_sub,
    annularCenteredTestFn_eq_testFnVec_sub]
  simp [testFnVec, testMass_smul]
  ring

/-- The canonical ABK Hilbert kernel of the `n`th centered annular test. -/
noncomputable def annularABKKernel (f : TestFn) (n : ℕ) :
    GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 :=
  let ζ := GaussianFields.abkStandardCutoff 2
  GaussianFields.abkLogKernelLp (GaussianFields.abkNormalization ζ) ζ
    (annularCenteredTestFn f n)
    (GaussianFields.memLp_abkLogKernelProd_canonical (by norm_num) ζ
      (annularCenteredTestFn f n))

/-- The rescaled annular kernel used to approximate the pinned covariance. -/
noncomputable def equatorKernelApprox (f : TestFn) (n : ℕ) :
    GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 :=
  Real.sqrt (2 * Real.pi) • annularABKKernel f n

theorem annularABKKernel_add (f g : TestFn) (n : ℕ) :
    annularABKKernel (f + g) n = annularABKKernel f n + annularABKKernel g n := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hψ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n)
  have hφ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn g n)
  have hsum := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn (f + g) n)
  have hsum' : MemLp
      (GaussianFields.abkLogKernelProd (GaussianFields.abkNormalization ζ) ζ
        (annularCenteredTestFn f n + annularCenteredTestFn g n)) 2
      (volume : Measure (ℝ × GaussianFields.Vec 2)) := by
    simpa only [← annularCenteredTestFn_add] using hsum
  simpa [annularABKKernel, annularCenteredTestFn_add] using
    (GaussianFields.abkLogKernelLp_add (GaussianFields.abkNormalization ζ) ζ
      (annularCenteredTestFn f n) (annularCenteredTestFn g n) hψ hφ hsum')

theorem annularABKKernel_smul (a : ℝ) (f : TestFn) (n : ℕ) :
    annularABKKernel (a • f) n = a • annularABKKernel f n := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hψ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n)
  have hsmul := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn (a • f) n)
  have hsmul' : MemLp
      (GaussianFields.abkLogKernelProd (GaussianFields.abkNormalization ζ) ζ
        (a • annularCenteredTestFn f n)) 2
      (volume : Measure (ℝ × GaussianFields.Vec 2)) := by
    simpa only [← annularCenteredTestFn_smul] using hsmul
  simpa [annularABKKernel, annularCenteredTestFn_smul] using
    (GaussianFields.abkLogKernelLp_smul (GaussianFields.abkNormalization ζ) ζ a
      (annularCenteredTestFn f n) hψ hsmul')

theorem equatorKernelApprox_add (f g : TestFn) (n : ℕ) :
    equatorKernelApprox (f + g) n =
      equatorKernelApprox f n + equatorKernelApprox g n := by
  rw [equatorKernelApprox, equatorKernelApprox, equatorKernelApprox,
    annularABKKernel_add, smul_add]

theorem equatorKernelApprox_smul (a : ℝ) (f : TestFn) (n : ℕ) :
    equatorKernelApprox (a • f) n = a • equatorKernelApprox f n := by
  rw [equatorKernelApprox, equatorKernelApprox, annularABKKernel_smul]
  simp [smul_smul, mul_comm]

theorem inner_annularABKKernel_eq_covarianceConstant_pairing (f g : TestFn)
    (n k : ℕ) :
    ⟪annularABKKernel f n, annularABKKernel g k⟫_ℝ =
      GaussianFields.abkLGFCovarianceConstant 2 *
        GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn g k) := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hψ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n)
  have hφ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn g k)
  have hcov := GaussianFields.covariance_abkLogCorrelatedFieldL2Canonical_eq_logCovariancePairing
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n) (annularCenteredTestFn g k)
  calc
    _ = cov[
        GaussianFields.scaleSpaceWhiteNoiseL2 2 (annularABKKernel f n),
        GaussianFields.scaleSpaceWhiteNoiseL2 2 (annularABKKernel g k);
        GaussianFields.scaleSpaceWhiteNoiseMeasure 2] := by
          exact (GaussianFields.covariance_scaleSpaceWhiteNoiseL2
            (annularABKKernel f n) (annularABKKernel g k)).symm
    _ = cov[
        GaussianFields.abkLogCorrelatedFieldL2Canonical
          (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n),
        GaussianFields.abkLogCorrelatedFieldL2Canonical
          (by norm_num : 0 < 2) ζ (annularCenteredTestFn g k);
        GaussianFields.scaleSpaceWhiteNoiseMeasure 2] := by
          rfl
    _ = _ := hcov

theorem inner_equatorKernelApprox_eq_pairing (f g : TestFn) (n k : ℕ) :
    ⟪equatorKernelApprox f n, equatorKernelApprox g k⟫_ℝ =
      GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g k) := by
  have hscale : (Real.sqrt (2 * Real.pi)) ^ 2 *
      GaussianFields.abkLGFCovarianceConstant 2 = 1 := by
    rw [abkLGFCovarianceConstant_two_eq_one_div_two_pi]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    field_simp [ne_of_gt Real.pi_pos]
  rw [equatorKernelApprox, equatorKernelApprox,
    inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [inner_annularABKKernel_eq_covarianceConstant_pairing]
  calc
    _ = (Real.sqrt (2 * Real.pi)) ^ 2 *
          (GaussianFields.abkLGFCovarianceConstant 2 *
            GaussianFields.abkLogCovariancePairing
              (annularCenteredTestFn f n) (annularCenteredTestFn g k)) := by ring
    _ = GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn g k) := by
      rw [← mul_assoc, hscale, one_mul]

theorem norm_sub_sq_equatorKernelApprox_le (f : TestFn) (n k : ℕ) :
    ‖equatorKernelApprox f n - equatorKernelApprox f k‖ ^ 2 ≤
      4 * (2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2)) *
        (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2)) := by
  let Q : ℕ → ℕ → ℝ := fun i j =>
    GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f i) (annularCenteredTestFn f j)
  let G : ℝ := gffCov f f
  have hnn : ‖equatorKernelApprox f n‖ ^ 2 = Q n n := by
    calc
      _ = ⟪equatorKernelApprox f n, equatorKernelApprox f n⟫_ℝ := by
        symm
        exact inner_self_eq_norm_sq_to_K _
      _ = Q n n := by
        simpa [Q] using inner_equatorKernelApprox_eq_pairing f f n n
  have hkk : ‖equatorKernelApprox f k‖ ^ 2 = Q k k := by
    calc
      _ = ⟪equatorKernelApprox f k, equatorKernelApprox f k⟫_ℝ := by
        symm
        exact inner_self_eq_norm_sq_to_K _
      _ = Q k k := by
        simpa [Q] using inner_equatorKernelApprox_eq_pairing f f k k
  have hnk : ⟪equatorKernelApprox f n, equatorKernelApprox f k⟫_ℝ = Q n k := by
    simpa [Q] using inner_equatorKernelApprox_eq_pairing f f n k
  have hexpand :
      ‖equatorKernelApprox f n - equatorKernelApprox f k‖ ^ 2 =
        (Q n n - G) + (Q k k - G) - 2 * (Q n k - G) := by
    rw [norm_sub_sq_real, hnn, hkk, hnk]
    dsimp [G]
    ring
  have herror (i j : ℕ) : |Q i j - G| ≤
      2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2) *
        (1 / ((i : ℝ) + 2) + 1 / ((j : ℝ) + 2)) := by
    simpa [Q, G] using abs_annularCenteredPairing_sub_gffCov_le f i j
  have htriangle :
      |(Q n n - G) + (Q k k - G) - 2 * (Q n k - G)| ≤
        |Q n n - G| + |Q k k - G| + 2 * |Q n k - G| := by
    calc
      _ = |((Q n n - G) + (Q k k - G)) + (-2 * (Q n k - G))| := by
        congr 1
        ring
      _ ≤ |(Q n n - G) + (Q k k - G)| + |-2 * (Q n k - G)| := abs_add_le _ _
      _ ≤ |Q n n - G| + |Q k k - G| + 2 * |Q n k - G| := by
        apply add_le_add
        · exact abs_add_le _ _
        · rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (Q n n - G) + (Q k k - G) - 2 * (Q n k - G) := hexpand
    _ ≤ |(Q n n - G) + (Q k k - G) - 2 * (Q n k - G)| := le_abs_self _
    _ ≤ |Q n n - G| + |Q k k - G| + 2 * |Q n k - G| := htriangle
    _ ≤ 2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2) *
          (1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 2)) +
        2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2) *
          (1 / ((k : ℝ) + 2) + 1 / ((k : ℝ) + 2)) +
        2 * (2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2) *
          (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2))) := by
        apply add_le_add
        · exact add_le_add (herror n n) (herror k k)
        · exact mul_le_mul_of_nonneg_left (herror n k) (by norm_num)
    _ = 4 * (2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2)) *
          (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2)) := by ring

theorem equatorKernelApprox_cauchy (f : TestFn) :
    CauchySeq (equatorKernelApprox f) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let C : ℝ := 2 * ((|testMass f| * ∫ z : ℂ, |f z|) + (testMass f) ^ 2)
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCplus : 0 < C + 1 := by linarith
  have hδ : Tendsto δ atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext j
    simp [δ, Nat.cast_add]
  let η := ε ^ 2 / (16 * (C + 1))
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) (by positivity)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hδ.eventually (gt_mem_nhds hη)))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hδm : δ m ≤ δ N := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast (Nat.add_le_add_right hm 2))
  have hδn : δ n ≤ δ N := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast (Nat.add_le_add_right hn 2))
  have hδN : δ N < η := hN N le_rfl
  have hnormsq := norm_sub_sq_equatorKernelApprox_le f m n
  have hsum : δ m + δ n ≤ 2 * δ N := by linarith
  have hnormsq' :
      ‖equatorKernelApprox f m - equatorKernelApprox f n‖ ^ 2 ≤
        8 * (C + 1) * δ N := by
    calc
      _ ≤ 4 * C * (δ m + δ n) := by
        simpa [C, δ] using hnormsq
      _ ≤ 4 * C * (2 * δ N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 4 * (C + 1) * (2 * δ N) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : C ≤ C + 1) (by norm_num))
          (by positivity)
      _ = 8 * (C + 1) * δ N := by ring
  have hsmall : 8 * (C + 1) * δ N < ε ^ 2 := by
    calc
      _ < 8 * (C + 1) * η :=
        mul_lt_mul_of_pos_left hδN (by positivity)
      _ = ε ^ 2 / 2 := by dsimp [η]; field_simp [ne_of_gt hCplus]; ring
      _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  have hnormlt : ‖equatorKernelApprox f m - equatorKernelApprox f n‖ < ε := by
    nlinarith [norm_nonneg (equatorKernelApprox f m - equatorKernelApprox f n)]
  simpa [dist_eq_norm] using hnormlt

/-- The limit of the rescaled annular kernels in the white-noise Hilbert space. -/
noncomputable def equatorKernelLimit (f : TestFn) :
    GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 :=
  limUnder atTop (equatorKernelApprox f)

theorem equatorKernelApprox_tendsto (f : TestFn) :
    Tendsto (equatorKernelApprox f) atTop (𝓝 (equatorKernelLimit f)) := by
  exact (equatorKernelApprox_cauchy f).tendsto_limUnder

/-- The finite-energy extension of the annular ABK kernel map to all test functions. -/
noncomputable def equatorKernelLimitMap :
    TestFn →ₗ[ℝ] GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 where
  toFun := equatorKernelLimit
  map_add' f g := by
    have hsum := (equatorKernelApprox_tendsto f).add (equatorKernelApprox_tendsto g)
    have hsum' : Tendsto (fun n => equatorKernelApprox (f + g) n) atTop
        (𝓝 (equatorKernelLimit f + equatorKernelLimit g)) := by
      convert hsum using 1
      funext n
      exact equatorKernelApprox_add f g n
    exact tendsto_nhds_unique (equatorKernelApprox_tendsto (f + g)) hsum'
  map_smul' a f := by
    have hsmul := ((continuous_const_smul a).tendsto (equatorKernelLimit f)).comp
      (equatorKernelApprox_tendsto f)
    have hsmul' : Tendsto (fun n => equatorKernelApprox (a • f) n) atTop
        (𝓝 (a • equatorKernelLimit f)) := by
      convert hsmul using 1
      funext n
      exact equatorKernelApprox_smul a f n
    exact tendsto_nhds_unique (equatorKernelApprox_tendsto (a • f)) hsmul'

/-- The equator-pinned field as an `L²`-valued real-linear map on test functions. -/
noncomputable def equatorFieldL2 :
    TestFn →ₗ[ℝ]
      Lp ℝ 2 (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) :=
  (GaussianFields.scaleSpaceWhiteNoiseL2 2).toLinearMap.comp equatorKernelLimitMap

theorem inner_equatorKernelLimitMap_eq_gffCov (f g : TestFn) :
    ⟪equatorKernelLimitMap f, equatorKernelLimitMap g⟫_ℝ = gffCov f g := by
  have hInner : Tendsto
      (fun n => ⟪equatorKernelApprox f n, equatorKernelApprox g n⟫_ℝ)
      atTop (𝓝 ⟪equatorKernelLimit f, equatorKernelLimit g⟫_ℝ) :=
    (equatorKernelApprox_tendsto f).inner (equatorKernelApprox_tendsto g)
  have hPair : Tendsto
      (fun n => GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g n))
      atTop (𝓝 ⟪equatorKernelLimitMap f, equatorKernelLimitMap g⟫_ℝ) := by
    have hEq : (fun n => ⟪equatorKernelApprox f n, equatorKernelApprox g n⟫_ℝ) =ᶠ[atTop]
        (fun n => GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn g n)) :=
      Filter.Eventually.of_forall fun n => inner_equatorKernelApprox_eq_pairing f g n n
    simpa [equatorKernelLimitMap] using hInner.congr' hEq
  exact tendsto_nhds_unique hPair (tendsto_annularCenteredPairing_gffCov f g)

/-- The covariance of the extended field evaluations is the DOZZ covariance `gffCov`. -/
theorem covariance_equatorFieldL2 (f g : TestFn) :
    cov[equatorFieldL2 f, equatorFieldL2 g;
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2] = gffCov f g := by
  change cov[
      GaussianFields.scaleSpaceWhiteNoiseL2 2 (equatorKernelLimitMap f),
      GaussianFields.scaleSpaceWhiteNoiseL2 2 (equatorKernelLimitMap g);
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2] = gffCov f g
  rw [GaussianFields.covariance_scaleSpaceWhiteNoiseL2]
  exact inner_equatorKernelLimitMap_eq_gffCov f g

/-- Every test evaluation is centered Gaussian with variance the diagonal DOZZ covariance. -/
theorem map_equatorFieldL2_eq_gaussianReal (f : TestFn) :
    Measure.map (equatorFieldL2 f) (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal (gffCov f f)) := by
  have hnorm :
      ‖equatorKernelLimitMap f‖ ^ 2 = gffCov f f := by
    calc
      _ = ⟪equatorKernelLimitMap f, equatorKernelLimitMap f⟫_ℝ := by
        symm
        exact inner_self_eq_norm_sq_to_K _
      _ = gffCov f f := inner_equatorKernelLimitMap_eq_gffCov f f
  change Measure.map
      (GaussianFields.scalarWhiteNoiseL2 3 (equatorKernelLimitMap f))
      (GaussianFields.scalarWhiteNoiseMeasure 3) =
    ProbabilityTheory.gaussianReal 0 (Real.toNNReal (gffCov f f))
  rw [GaussianFields.map_scalarWhiteNoiseL2_eq_gaussianReal, hnorm]


end DOZZ

end
