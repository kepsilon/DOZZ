/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.EnergyPositivity

/-!
# DOZZ.GFF.AnnularEnergyConvergence

Mixed-energy estimates for the smooth annular approximations to the equator law.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DOZZ

/-- The mixed raw-log energy of the `n`th and `k`th annular probability densities. -/
noncomputable def annularMixedEnergy (n k : ℕ) : ℝ :=
  ∫ q : ℂ × ℂ,
    annularProbabilityDensity n q.1 * annularProbabilityDensity k q.2 *
      (-Real.log ‖q.1 - q.2‖)
    ∂((volume : Measure ℂ).prod (volume : Measure ℂ))

/-- The mean-zero ABK pairing transports to a mixed complex logarithmic energy. -/
theorem abkLogCovariancePairing_eq_complex_pair
    (ψ φ : GaussianFields.MeanZeroTestFunction 2) :
    GaussianFields.abkLogCovariancePairing ψ φ =
      ∫ q : ℂ × ℂ,
        ψ (complexToVecTwo q.1) * φ (complexToVecTwo q.2) *
          (-Real.log ‖q.1 - q.2‖)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let ψC : ℂ → ℝ := fun z => ψ (complexLinearEquivVecTwo z)
  let φC : ℂ → ℝ := fun z => φ (complexLinearEquivVecTwo z)
  have hψC : Continuous ψC := ψ.continuous.comp complexLinearEquivVecTwo.continuous
  have hφC : Continuous φC := φ.continuous.comp complexLinearEquivVecTwo.continuous
  have hψCc : HasCompactSupport ψC :=
    ψ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph
  have hφCc : HasCompactSupport φC :=
    φ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph
  have hpair := integral_complexLogKernelPair_eq_vec ψC φC hψC hφC hψCc hφCc
  have hkernel (z w : ℂ) :
      GaussianFields.abkLogCovarianceKernel (complexToVecTwo z) (complexToVecTwo w) =
        -Real.log ‖z - w‖ := by
    rw [GaussianFields.abkLogCovarianceKernel, ← complexToVecTwo_sub z w]
    exact congrArg (fun t : ℝ => -Real.log t) (euclideanNorm_complexToVecTwo (z - w))
  have hback (z : ℂ) : complexLinearEquivVecTwo.symm (complexToVecTwo z) = z := by
    rw [← complexLinearEquivVecTwo_apply]
    simp
  have hψmap (z : ℂ) : ψC z = ψ (complexToVecTwo z) := by
    simp [ψC, complexLinearEquivVecTwo_apply]
  have hφmap (z : ℂ) : φC z = φ (complexToVecTwo z) := by
    simp [φC, complexLinearEquivVecTwo_apply]
  unfold GaussianFields.abkLogCovariancePairing GaussianFields.abkKernelPairing
  calc
    _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          ψC (complexLinearEquivVecTwo.symm p.1) *
            φC (complexLinearEquivVecTwo.symm p.2) *
            GaussianFields.abkLogCovarianceKernel p.1 p.2
          ∂((volume : Measure (GaussianFields.Vec 2)).prod
            (volume : Measure (GaussianFields.Vec 2))) := by
              apply integral_congr_ae
              filter_upwards with p
              simp [ψC, φC]
    _ = ∫ q : ℂ × ℂ,
          ψC q.1 * φC q.2 * (-Real.log ‖q.1 - q.2‖)
          ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := hpair.2.symm
    _ = ∫ q : ℂ × ℂ,
          ψ (complexToVecTwo q.1) * φ (complexToVecTwo q.2) *
            (-Real.log ‖q.1 - q.2‖)
          ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
            apply integral_congr_ae
            filter_upwards with q
            rw [hψmap q.1, hφmap q.2]

/-- The annular centered pairing for two tests and two annulus widths expands into the planar,
two mixed, and annular-annular logarithmic energies. -/
theorem annularCenteredPairing_eq_mixedExpansion (f g : TestFn) (n k : ℕ) :
    GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g k) =
      testFnLogPairing f g - testMass g * annularCrossEnergy f k -
        testMass f * annularCrossEnergy g n +
          testMass f * testMass g * annularMixedEnergy n k := by
  let m := testMass f
  let p := testMass g
  let ρn : ℂ → ℝ := annularProbabilityDensity n
  let ρk : ℂ → ℝ := annularProbabilityDensity k
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  let A : ℂ × ℂ → ℝ := fun q => f q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
  let B : ℂ × ℂ → ℝ := fun q => f q.1 * ρk q.2 * (-Real.log ‖q.1 - q.2‖)
  let C : ℂ × ℂ → ℝ := fun q => ρn q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
  let Cswap : ℂ × ℂ → ℝ := fun q => g q.1 * ρn q.2 * (-Real.log ‖q.1 - q.2‖)
  let D : ℂ × ℂ → ℝ := fun q => ρn q.1 * ρk q.2 * (-Real.log ‖q.1 - q.2‖)
  let h : ℂ → ℝ := fun z => f z - m * ρn z
  let j : ℂ → ℝ := fun z => g z - p * ρk z
  have hρnc := continuous_annularProbabilityDensity n
  have hρkc := continuous_annularProbabilityDensity k
  have hρncs := hasCompactSupport_annularProbabilityDensity n
  have hρkcs := hasCompactSupport_annularProbabilityDensity k
  have hhc : Continuous h := f.continuous.sub (hρnc.const_mul m)
  have hjc : Continuous j := g.continuous.sub (hρkc.const_mul p)
  have hhcs : HasCompactSupport h := by
    have hmul : HasCompactSupport (fun z : ℂ => m * ρn z) := by
      have hfun : (fun z : ℂ => m * ρn z) = (fun _ : ℂ => m) • ρn := by
        funext z
        simp [smul_eq_mul]
      rw [hfun]
      exact hρncs.smul_left (f := fun _ : ℂ => m)
    exact f.hasCompactSupport.sub hmul
  have hjcs : HasCompactSupport j := by
    have hmul : HasCompactSupport (fun z : ℂ => p * ρk z) := by
      have hfun : (fun z : ℂ => p * ρk z) = (fun _ : ℂ => p) • ρk := by
        funext z
        simp [smul_eq_mul]
      rw [hfun]
      exact hρkcs.smul_left (f := fun _ : ℂ => p)
    exact g.hasCompactSupport.sub hmul
  have hA0 := integral_complexLogKernelPair_eq_vec f g
    f.continuous g.continuous f.hasCompactSupport g.hasCompactSupport
  have hB0 := integral_complexLogKernelPair_eq_vec f ρk
    f.continuous hρkc f.hasCompactSupport hρkcs
  have hC0 := integral_complexLogKernelPair_eq_vec ρn g
    hρnc g.continuous hρncs g.hasCompactSupport
  have hCswap0 := integral_complexLogKernelPair_eq_vec g ρn
    g.continuous hρnc g.hasCompactSupport hρncs
  have hD0 := integral_complexLogKernelPair_eq_vec ρn ρk
    hρnc hρkc hρncs hρkcs
  have hAint : Integrable A μ := by simpa [A, μ] using hA0.1
  have hBint : Integrable B μ := by simpa [B, μ] using hB0.1
  have hCint : Integrable C μ := by simpa [C, μ] using hC0.1
  have hCswapInt : Integrable Cswap μ := by simpa [Cswap, μ] using hCswap0.1
  have hDint : Integrable D μ := by simpa [D, μ] using hD0.1
  have hHJ0 := integral_complexLogKernelPair_eq_vec h j hhc hjc hhcs hjcs
  have hHJint : Integrable
      (fun q : ℂ × ℂ => h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖)) μ := by
    simpa [μ] using hHJ0.1
  have hpB : Integrable (fun q => p * B q) μ := hBint.const_mul p
  have hmC : Integrable (fun q => m * C q) μ := hCint.const_mul m
  have hmpD : Integrable (fun q => m * p * D q) μ := hDint.const_mul (m * p)
  have hpoint (q : ℂ × ℂ) :
      h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖) =
        (A q - p * B q) - (m * C q - m * p * D q) := by
    simp [A, B, C, D, h, j, ρn, ρk, m, p]
    ring
  have hswap : ∫ q : ℂ × ℂ, C q ∂μ = ∫ q : ℂ × ℂ, Cswap q ∂μ := by
    calc
      _ = ∫ q : ℂ × ℂ, Cswap q.swap ∂μ := by
            apply integral_congr_ae
            filter_upwards with q
            dsimp [C, Cswap]
            rw [norm_sub_rev]
            ring
      _ = ∫ q : ℂ × ℂ, Cswap q ∂μ := integral_prod_swap Cswap
  have hBvalue : annularCrossEnergy f k = ∫ q : ℂ × ℂ, B q ∂μ := by
    rfl
  have hCvalue : annularCrossEnergy g n = ∫ q : ℂ × ℂ, Cswap q ∂μ := by
    rfl
  have hDvalue : annularMixedEnergy n k = ∫ q : ℂ × ℂ, D q ∂μ := by
    rfl
  have hpair := abkLogCovariancePairing_eq_complex_pair
    (annularCenteredTestFn f n) (annularCenteredTestFn g k)
  have hpair' :
      GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn g k) =
        ∫ q : ℂ × ℂ, h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖) ∂μ := by
    calc
      _ = ∫ q : ℂ × ℂ,
            annularCenteredTestFn f n (complexToVecTwo q.1) *
              annularCenteredTestFn g k (complexToVecTwo q.2) *
                (-Real.log ‖q.1 - q.2‖) ∂μ := by
          simpa [μ] using hpair
      _ = ∫ q : ℂ × ℂ, h q.1 * j q.2 *
            (-Real.log ‖q.1 - q.2‖) ∂μ := by
          apply integral_congr_ae
          filter_upwards with q
          rw [annularCenteredTestFn_complexValue, annularCenteredTestFn_complexValue]
  have hExpanded :
      (∫ q : ℂ × ℂ, h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖) ∂μ) =
        (∫ q : ℂ × ℂ, A q ∂μ) - p * (∫ q : ℂ × ℂ, B q ∂μ) -
          m * (∫ q : ℂ × ℂ, C q ∂μ) +
            m * p * (∫ q : ℂ × ℂ, D q ∂μ) := by
    calc
      _ = ∫ q : ℂ × ℂ, (A q - p * B q) - (m * C q - m * p * D q) ∂μ := by
            apply integral_congr_ae
            filter_upwards with q
            exact hpoint q
      _ = (∫ q : ℂ × ℂ, A q - p * B q ∂μ) -
            ∫ q : ℂ × ℂ, m * C q - m * p * D q ∂μ :=
          integral_sub (hAint.sub hpB) (hmC.sub hmpD)
      _ = _ := by
            rw [integral_sub hAint hpB, integral_sub hmC hmpD]
            simp only [integral_const_mul]
            ring
  have hAtest : testFnLogPairing f g = ∫ q : ℂ × ℂ, A q ∂μ := by
    simpa [A, μ] using testFnLogPairing_eq_complex f g
  rw [hpair', hExpanded, hswap, ← hAtest, ← hBvalue, ← hCvalue, ← hDvalue]

theorem integrable_annularMixedEnergyIntegrand (n k : ℕ) :
    Integrable
      (fun q : ℂ × ℂ =>
        annularProbabilityDensity n q.1 * annularProbabilityDensity k q.2 *
          (-Real.log ‖q.1 - q.2‖))
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  exact (integral_complexLogKernelPair_eq_vec
    (annularProbabilityDensity n) (annularProbabilityDensity k)
    (continuous_annularProbabilityDensity n) (continuous_annularProbabilityDensity k)
    (hasCompactSupport_annularProbabilityDensity n)
    (hasCompactSupport_annularProbabilityDensity k)).1

theorem abs_annularMixedEnergy_le (n k : ℕ) :
    |annularMixedEnergy n k| ≤
      1 / ((n : ℝ) + 2) + 2 / ((k : ℝ) + 2) := by
  let ρ : ℂ → ℝ := annularProbabilityDensity n
  let V : ℂ → ℝ := annularLogPotential k
  let μ : Measure ℂ := volume
  let c : ℝ := 1 / ((n : ℝ) + 2) + 2 / ((k : ℝ) + 2)
  have hPair := integral_logKernel_annular ρ
    (continuous_annularProbabilityDensity n)
    (hasCompactSupport_annularProbabilityDensity n) k
  have hVInt : Integrable (fun z : ℂ => ρ z * V z) μ := by
    simpa [ρ, V, μ, annularLogPotential] using hPair.1
  have hρInt : Integrable ρ μ := by
    simpa [ρ, μ] using integrable_annularProbabilityDensity n
  have hρMass : ∫ z : ℂ, ρ z ∂μ = 1 := by
    simpa [ρ, μ] using integral_annularProbabilityDensity n
  have hD : annularMixedEnergy n k = -(∫ z : ℂ, ρ z * V z ∂μ) := by
    simpa [annularMixedEnergy, ρ, V, μ, annularLogPotential] using hPair.2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hUpperInt : Integrable (fun z : ℂ => c * ρ z) μ := hρInt.const_mul c
  have hPointwise (z : ℂ) : |ρ z * V z| ≤ c * ρ z := by
    by_cases hzero : ρ z = 0
    · simp [hzero]
    · have hρnonneg : 0 ≤ ρ z := annularProbabilityDensity_nonneg n z
      have hlog := abs_logPlus_of_annularDensity_ne_zero n z (by simpa [ρ] using hzero)
      have hpotential := abs_annularLogPotential_sub_logPlus k z
      have hpot : |V z - Real.log (max 1 ‖z‖)| ≤ 2 / ((k : ℝ) + 2) := by
        simpa [V] using hpotential
      have hV : |V z| ≤ c := by
        have htri : |V z| ≤ |V z - Real.log (max 1 ‖z‖)| +
            |Real.log (max 1 ‖z‖)| := by
          calc
            |V z| = |(V z - Real.log (max 1 ‖z‖)) +
                Real.log (max 1 ‖z‖)| := by congr 1; ring
            _ ≤ |V z - Real.log (max 1 ‖z‖)| +
                |Real.log (max 1 ‖z‖)| := abs_add_le _ _
        have hbound : |V z| ≤
            2 / ((k : ℝ) + 2) + 1 / ((n : ℝ) + 2) := by
          calc
            |V z| ≤ |V z - Real.log (max 1 ‖z‖)| +
                |Real.log (max 1 ‖z‖)| := htri
            _ ≤ 2 / ((k : ℝ) + 2) + 1 / ((n : ℝ) + 2) := add_le_add hpot hlog
        simpa [c, add_comm] using hbound
      rw [abs_mul, abs_of_nonneg hρnonneg]
      calc
        ρ z * |V z| ≤ ρ z * c := mul_le_mul_of_nonneg_left hV hρnonneg
        _ = c * ρ z := by ring
  calc
    |annularMixedEnergy n k| = |∫ z : ℂ, ρ z * V z ∂μ| := by rw [hD, abs_neg]
    _ ≤ ∫ z : ℂ, |ρ z * V z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℂ, c * ρ z ∂μ := by
      apply integral_mono_ae hVInt.norm hUpperInt
      filter_upwards with z
      exact hPointwise z
    _ = c := by rw [integral_const_mul, hρMass]; ring
    _ = _ := rfl

/-- The mixed annular centered energies converge quantitatively to the pinned covariance. -/
theorem abs_annularCenteredPairing_sub_gffCov_le (f : TestFn) (n k : ℕ) :
    |GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn f k) - gffCov f f| ≤
      (2 * (|testMass f| * (∫ z : ℂ, |f z|) + (testMass f) ^ 2)) *
        (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2)) := by
  let m : ℝ := testMass f
  let L : ℝ := ∫ z : ℂ, |f z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  let Q : ℕ → ℕ → ℝ := fun i j =>
    GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f i) (annularCenteredTestFn f j)
  let C : ℝ := 2 * (|m| * L + m ^ 2)
  have hCovExpansion : gffCov f f = testFnLogPairing f f + 2 * m * testFnPotential f := by
    rw [gffCov_eq_equatorLogEnergy]
    dsimp [m]
    ring
  have hQ : Q n k = testFnLogPairing f f - m * annularCrossEnergy f k -
      m * annularCrossEnergy f n + m ^ 2 * annularMixedEnergy n k := by
    dsimp [Q]
    rw [annularCenteredPairing_eq_mixedExpansion f f n k]
    dsimp [m]
    ring
  have hCrossN := abs_annularCrossEnergy_add_testFnPotential f n
  have hCrossK := abs_annularCrossEnergy_add_testFnPotential f k
  have hMixed := abs_annularMixedEnergy_le n k
  have hDiff : Q n k - gffCov f f =
      -m * (annularCrossEnergy f k + testFnPotential f) -
        m * (annularCrossEnergy f n + testFnPotential f) +
          m ^ 2 * annularMixedEnergy n k := by
    rw [hQ, hCovExpansion]
    ring
  have hCoeff : |-m| = |m| := by simp
  have hCrossN' : |annularCrossEnergy f n + testFnPotential f| ≤
      2 * δ n * L := by
    calc
      _ ≤ 2 / ((n : ℝ) + 2) * ∫ z : ℂ, |f z| := hCrossN
      _ = 2 * δ n * L := by dsimp [δ, L]; ring
  have hCrossK' : |annularCrossEnergy f k + testFnPotential f| ≤
      2 * δ k * L := by
    calc
      _ ≤ 2 / ((k : ℝ) + 2) * ∫ z : ℂ, |f z| := hCrossK
      _ = 2 * δ k * L := by dsimp [δ, L]; ring
  have hMixed' : |annularMixedEnergy n k| ≤ δ n + 2 * δ k := by
    calc
      _ ≤ 1 / ((n : ℝ) + 2) + 2 / ((k : ℝ) + 2) := hMixed
      _ = δ n + 2 * δ k := by dsimp [δ]; ring
  calc
    |Q n k - gffCov f f| =
        |-m * (annularCrossEnergy f k + testFnPotential f) -
          m * (annularCrossEnergy f n + testFnPotential f) +
            m ^ 2 * annularMixedEnergy n k| := by rw [hDiff]
    _ ≤ |m| * |annularCrossEnergy f k + testFnPotential f| +
          |m| * |annularCrossEnergy f n + testFnPotential f| +
            m ^ 2 * |annularMixedEnergy n k| := by
        calc
          _ ≤ |-m * (annularCrossEnergy f k + testFnPotential f) -
                m * (annularCrossEnergy f n + testFnPotential f)| +
                  |m ^ 2 * annularMixedEnergy n k| := by
                simpa only [sub_eq_add_neg] using abs_add_le
                  (-m * (annularCrossEnergy f k + testFnPotential f) -
                    m * (annularCrossEnergy f n + testFnPotential f))
                  (m ^ 2 * annularMixedEnergy n k)
          _ ≤ |-m * (annularCrossEnergy f k + testFnPotential f)| +
                |m * (annularCrossEnergy f n + testFnPotential f)| +
                  |m ^ 2 * annularMixedEnergy n k| := by
                have hAB :
                    |-m * (annularCrossEnergy f k + testFnPotential f) -
                      m * (annularCrossEnergy f n + testFnPotential f)| ≤
                    |-m * (annularCrossEnergy f k + testFnPotential f)| +
                      |m * (annularCrossEnergy f n + testFnPotential f)| := by
                  calc
                    _ = |-m * (annularCrossEnergy f k + testFnPotential f) +
                          -(m * (annularCrossEnergy f n + testFnPotential f))| := by
                            congr 1
                    _ ≤ _ := abs_add_le _ _
                    _ = _ := by rw [abs_neg]
                exact add_le_add hAB le_rfl
          _ = _ := by rw [abs_mul, hCoeff, abs_mul, abs_mul,
                abs_of_nonneg (sq_nonneg m)]
    _ ≤ |m| * (2 * δ k * L) + |m| * (2 * δ n * L) +
          m ^ 2 * (δ n + 2 * δ k) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hCrossK' (abs_nonneg m)
          · exact mul_le_mul_of_nonneg_left hCrossN' (abs_nonneg m)
        · exact mul_le_mul_of_nonneg_left hMixed' (sq_nonneg m)
    _ ≤ C * (δ n + δ k) := by
        have hδn : 0 ≤ δ n := by dsimp [δ]; positivity
        have hdouble : m ^ 2 * δ n ≤ 2 * m ^ 2 * δ n := by
          calc
            _ = m ^ 2 * δ n + 0 := by ring
            _ ≤ m ^ 2 * δ n + m ^ 2 * δ n :=
              add_le_add le_rfl (mul_nonneg (sq_nonneg m) hδn)
            _ = _ := by ring
        calc
          |m| * (2 * δ k * L) + |m| * (2 * δ n * L) +
              m ^ 2 * (δ n + 2 * δ k) =
            2 * (|m| * L) * (δ n + δ k) + m ^ 2 * δ n + 2 * m ^ 2 * δ k := by
              ring
          _ ≤ 2 * (|m| * L) * (δ n + δ k) + 2 * m ^ 2 * δ n +
                2 * m ^ 2 * δ k := by
              exact add_le_add_left
                (add_le_add_right hdouble (2 * (|m| * L) * (δ n + δ k))) _
          _ = 2 * (|m| * L + m ^ 2) * (δ n + δ k) := by ring
          _ = C * (δ n + δ k) := by dsimp [C]
    _ = _ := by
        dsimp [C, δ, m, L]

/-- The mixed annular centered pairing converges quantitatively to the full pinned covariance. -/
theorem abs_annularCenteredPairing_sub_gffCov_le_mixed
    (f g : TestFn) (n k : ℕ) :
    |GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g k) - gffCov f g| ≤
      (2 * (|testMass g| * (∫ z : ℂ, |f z|) +
        |testMass f| * (∫ z : ℂ, |g z|) +
        |testMass f * testMass g|)) *
        (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2)) := by
  let m : ℝ := testMass f
  let p : ℝ := testMass g
  let Lf : ℝ := ∫ z : ℂ, |f z|
  let Lg : ℝ := ∫ z : ℂ, |g z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  let Q : ℕ → ℕ → ℝ := fun i j =>
    GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f i) (annularCenteredTestFn g j)
  let C : ℝ := 2 * (|p| * Lf + |m| * Lg + |m * p|)
  have hCovExpansion :
      gffCov f g = testFnLogPairing f g + testFnPotential f * p +
        m * testFnPotential g := by
    rw [gffCov_eq_equatorLogEnergy]
  have hQ : Q n k = testFnLogPairing f g - p * annularCrossEnergy f k -
      m * annularCrossEnergy g n + m * p * annularMixedEnergy n k := by
    dsimp [Q]
    rw [annularCenteredPairing_eq_mixedExpansion f g n k]
  have hDiff : Q n k - gffCov f g =
      -p * (annularCrossEnergy f k + testFnPotential f) -
        m * (annularCrossEnergy g n + testFnPotential g) +
          m * p * annularMixedEnergy n k := by
    rw [hQ, hCovExpansion]
    ring
  have hLf : 0 ≤ Lf := by
    dsimp [Lf]
    exact integral_nonneg (fun z => abs_nonneg (f z))
  have hLg : 0 ≤ Lg := by
    dsimp [Lg]
    exact integral_nonneg (fun z => abs_nonneg (g z))
  have hCrossf := abs_annularCrossEnergy_add_testFnPotential f k
  have hCrossg := abs_annularCrossEnergy_add_testFnPotential g n
  have hMixed := abs_annularMixedEnergy_le n k
  have hCrossf' : |annularCrossEnergy f k + testFnPotential f| ≤
      2 * δ k * Lf := by
    calc
      _ ≤ 2 / ((k : ℝ) + 2) * ∫ z : ℂ, |f z| := hCrossf
      _ = 2 * δ k * Lf := by dsimp [δ, Lf]; ring
  have hCrossg' : |annularCrossEnergy g n + testFnPotential g| ≤
      2 * δ n * Lg := by
    calc
      _ ≤ 2 / ((n : ℝ) + 2) * ∫ z : ℂ, |g z| := hCrossg
      _ = 2 * δ n * Lg := by dsimp [δ, Lg]; ring
  have hMixed' : |annularMixedEnergy n k| ≤ δ n + 2 * δ k := by
    calc
      _ ≤ 1 / ((n : ℝ) + 2) + 2 / ((k : ℝ) + 2) := hMixed
      _ = δ n + 2 * δ k := by dsimp [δ]; ring
  have hCoeffK : 2 * |p| * Lf + 2 * |m * p| ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ |m| * Lg := mul_nonneg (abs_nonneg m) hLg
    linarith
  have hCoeffN : 2 * |m| * Lg + |m * p| ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ |p| * Lf := mul_nonneg (abs_nonneg p) hLf
    have hnonneg' : 0 ≤ |m * p| := abs_nonneg _
    linarith
  have hδn : 0 ≤ δ n := by dsimp [δ]; positivity
  have hδk : 0 ≤ δ k := by dsimp [δ]; positivity
  calc
    |Q n k - gffCov f g| =
        |-p * (annularCrossEnergy f k + testFnPotential f) -
          m * (annularCrossEnergy g n + testFnPotential g) +
            m * p * annularMixedEnergy n k| := by rw [hDiff]
    _ ≤ |p| * |annularCrossEnergy f k + testFnPotential f| +
          |m| * |annularCrossEnergy g n + testFnPotential g| +
            |m * p| * |annularMixedEnergy n k| := by
        calc
          _ ≤ |-p * (annularCrossEnergy f k + testFnPotential f) -
                m * (annularCrossEnergy g n + testFnPotential g)| +
                  |m * p * annularMixedEnergy n k| := by
                simpa only [sub_eq_add_neg] using abs_add_le
                  (-p * (annularCrossEnergy f k + testFnPotential f) -
                    m * (annularCrossEnergy g n + testFnPotential g))
                  (m * p * annularMixedEnergy n k)
          _ ≤ |-p * (annularCrossEnergy f k + testFnPotential f)| +
                |m * (annularCrossEnergy g n + testFnPotential g)| +
                  |m * p * annularMixedEnergy n k| := by
                have hab :
                    |-p * (annularCrossEnergy f k + testFnPotential f) -
                      m * (annularCrossEnergy g n + testFnPotential g)| ≤
                    |-p * (annularCrossEnergy f k + testFnPotential f)| +
                      |m * (annularCrossEnergy g n + testFnPotential g)| := by
                  calc
                    _ = |-p * (annularCrossEnergy f k + testFnPotential f) +
                          -(m * (annularCrossEnergy g n + testFnPotential g))| := by
                            congr 1
                    _ ≤ _ := abs_add_le _ _
                    _ = _ := by rw [abs_neg]
                exact add_le_add hab le_rfl
          _ = _ := by
                rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul]
    _ ≤ |p| * (2 * δ k * Lf) + |m| * (2 * δ n * Lg) +
          |m * p| * (δ n + 2 * δ k) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hCrossf' (abs_nonneg p)
          · exact mul_le_mul_of_nonneg_left hCrossg' (abs_nonneg m)
        · exact mul_le_mul_of_nonneg_left hMixed' (abs_nonneg (m * p))
    _ ≤ C * (δ n + δ k) := by
        calc
          _ = (2 * |m| * Lg + |m * p|) * δ n +
                (2 * |p| * Lf + 2 * |m * p|) * δ k := by ring
          _ ≤ C * δ n + C * δ k := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_right hCoeffN hδn
                · exact mul_le_mul_of_nonneg_right hCoeffK hδk
          _ = C * (δ n + δ k) := by ring
    _ = _ := by dsimp [C, δ, m, p, Lf, Lg]

/-- The diagonal sequence of mixed annular pairings converges to the pinned covariance. -/
theorem tendsto_annularCenteredPairing_gffCov (f g : TestFn) :
    Tendsto
      (fun n => GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g n))
      atTop (𝓝 (gffCov f g)) := by
  let m : ℝ := testMass f
  let p : ℝ := testMass g
  let Lf : ℝ := ∫ z : ℂ, |f z|
  let Lg : ℝ := ∫ z : ℂ, |g z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  let Q : ℕ → ℝ := fun j => GaussianFields.abkLogCovariancePairing
    (annularCenteredTestFn f j) (annularCenteredTestFn g j)
  let C : ℝ := 2 * (|p| * Lf + |m| * Lg + |m * p|)
  let B : ℕ → ℝ := fun j => C * (δ j + δ j)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext j
    simp [δ, Nat.cast_add]
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa [B] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul (hδ.add hδ)
  have hconst : Tendsto (fun _ : ℕ => gffCov f g) atTop (𝓝 (gffCov f g)) :=
    tendsto_const_nhds
  have hlow : Tendsto (fun j => gffCov f g - B j) atTop (𝓝 (gffCov f g)) := by
    simpa [sub_eq_add_neg, add_comm] using hconst.add hB.neg
  have hupp : Tendsto (fun j => gffCov f g + B j) atTop (𝓝 (gffCov f g)) := by
    simpa using hconst.add hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro j
    have h := abs_le.mp (abs_annularCenteredPairing_sub_gffCov_le_mixed f g j j)
    dsimp [Q, B, δ, C, m, p, Lf, Lg]
    linarith
  · intro j
    have h := abs_le.mp (abs_annularCenteredPairing_sub_gffCov_le_mixed f g j j)
    dsimp [Q, B, δ, C, m, p, Lf, Lg]
    linarith

end DOZZ

end
