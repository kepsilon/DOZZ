/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.KahaneNegativeMellin
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Bounded Laplace tests pass field-chaos Kahane comparisons through convergence in measure. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A field-chaos Laplace comparison passes to limits in measure. The two probability spaces use
a common subsequence, and bounded convergence transfers the cutoff inequalities to the limits. -/
theorem kahane_limit_field_laplace
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, DOZZ.IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, DOZZ.IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ t : ℝ) (ht : 0 ≤ t)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZX ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZY ω)) ∂PY := by
  classical
  let fX : ℝ → ΩX → ℝ := fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal
  let fY : ℝ → ΩY → ℝ := fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal
  have hXnat : TendstoInMeasure PX (fun n : ℕ => fX n) atTop ZX :=
    hXconv.comp tendsto_natCast_atTop_atTop
  obtain ⟨ns, hns, hXae⟩ := hXnat.exists_seq_tendsto_ae
  have hYnat : TendstoInMeasure PY (fun n : ℕ => fY n) atTop ZY :=
    hYconv.comp tendsto_natCast_atTop_atTop
  have hYsub : TendstoInMeasure PY (fun n : ℕ => fY (ns n)) atTop ZY :=
    hYnat.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hYae⟩ := hYsub.exists_seq_tendsto_ae
  have hXseq : ∀ᵐ ω ∂PX, Tendsto (fun n => fX (ns (ms n)) ω) atTop (𝓝 (ZX ω)) := by
    filter_upwards [hXae] with ω hω
    exact hω.comp hms.tendsto_atTop
  have hYseq : ∀ᵐ ω ∂PY, Tendsto (fun n => fY (ns (ms n)) ω) atTop (𝓝 (ZY ω)) := by
    filter_upwards [hYae] with ω hω
    exact hω
  have hzeroX := hΦ 0
  have hzeroY := hΨ 0
  let : IsProbabilityMeasure PX := hzeroX.2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let : IsProbabilityMeasure PY := hzeroY.2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hLap (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * fX r ω)) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * fY r ω)) ∂PY := by
    by_cases hνzero : ν = 0
    · have hmassX (ω : ΩX) : DOZZ.fieldChaosMass PX (Φ r) ν h γ ω = 0 := by
        simp [DOZZ.fieldChaosMass, hνzero]
      have hmassY (ω : ΩY) : DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω = 0 := by
        simp [DOZZ.fieldChaosMass, hνzero]
      simp [fX, fY, hmassX, hmassY]
    · have hS : Nonempty S := by
        have hUniv : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνzero
        obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
        exact ⟨x⟩
      let : Nonempty S := hS
      have hcov' : ∀ᵐ xy ∂(νf : Measure S).prod νf,
          DOZZ.gaussianCovariance PX (fun ω => Φ r ω xy.1) (fun ω => Φ r ω xy.2) ≤
            DOZZ.gaussianCovariance PY (fun ω => Ψ r ω xy.1) (fun ω => Ψ r ω xy.2) := by
        filter_upwards [hcov r] with xy hxy
        simpa [DOZZ.gaussianCovariance] using hxy
      have hdiag' : ∀ᵐ x ∂(νf : Measure S),
          DOZZ.gaussianVariance PX (fun ω => Φ r ω x) ≤
            DOZZ.gaussianVariance PY (fun ω => Ψ r ω x) := by
        filter_upwards [hdiag r] with x hx
        simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx
      simpa [fX, fY, νf] using
        kahane_field_laplace_of_nonzero_finite_measure_eq PX PY (Φ r) (Ψ r)
          (hΦ r) (hΨ r) νf (by
            intro hz
            apply hνzero
            have hcoerce := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hz
            simpa [νf] using hcoerce)
          h hh hhb γ t ht hcov' hdiag'
  let FX : ℕ → ΩX → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.exp (-t * fX (ns (ms n)) ω))
  let FY : ℕ → ΩY → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.exp (-t * fY (ns (ms n)) ω))
  have hFXmeas : ∀ n, Measurable (FX n) := by
    intro n
    dsimp [FX, fX]
    exact ENNReal.measurable_ofReal.comp <| Real.measurable_exp.comp <|
      (measurable_const.mul <|
        (centeredGaussianField_fieldChaosMass_measurable PX (Φ (ns (ms n)))
          (hΦ (ns (ms n))) ν h hh γ).ennreal_toReal)
  have hFYmeas : ∀ n, Measurable (FY n) := by
    intro n
    dsimp [FY, fY]
    exact ENNReal.measurable_ofReal.comp <| Real.measurable_exp.comp <|
      (measurable_const.mul <|
        (centeredGaussianField_fieldChaosMass_measurable PY (Ψ (ns (ms n)))
          (hΨ (ns (ms n))) ν h hh γ).ennreal_toReal)
  have hFXbound : ∀ n, ∀ᵐ ω ∂PX, FX n ω ≤ 1 := by
    intro n
    filter_upwards [] with ω
    rw [ENNReal.ofReal_le_one]
    apply Real.exp_le_one_iff.mpr
    have hm : 0 ≤ fX (ns (ms n)) ω := ENNReal.toReal_nonneg
    nlinarith [mul_nonneg ht hm]
  have hFYbound : ∀ n, ∀ᵐ ω ∂PY, FY n ω ≤ 1 := by
    intro n
    filter_upwards [] with ω
    rw [ENNReal.ofReal_le_one]
    apply Real.exp_le_one_iff.mpr
    have hm : 0 ≤ fY (ns (ms n)) ω := ENNReal.toReal_nonneg
    nlinarith [mul_nonneg ht hm]
  have hfiniteX : ∫⁻ ω : ΩX, (1 : ℝ≥0∞) ∂PX ≠ ∞ := by simp
  have hfiniteY : ∫⁻ ω : ΩY, (1 : ℝ≥0∞) ∂PY ≠ ∞ := by simp
  let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-t * x))
  have hgcont : Continuous g := by
    dsimp [g]
    exact ENNReal.continuous_ofReal.comp <|
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFXlim : ∀ᵐ ω ∂PX, Tendsto (fun n => FX n ω) atTop (𝓝 (g (ZX ω))) := by
    filter_upwards [hXseq] with ω hω
    exact hgcont.continuousAt.tendsto.comp hω
  have hFYlim : ∀ᵐ ω ∂PY, Tendsto (fun n => FY n ω) atTop (𝓝 (g (ZY ω))) := by
    filter_upwards [hYseq] with ω hω
    exact hgcont.continuousAt.tendsto.comp hω
  have hXint := tendsto_lintegral_of_dominated_convergence
    (fun _ : ΩX => (1 : ℝ≥0∞)) hFXmeas hFXbound hfiniteX hFXlim
  have hYint := tendsto_lintegral_of_dominated_convergence
    (fun _ : ΩY => (1 : ℝ≥0∞)) hFYmeas hFYbound hfiniteY hFYlim
  have horder : ∀ n, ∫⁻ ω, FX n ω ∂PX ≤ ∫⁻ ω, FY n ω ∂PY := by
    intro n
    simpa [FX, FY, fX, fY] using hLap (ns (ms n))
  have hlimorder := le_of_tendsto_of_tendsto hXint hYint
    (Filter.Eventually.of_forall horder)
  simpa [g] using hlimorder

/-- Negative-power field comparison passes to limits in measure. The finite-cutoff comparison is
first transferred to bounded Laplace tests, then Mellin integration recovers the possibly infinite
negative moments of the limiting masses. -/
theorem kahane_limit_field_negative_power
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, DOZZ.IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, DOZZ.IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ q : ℝ) (hq : 0 < q)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX ≤
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY := by
  classical
  have hPXprob : IsProbabilityMeasure PX :=
    (hΦ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  have hPYprob : IsProbabilityMeasure PY :=
    (hΨ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let : IsProbabilityMeasure PX := hPXprob
  let : IsProbabilityMeasure PY := hPYprob
  let fX : ℝ → ΩX → ℝ := fun r ω =>
    (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal
  let fY : ℝ → ΩY → ℝ := fun r ω =>
    (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal
  have hfXmeas (r : ℝ) : AEMeasurable (fX r) PX :=
    (centeredGaussianField_fieldChaosMass_measurable PX (Φ r) (hΦ r) ν h hh γ)
      |>.ennreal_toReal.aemeasurable
  have hfYmeas (r : ℝ) : AEMeasurable (fY r) PY :=
    (centeredGaussianField_fieldChaosMass_measurable PY (Ψ r) (hΨ r) ν h hh γ)
      |>.ennreal_toReal.aemeasurable
  have hZXae : AEMeasurable ZX PX := hXconv.aemeasurable hfXmeas
  have hZYae : AEMeasurable ZY PY := hYconv.aemeasurable hfYmeas
  have hXnat : TendstoInMeasure PX (fun n : ℕ => fX n) atTop ZX :=
    hXconv.comp tendsto_natCast_atTop_atTop
  obtain ⟨ns, hns, hXae⟩ := hXnat.exists_seq_tendsto_ae
  have hYnat : TendstoInMeasure PY (fun n : ℕ => fY n) atTop ZY :=
    hYconv.comp tendsto_natCast_atTop_atTop
  have hYsub : TendstoInMeasure PY (fun n : ℕ => fY (ns n)) atTop ZY :=
    hYnat.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hYae⟩ := hYsub.exists_seq_tendsto_ae
  have hXseq : ∀ᵐ ω ∂PX, Tendsto (fun n => fX (ns (ms n)) ω) atTop (𝓝 (ZX ω)) := by
    filter_upwards [hXae] with ω hω
    exact hω.comp hms.tendsto_atTop
  have hYseq : ∀ᵐ ω ∂PY, Tendsto (fun n => fY (ns (ms n)) ω) atTop (𝓝 (ZY ω)) := by
    filter_upwards [hYae] with ω hω
    exact hω
  have hZXnonneg : ∀ᵐ ω ∂PX, 0 ≤ ZX ω := by
    filter_upwards [hXseq] with ω hω
    exact isClosed_Ici.mem_of_tendsto hω
      (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  have hZYnonneg : ∀ᵐ ω ∂PY, 0 ≤ ZY ω := by
    filter_upwards [hYseq] with ω hω
    exact isClosed_Ici.mem_of_tendsto hω
      (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  let mX : ΩX → ℝ := fun ω => max (ZX ω) 0
  let mY : ΩY → ℝ := fun ω => max (ZY ω) 0
  have hmX : ∀ ω, 0 ≤ mX ω := fun ω => le_max_right _ _
  have hmY : ∀ ω, 0 ≤ mY ω := fun ω => le_max_right _ _
  have hmXae : AEMeasurable mX PX := by
    exact hZXae.max measurable_const.aemeasurable
  have hmYae : AEMeasurable mY PY := by
    exact hZYae.max measurable_const.aemeasurable
  have hmXeq : mX =ᵐ[PX] ZX := by
    filter_upwards [hZXnonneg] with ω hω
    simp [mX, max_eq_left hω]
  have hmYeq : mY =ᵐ[PY] ZY := by
    filter_upwards [hZYnonneg] with ω hω
    simp [mY, max_eq_left hω]
  have hLapLimit (t : ℝ) (ht : 0 < t) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZX ω)) ∂PX := by
            apply lintegral_congr_ae
            filter_upwards [hmXeq] with ω hω
            congr 2
            rw [hω]
            ring
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZY ω)) ∂PY :=
        kahane_limit_field_laplace PX PY Φ Ψ hΦ hΨ ν h hh hhb γ t
          (le_of_lt ht) hcov hdiag ZX ZY hXconv hYconv
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY := by
            apply lintegral_congr_ae
            filter_upwards [hmYeq] with ω hω
            congr 2
            rw [hω]
            ring
  have hMellinX := nonneg_rpow_neg_lintegral_eq_weighted_laplace
    PX mX hmX hmXae q hq
  have hMellinY := nonneg_rpow_neg_lintegral_eq_weighted_laplace
    PY mY hmY hmYae q hq
  have hweighted :
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume ≤
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_left (hLapLimit t ht)
      (by positivity)
  have hMomentX :
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX =
        ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) (-q) ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hmXeq] with ω hω
    rw [hω]
  have hMomentY :
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY =
        ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) (-q) ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hmYeq] with ω hω
    rw [hω]
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX =
        ENNReal.ofReal (1 / Real.Gamma q) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume :=
          hMomentX.trans hMellinX
    _ ≤ ENNReal.ofReal (1 / Real.Gamma q) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume :=
          mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY :=
          (hMomentY.trans hMellinY).symm


end DOZZ.Proofs
