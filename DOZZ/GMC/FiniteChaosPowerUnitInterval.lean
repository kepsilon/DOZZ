/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosNegativePower
public import DOZZ.GMC.FiniteChaosMean
public import DOZZ.GMC.FiniteChaosResolvent
public import DOZZ.Statements.GMC.FiniteChaosMoment
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! Fractional finite-chaos power comparisons from the Laplace order. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Distributions ENNReal

namespace DOZZ.Proofs

private theorem finiteChaosMass_measurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : DOZZ.IsCenteredJointlyGaussian P Z)
    (a : ι → ℝ) (γ : ℝ) :
    AEMeasurable (fun ω => DOZZ.finiteChaosMass P Z a γ ω) P := by
  classical
  have hterm (i : ι) : AEMeasurable
      (fun ω => a i * Real.exp (γ * Z ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω i))) P := by
    have harg : AEMeasurable (fun ω => γ * Z ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω i)) P :=
      (hZ.2.1 i).const_mul γ |>.sub_const _
    exact (Real.measurable_exp.comp_aemeasurable harg).const_mul (a i)
  change AEMeasurable (fun ω => ∑ i,
    a i * Real.exp (γ * Z ω i - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Z ω i))) P
  exact Finset.aemeasurable_fun_sum _ fun i _ => hterm i

private theorem finiteChaosMass_nonneg
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (γ : ℝ) (ω : Ω) :
    0 ≤ DOZZ.finiteChaosMass P Z a γ ω := by
  classical
  unfold DOZZ.finiteChaosMass
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (ha i) (Real.exp_nonneg _)

private theorem finiteChaosMass_pos_of_pos_weight
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hapos : ∃ i, 0 < a i) (γ : ℝ) (ω : Ω) :
    0 < DOZZ.finiteChaosMass P Z a γ ω := by
  classical
  obtain ⟨i, hai⟩ := hapos
  have hterms : ∀ j, 0 ≤ a j * Real.exp
      (γ * Z ω j - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω j)) :=
    fun j => mul_nonneg (ha j) (Real.exp_nonneg _)
  have hterm : 0 < a i * Real.exp
      (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i)) :=
    mul_pos hai (Real.exp_pos _)
  unfold DOZZ.finiteChaosMass
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_univ i))

/-- Kahane's concave power comparison for `0 < p < 1`, derived from the Laplace comparison via
the Stieltjes representation of `x^p`. -/
theorem kahane_finite_power_concave
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ p : ℝ)
    (hp : 0 < p ∧ p < 1)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ p ≥ DOZZ.finiteChaosMoment PY Y a γ p := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  by_cases hapos : ∃ i, 0 < a i
  · let mX : ΩX → ℝ := DOZZ.finiteChaosMass PX X a γ
    let mY : ΩY → ℝ := DOZZ.finiteChaosMass PY Y a γ
    have hmX : AEMeasurable mX PX := finiteChaosMass_measurable PX X hX a γ
    have hmY : AEMeasurable mY PY := finiteChaosMass_measurable PY Y hY a γ
    have hmX0 : ∀ ω, 0 ≤ mX ω := finiteChaosMass_nonneg PX X a ha γ
    have hmY0 : ∀ ω, 0 ≤ mY ω := finiteChaosMass_nonneg PY Y a ha γ
    have hmXpos : ∀ ω, 0 < mX ω :=
      finiteChaosMass_pos_of_pos_weight PX X a ha hapos γ
    have hmYpos : ∀ ω, 0 < mY ω :=
      finiteChaosMass_pos_of_pos_weight PY Y a ha hapos γ
    have hLap (s : ℝ) (hs : 0 ≤ s) :
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mX ω))) ∂PX ≤
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mY ω))) ∂PY := by
      have h := kahane_finite_laplace_lintegral_fintype PX PY X Y hX hY a ha γ s hs hcov
      have hXexp : (fun ω => Real.exp (-s * mX ω)) =
          fun ω => Real.exp (-(s * mX ω)) := by
        funext ω
        congr 1
        ring
      have hYexp : (fun ω => Real.exp (-s * mY ω)) =
          fun ω => Real.exp (-(s * mY ω)) := by
        funext ω
        congr 1
        ring
      simpa [mX, mY, hXexp, hYexp] using h
    let c : ℝ := (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1 ∂volume)⁻¹
    have hcpos : 0 < c := by
      dsimp [c]
      exact inv_pos.mpr (Real.integral_rpowIntegrand₀₁_one_pos ⟨hp.1, hp.2⟩)
    let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
    let fX : ΩX → ℝ → ℝ≥0∞ := fun ω t =>
      ENNReal.ofReal (Real.rpowIntegrand₀₁ p t (mX ω))
    let fY : ΩY → ℝ → ℝ≥0∞ := fun ω t =>
      ENNReal.ofReal (Real.rpowIntegrand₀₁ p t (mY ω))
    have hfX : AEMeasurable (Function.uncurry fX) (PX.prod ν) := by
      have hkernel : Measurable (fun z : ℝ × ℝ =>
          Real.rpowIntegrand₀₁ p z.1 z.2) := by
        unfold Real.rpowIntegrand₀₁
        fun_prop
      have hpair : AEMeasurable (fun z : ΩX × ℝ => (z.2, mX z.1)) (PX.prod ν) :=
        measurable_snd.aemeasurable.prodMk hmX.comp_fst
      exact (hkernel.comp_aemeasurable hpair).ennreal_ofReal
    have hfY : AEMeasurable (Function.uncurry fY) (PY.prod ν) := by
      have hkernel : Measurable (fun z : ℝ × ℝ =>
          Real.rpowIntegrand₀₁ p z.1 z.2) := by
        unfold Real.rpowIntegrand₀₁
        fun_prop
      have hpair : AEMeasurable (fun z : ΩY × ℝ => (z.2, mY z.1)) (PY.prod ν) :=
        measurable_snd.aemeasurable.prodMk hmY.comp_fst
      exact (hkernel.comp_aemeasurable hpair).ennreal_ofReal
    have hpointX (ω : ΩX) :
        ENNReal.rpow (ENNReal.ofReal (mX ω)) p =
          ENNReal.ofReal c * ∫⁻ t, fX ω t ∂ν := by
      change ENNReal.ofReal (mX ω) ^ p = _
      rw [ENNReal.ofReal_rpow_of_pos (hmXpos ω)]
      have hkernelInt : IntegrableOn
          (fun t => Real.rpowIntegrand₀₁ p t (mX ω)) (Ioi (0 : ℝ)) volume :=
        Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hp.1, hp.2⟩ (hmX0 ω)
      have hkernelNonneg :
          0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
            (fun t => Real.rpowIntegrand₀₁ p t (mX ω)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) (hmX0 ω)
      have hkernelL := ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg
      rw [show (mX ω) ^ p = c *
            ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t (mX ω) ∂volume by
            simpa [c] using Real.rpow_eq_const_mul_integral
              ⟨hp.1, hp.2⟩ (hmX0 ω),
        ENNReal.ofReal_mul hcpos.le, hkernelL]
    have hpointY (ω : ΩY) :
        ENNReal.rpow (ENNReal.ofReal (mY ω)) p =
          ENNReal.ofReal c * ∫⁻ t, fY ω t ∂ν := by
      change ENNReal.ofReal (mY ω) ^ p = _
      rw [ENNReal.ofReal_rpow_of_pos (hmYpos ω)]
      have hkernelInt : IntegrableOn
          (fun t => Real.rpowIntegrand₀₁ p t (mY ω)) (Ioi (0 : ℝ)) volume :=
        Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hp.1, hp.2⟩ (hmY0 ω)
      have hkernelNonneg :
          0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
            (fun t => Real.rpowIntegrand₀₁ p t (mY ω)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) (hmY0 ω)
      have hkernelL := ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg
      rw [show (mY ω) ^ p = c *
            ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t (mY ω) ∂volume by
            simpa [c] using Real.rpow_eq_const_mul_integral
              ⟨hp.1, hp.2⟩ (hmY0 ω),
        ENNReal.ofReal_mul hcpos.le, hkernelL]
    have hRepX : DOZZ.finiteChaosMoment PX X a γ p =
        ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume := by
      rw [DOZZ.finiteChaosMoment]
      calc
        (∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX) =
            ∫⁻ ω, ENNReal.ofReal c * (∫⁻ t, fX ω t ∂ν) ∂PX := by
              apply lintegral_congr_ae
              exact ae_of_all PX hpointX
        _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ t, fX ω t ∂ν ∂PX :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal c * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hfX
    have hRepY : DOZZ.finiteChaosMoment PY Y a γ p =
        ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume := by
      rw [DOZZ.finiteChaosMoment]
      calc
        (∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY) =
            ∫⁻ ω, ENNReal.ofReal c * (∫⁻ t, fY ω t ∂ν) ∂PY := by
              apply lintegral_congr_ae
              exact ae_of_all PY hpointY
        _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ t, fY ω t ∂ν ∂PY :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal c * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hfY
    have hkernelOrder (t : ℝ) (ht : 0 < t) :
        ∫⁻ ω, fY ω t ∂PY ≤ ∫⁻ ω, fX ω t ∂PX := by
      have hfrac := laplace_order_fraction_expectation PX PY mX mY hmX hmY hmX0 hmY0 hLap t ht
      have hfracIntX := resolvent_fraction_integrable PX mX hmX hmX0 t ht
      have hfracIntY := resolvent_fraction_integrable PY mY hmY hmY0 t ht
      have hcoef : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg (le_of_lt ht) _
      have hkernelEqX (ω : ΩX) : Real.rpowIntegrand₀₁ p t (mX ω) =
          t ^ (p - 1) * (mX ω / (t + mX ω)) := by
        rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp.1, hp.2⟩ ht.le (hmX0 ω)]
        ring
      have hkernelEqY (ω : ΩY) : Real.rpowIntegrand₀₁ p t (mY ω) =
          t ^ (p - 1) * (mY ω / (t + mY ω)) := by
        rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp.1, hp.2⟩ ht.le (hmY0 ω)]
        ring
      have hkerIntX : Integrable (fun ω => Real.rpowIntegrand₀₁ p t (mX ω)) PX := by
        rw [show (fun ω => Real.rpowIntegrand₀₁ p t (mX ω)) =
          fun ω => t ^ (p - 1) * (mX ω / (t + mX ω)) by funext ω; exact hkernelEqX ω]
        exact (hfracIntX.const_mul (t ^ (p - 1))).congr
          (Filter.Eventually.of_forall fun ω => by ring)
      have hkerIntY : Integrable (fun ω => Real.rpowIntegrand₀₁ p t (mY ω)) PY := by
        rw [show (fun ω => Real.rpowIntegrand₀₁ p t (mY ω)) =
          fun ω => t ^ (p - 1) * (mY ω / (t + mY ω)) by funext ω; exact hkernelEqY ω]
        exact (hfracIntY.const_mul (t ^ (p - 1))).congr
          (Filter.Eventually.of_forall fun ω => by ring)
      have hkerNonnegX : ∀ ω, 0 ≤ Real.rpowIntegrand₀₁ p t (mX ω) := by
        intro ω
        exact Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (hmX0 ω)
      have hkerNonnegY : ∀ ω, 0 ≤ Real.rpowIntegrand₀₁ p t (mY ω) := by
        intro ω
        exact Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (hmY0 ω)
      have hkerReal :
          ∫ ω', Real.rpowIntegrand₀₁ p t (mY ω') ∂PY ≤
            ∫ ω, Real.rpowIntegrand₀₁ p t (mX ω) ∂PX := by
        rw [show (fun ω => Real.rpowIntegrand₀₁ p t (mX ω)) =
            fun ω => t ^ (p - 1) * (mX ω / (t + mX ω)) by funext ω; exact hkernelEqX ω,
          show (fun ω => Real.rpowIntegrand₀₁ p t (mY ω)) =
            fun ω => t ^ (p - 1) * (mY ω / (t + mY ω)) by funext ω; exact hkernelEqY ω,
          integral_const_mul, integral_const_mul]
        exact mul_le_mul_of_nonneg_left hfrac hcoef
      have hlinX := ofReal_integral_eq_lintegral_ofReal hkerIntX
        (Filter.Eventually.of_forall hkerNonnegX)
      have hlinY := ofReal_integral_eq_lintegral_ofReal hkerIntY
        (Filter.Eventually.of_forall hkerNonnegY)
      rw [← hlinY, ← hlinX]
      exact ENNReal.ofReal_le_ofReal hkerReal
    have houter :
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume ≤
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hkernelOrder t ht
    rw [hRepX, hRepY]
    gcongr
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      have hnot : ¬ 0 < a i := fun hi => hapos ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt hnot) (ha i)
    have hmassX (ω : ΩX) : DOZZ.finiteChaosMass PX X a γ ω = 0 := by
      simp [DOZZ.finiteChaosMass, ha0]
    have hmassY (ω : ΩY) : DOZZ.finiteChaosMass PY Y a γ ω = 0 := by
      simp [DOZZ.finiteChaosMass, ha0]
    simp [DOZZ.finiteChaosMoment, hmassX, hmassY, ENNReal.zero_rpow_of_pos hp.1,
      hX.1.measure_univ, hY.1.measure_univ]

/-- The finite convex power comparison on `1 < p < 2`, from the resolvent representation of
`x^p` and equality of the first chaos moments. -/
theorem kahane_finite_power_convex_one_two
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ p : ℝ)
    (hp : 1 < p ∧ p < 2)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ p ≤ DOZZ.finiteChaosMoment PY Y a γ p := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  by_cases hapos : ∃ i, 0 < a i
  · let mX : ΩX → ℝ := DOZZ.finiteChaosMass PX X a γ
    let mY : ΩY → ℝ := DOZZ.finiteChaosMass PY Y a γ
    have hmX : AEMeasurable mX PX := finiteChaosMass_measurable PX X hX a γ
    have hmY : AEMeasurable mY PY := finiteChaosMass_measurable PY Y hY a γ
    have hmX0 : ∀ ω, 0 ≤ mX ω := finiteChaosMass_nonneg PX X a ha γ
    have hmY0 : ∀ ω, 0 ≤ mY ω := finiteChaosMass_nonneg PY Y a ha γ
    have hmXpos : ∀ ω, 0 < mX ω :=
      finiteChaosMass_pos_of_pos_weight PX X a ha hapos γ
    have hmYpos : ∀ ω, 0 < mY ω :=
      finiteChaosMass_pos_of_pos_weight PY Y a ha hapos γ
    have hLap (s : ℝ) (hs : 0 ≤ s) :
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mX ω))) ∂PX ≤
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mY ω))) ∂PY := by
      have h := kahane_finite_laplace_lintegral_fintype PX PY X Y hX hY a ha γ s hs hcov
      have hXexp : (fun ω => Real.exp (-s * mX ω)) =
          fun ω => Real.exp (-(s * mX ω)) := by
        funext ω
        congr 1
        ring
      have hYexp : (fun ω => Real.exp (-s * mY ω)) =
          fun ω => Real.exp (-(s * mY ω)) := by
        funext ω
        congr 1
        ring
      simpa [mX, mY, hXexp, hYexp] using h
    let c : ℝ := (∫ t in Ioi (0 : ℝ),
      Real.rpowIntegrand₀₁ (p - 1) t 1 ∂volume)⁻¹
    have hcpos : 0 < c := by
      dsimp [c]
      have hp' : p - 1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
      exact inv_pos.mpr (Real.integral_rpowIntegrand₀₁_one_pos hp')
    let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
    let fX : ΩX → ℝ → ℝ≥0∞ := fun ω t =>
      ENNReal.ofReal (Real.rpowIntegrand₁₂ p t (mX ω))
    let fY : ΩY → ℝ → ℝ≥0∞ := fun ω t =>
      ENNReal.ofReal (Real.rpowIntegrand₁₂ p t (mY ω))
    have hfX : AEMeasurable (Function.uncurry fX) (PX.prod ν) := by
      have hkernel : Measurable (fun z : ℝ × ℝ => Real.rpowIntegrand₁₂ p z.1 z.2) := by
        unfold Real.rpowIntegrand₁₂
        fun_prop
      have hpair : AEMeasurable (fun z : ΩX × ℝ => (z.2, mX z.1)) (PX.prod ν) :=
        measurable_snd.aemeasurable.prodMk hmX.comp_fst
      exact (hkernel.comp_aemeasurable hpair).ennreal_ofReal
    have hfY : AEMeasurable (Function.uncurry fY) (PY.prod ν) := by
      have hkernel : Measurable (fun z : ℝ × ℝ => Real.rpowIntegrand₁₂ p z.1 z.2) := by
        unfold Real.rpowIntegrand₁₂
        fun_prop
      have hpair : AEMeasurable (fun z : ΩY × ℝ => (z.2, mY z.1)) (PY.prod ν) :=
        measurable_snd.aemeasurable.prodMk hmY.comp_fst
      exact (hkernel.comp_aemeasurable hpair).ennreal_ofReal
    have hpointX (ω : ΩX) :
        ENNReal.rpow (ENNReal.ofReal (mX ω)) p =
          ENNReal.ofReal c * ∫⁻ t, fX ω t ∂ν := by
      change ENNReal.ofReal (mX ω) ^ p = _
      rw [ENNReal.ofReal_rpow_of_pos (hmXpos ω)]
      have hp' : p - 1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
      have hkernelInt : IntegrableOn
          (fun t => Real.rpowIntegrand₁₂ p t (mX ω)) (Ioi (0 : ℝ)) volume :=
        Real.integrableOn_rpowIntegrand₁₂ ⟨hp.1, hp.2⟩ (hmX0 ω)
      have hkernelNonneg :
          0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
            (fun t => Real.rpowIntegrand₁₂ p t (mX ω)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpowIntegrand₁₂_nonneg hp.1 ht.le (hmX0 ω)
      have hkernelL := ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg
      rw [show (mX ω) ^ p = c *
            ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₁₂ p t (mX ω) ∂volume by
            simpa [c] using Real.rpow_eq_const_mul_integral_rpowIntegrand₁₂
              ⟨hp.1, hp.2⟩ (hmX0 ω),
        ENNReal.ofReal_mul hcpos.le, hkernelL]
    have hpointY (ω : ΩY) :
        ENNReal.rpow (ENNReal.ofReal (mY ω)) p =
          ENNReal.ofReal c * ∫⁻ t, fY ω t ∂ν := by
      change ENNReal.ofReal (mY ω) ^ p = _
      rw [ENNReal.ofReal_rpow_of_pos (hmYpos ω)]
      have hkernelInt : IntegrableOn
          (fun t => Real.rpowIntegrand₁₂ p t (mY ω)) (Ioi (0 : ℝ)) volume :=
        Real.integrableOn_rpowIntegrand₁₂ ⟨hp.1, hp.2⟩ (hmY0 ω)
      have hkernelNonneg :
          0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
            (fun t => Real.rpowIntegrand₁₂ p t (mY ω)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpowIntegrand₁₂_nonneg hp.1 ht.le (hmY0 ω)
      have hkernelL := ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg
      rw [show (mY ω) ^ p = c *
            ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₁₂ p t (mY ω) ∂volume by
            simpa [c] using Real.rpow_eq_const_mul_integral_rpowIntegrand₁₂
              ⟨hp.1, hp.2⟩ (hmY0 ω),
        ENNReal.ofReal_mul hcpos.le, hkernelL]
    have hRepX : DOZZ.finiteChaosMoment PX X a γ p =
        ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume := by
      rw [DOZZ.finiteChaosMoment]
      calc
        (∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX) =
            ∫⁻ ω, ENNReal.ofReal c * (∫⁻ t, fX ω t ∂ν) ∂PX := by
              apply lintegral_congr_ae
              exact ae_of_all PX hpointX
        _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ t, fX ω t ∂ν ∂PX :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal c * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hfX
    have hRepY : DOZZ.finiteChaosMoment PY Y a γ p =
        ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume := by
      rw [DOZZ.finiteChaosMoment]
      calc
        (∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY) =
            ∫⁻ ω, ENNReal.ofReal c * (∫⁻ t, fY ω t ∂ν) ∂PY := by
              apply lintegral_congr_ae
              exact ae_of_all PY hpointY
        _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ t, fY ω t ∂ν ∂PY :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal c * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hfY
    have hmassIntX : Integrable mX PX ∧ (∫ ω, mX ω ∂PX) = ∑ i, a i := by
      simpa [mX] using finiteChaosMass_integral PX X hX a γ
    have hmassIntY : Integrable mY PY ∧ (∫ ω, mY ω ∂PY) = ∑ i, a i := by
      simpa [mY] using finiteChaosMass_integral PY Y hY a γ
    have hkernelOrder (t : ℝ) (ht : 0 < t) :
        ∫⁻ ω, fX ω t ∂PX ≤ ∫⁻ ω, fY ω t ∂PY := by
      have hInvOrd := laplace_order_inverse_expectation PX PY mX mY hmX hmY
        hmX0 hmY0 hLap t ht
      have hInvIntX := resolvent_inverse_integrable PX mX hmX hmX0 t ht
      have hInvIntY := resolvent_inverse_integrable PY mY hmY hmY0 t ht
      have hKernelEqX (ω : ΩX) : Real.rpowIntegrand₁₂ p t (mX ω) =
          t ^ (p - 2) * (mX ω - t + t ^ 2 * (t + mX ω)⁻¹) := by
        rw [Real.rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ (hmX0 ω) ht]
        have hp' : p - 1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
        rw [Real.rpowIntegrand₀₁_eq_pow_div hp' ht.le (hmX0 ω)]
        have hpow : t ^ ((p - 1) - 1) = t ^ (p - 2) := by congr 1; ring
        rw [hpow]
        have hden : t + mX ω ≠ 0 := ne_of_gt (by linarith [ht, hmX0 ω])
        field_simp [hden, ne_of_gt ht]
        ring
      have hKernelEqY (ω : ΩY) : Real.rpowIntegrand₁₂ p t (mY ω) =
          t ^ (p - 2) * (mY ω - t + t ^ 2 * (t + mY ω)⁻¹) := by
        rw [Real.rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ (hmY0 ω) ht]
        have hp' : p - 1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
        rw [Real.rpowIntegrand₀₁_eq_pow_div hp' ht.le (hmY0 ω)]
        have hpow : t ^ ((p - 1) - 1) = t ^ (p - 2) := by congr 1; ring
        rw [hpow]
        have hden : t + mY ω ≠ 0 := ne_of_gt (by linarith [ht, hmY0 ω])
        field_simp [hden, ne_of_gt ht]
        ring
      have hinnerIntX : Integrable
          (fun ω => mX ω - t + t ^ 2 * (t + mX ω)⁻¹) PX := by
        have h := (hmassIntX.1.sub (integrable_const t)).add (hInvIntX.const_mul (t ^ 2))
        exact h.congr (Filter.Eventually.of_forall fun ω => by
          change (mX ω - t) + t ^ 2 * (t + mX ω)⁻¹ =
            mX ω - t + t ^ 2 * (t + mX ω)⁻¹
          rfl)
      have hinnerIntY : Integrable
          (fun ω => mY ω - t + t ^ 2 * (t + mY ω)⁻¹) PY := by
        have h := (hmassIntY.1.sub (integrable_const t)).add (hInvIntY.const_mul (t ^ 2))
        exact h.congr (Filter.Eventually.of_forall fun ω => by
          change (mY ω - t) + t ^ 2 * (t + mY ω)⁻¹ =
            mY ω - t + t ^ 2 * (t + mY ω)⁻¹
          rfl)
      have hkernelIntX : Integrable (fun ω => Real.rpowIntegrand₁₂ p t (mX ω)) PX := by
        rw [show (fun ω => Real.rpowIntegrand₁₂ p t (mX ω)) =
          fun ω => t ^ (p - 2) * (mX ω - t + t ^ 2 * (t + mX ω)⁻¹) by
            funext ω
            exact hKernelEqX ω]
        exact (hinnerIntX.const_mul (t ^ (p - 2))).congr
          (Filter.Eventually.of_forall fun ω => by ring)
      have hkernelIntY : Integrable (fun ω => Real.rpowIntegrand₁₂ p t (mY ω)) PY := by
        rw [show (fun ω => Real.rpowIntegrand₁₂ p t (mY ω)) =
          fun ω => t ^ (p - 2) * (mY ω - t + t ^ 2 * (t + mY ω)⁻¹) by
            funext ω
            exact hKernelEqY ω]
        exact (hinnerIntY.const_mul (t ^ (p - 2))).congr
          (Filter.Eventually.of_forall fun ω => by ring)
      have hmeanX : (∫ ω, Real.rpowIntegrand₁₂ p t (mX ω) ∂PX) =
          t ^ (p - 2) * ((∫ ω, mX ω ∂PX) - t +
            t ^ 2 * ∫ ω, (t + mX ω)⁻¹ ∂PX) := by
        have hconst : Integrable (fun _ : ΩX => t) PX := integrable_const t
        have hinner : (∫ ω, mX ω - t + t ^ 2 * (t + mX ω)⁻¹ ∂PX) =
            (∫ ω, mX ω ∂PX) - t + t ^ 2 * ∫ ω, (t + mX ω)⁻¹ ∂PX := by
          calc
            _ = (∫ ω, mX ω - t ∂PX) + ∫ ω, t ^ 2 * (t + mX ω)⁻¹ ∂PX :=
              integral_add (hmassIntX.1.sub hconst) (hInvIntX.const_mul (t ^ 2))
            _ = (∫ ω, mX ω ∂PX) - t + t ^ 2 * ∫ ω, (t + mX ω)⁻¹ ∂PX := by
              rw [integral_sub hmassIntX.1 hconst, integral_const, integral_const_mul]
              simp
        calc
          _ = ∫ ω, t ^ (p - 2) *
              (mX ω - t + t ^ 2 * (t + mX ω)⁻¹) ∂PX := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun ω => hKernelEqX ω
          _ = t ^ (p - 2) *
              ∫ ω, mX ω - t + t ^ 2 * (t + mX ω)⁻¹ ∂PX := by
                rw [integral_const_mul]
          _ = _ := by rw [hinner]
      have hmeanY : (∫ ω, Real.rpowIntegrand₁₂ p t (mY ω) ∂PY) =
          t ^ (p - 2) * ((∫ ω, mY ω ∂PY) - t +
            t ^ 2 * ∫ ω, (t + mY ω)⁻¹ ∂PY) := by
        have hconst : Integrable (fun _ : ΩY => t) PY := integrable_const t
        have hinner : (∫ ω, mY ω - t + t ^ 2 * (t + mY ω)⁻¹ ∂PY) =
            (∫ ω, mY ω ∂PY) - t + t ^ 2 * ∫ ω, (t + mY ω)⁻¹ ∂PY := by
          calc
            _ = (∫ ω, mY ω - t ∂PY) + ∫ ω, t ^ 2 * (t + mY ω)⁻¹ ∂PY :=
              integral_add (hmassIntY.1.sub hconst) (hInvIntY.const_mul (t ^ 2))
            _ = (∫ ω, mY ω ∂PY) - t + t ^ 2 * ∫ ω, (t + mY ω)⁻¹ ∂PY := by
              rw [integral_sub hmassIntY.1 hconst, integral_const, integral_const_mul]
              simp
        calc
          _ = ∫ ω, t ^ (p - 2) *
              (mY ω - t + t ^ 2 * (t + mY ω)⁻¹) ∂PY := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun ω => hKernelEqY ω
          _ = t ^ (p - 2) *
              ∫ ω, mY ω - t + t ^ 2 * (t + mY ω)⁻¹ ∂PY := by
                rw [integral_const_mul]
          _ = _ := by rw [hinner]
      have hkerReal : (∫ ω, Real.rpowIntegrand₁₂ p t (mX ω) ∂PX) ≤
          ∫ ω, Real.rpowIntegrand₁₂ p t (mY ω) ∂PY := by
        rw [hmeanX, hmeanY, hmassIntX.2, hmassIntY.2]
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have hpcoef : 0 ≤ t ^ (p - 2) := Real.rpow_nonneg ht.le _
        gcongr
      have hkerNonnegX : ∀ ω, 0 ≤ Real.rpowIntegrand₁₂ p t (mX ω) := by
        intro ω
        exact Real.rpowIntegrand₁₂_nonneg hp.1 ht.le (hmX0 ω)
      have hkerNonnegY : ∀ ω, 0 ≤ Real.rpowIntegrand₁₂ p t (mY ω) := by
        intro ω
        exact Real.rpowIntegrand₁₂_nonneg hp.1 ht.le (hmY0 ω)
      have hlinX := ofReal_integral_eq_lintegral_ofReal hkernelIntX
        (Filter.Eventually.of_forall hkerNonnegX)
      have hlinY := ofReal_integral_eq_lintegral_ofReal hkernelIntY
        (Filter.Eventually.of_forall hkerNonnegY)
      rw [← hlinX, ← hlinY]
      exact ENNReal.ofReal_le_ofReal hkerReal
    have houter :
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume ≤
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hkernelOrder t ht
    rw [hRepX, hRepY]
    gcongr
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      have hnot : ¬ 0 < a i := fun hi => hapos ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt hnot) (ha i)
    have hmassX (ω : ΩX) : DOZZ.finiteChaosMass PX X a γ ω = 0 := by
      simp [DOZZ.finiteChaosMass, ha0]
    have hmassY (ω : ΩY) : DOZZ.finiteChaosMass PY Y a γ ω = 0 := by
      simp [DOZZ.finiteChaosMass, ha0]
    have hp0 : 0 < p := lt_trans zero_lt_one hp.1
    simp [DOZZ.finiteChaosMoment, hmassX, hmassY, ENNReal.zero_rpow_of_pos hp0,
      hX.1.measure_univ, hY.1.measure_univ]


end DOZZ.Proofs
