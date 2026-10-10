/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosGaussianLaplaceFintype
public import DOZZ.GMC.FiniteChaosMellin
public import DOZZ.Statements.GMC.FiniteChaosMoment
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Negative finite-chaos powers from the finite Laplace comparison. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Distributions

namespace DOZZ.Proofs

private theorem finiteChaosMass_aemeasurable
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
  change AEMeasurable (fun ω => ∑ i, a i * Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i))) P
  exact Finset.aemeasurable_fun_sum _ fun i _ => hterm i

/-- Integrating the pointwise Mellin formula expresses a negative moment as a weighted integral
of Laplace transforms. Tonelli is applied on the probability space times the positive half-line. -/
theorem finite_rpow_neg_lintegral_eq_weighted_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : Ω → ℝ)
    (hm : ∀ ω, 0 < m ω) (hmA : AEMeasurable m P) (q : ℝ) (hq : 0 < q) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
      ENNReal.ofReal (1 / Real.Gamma q) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / Real.Gamma q)
  let f : Ω → ℝ → ℝ≥0∞ := fun ω t =>
    ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m ω * t)))
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hf : AEMeasurable (Function.uncurry f) (P.prod ν) := by
    have hmprod : AEMeasurable (fun z : Ω × ℝ => m z.1) (P.prod ν) := hmA.comp_fst
    have htprod : AEMeasurable (fun z : Ω × ℝ => z.2) (P.prod ν) :=
      measurable_snd.aemeasurable
    have harg : AEMeasurable (fun z : Ω × ℝ => -(m z.1 * z.2)) (P.prod ν) :=
      (hmprod.mul htprod).neg
    have hexp : AEMeasurable (fun z : Ω × ℝ => Real.exp (-(m z.1 * z.2)))
        (P.prod ν) := Real.measurable_exp.comp_aemeasurable harg
    have hpow : Measurable (fun z : Ω × ℝ => z.2 ^ (q - 1)) := by fun_prop
    have hreal : AEMeasurable (fun z : Ω × ℝ =>
        z.2 ^ (q - 1) * Real.exp (-(m z.1 * z.2))) (P.prod ν) :=
      hpow.aemeasurable.mul hexp
    exact hreal.ennreal_ofReal
  have hfactor : ∀ᵐ t ∂ν,
      (∫⁻ ω, f ω t ∂P) = ENNReal.ofReal (t ^ (q - 1)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hct : ENNReal.ofReal (t ^ (q - 1)) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [show (fun ω => f ω t) = fun ω => ENNReal.ofReal (t ^ (q - 1)) *
        ENNReal.ofReal (Real.exp (-(m ω * t))) by
          funext ω
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)] ]
    exact lintegral_const_mul' _ _ hct
  have hpoint (ω : Ω) :
      ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) =
        c * ∫⁻ t in Ioi (0 : ℝ), f ω t ∂volume := by
    change ENNReal.ofReal (m ω) ^ (-q) = _
    rw [ENNReal.ofReal_rpow_of_pos (hm ω)]
    simpa [c, f] using ofReal_rpow_neg_eq_mellin_lintegral (hm ω) hq
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
        ∫⁻ ω, c * (∫⁻ t in Ioi (0 : ℝ), f ω t ∂volume) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P hpoint
    _ = c * ∫⁻ ω, ∫⁻ t, f ω t ∂ν ∂P := lintegral_const_mul' c _ hc
    _ = c * ∫⁻ t, ∫⁻ ω, f ω t ∂P ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hf
    _ = c * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
          congr 1
          apply lintegral_congr_ae
          exact hfactor

/-- The scalar negative-power Kahane comparison follows from the finite Laplace comparison by
Mellin integration. A positive coefficient makes each finite chaos mass strictly positive. -/
theorem kahane_finite_negative_power_of_pos_weight
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hapos : ∃ i, 0 < a i)
    (γ q : ℝ) (hq : 0 < q)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ (-q) ≤ DOZZ.finiteChaosMoment PY Y a γ (-q) := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  let mX : ΩX → ℝ := DOZZ.finiteChaosMass PX X a γ
  let mY : ΩY → ℝ := DOZZ.finiteChaosMass PY Y a γ
  have hposX (ω : ΩX) : 0 < mX ω := by
    obtain ⟨i, hai⟩ := hapos
    have hterms : ∀ j, 0 ≤ a j * Real.exp (γ * X ω j - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PX (fun ω => X ω j)) :=
      fun j => mul_nonneg (ha j) (le_of_lt (Real.exp_pos _))
    have hterm : 0 < a i * Real.exp (γ * X ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PX (fun ω => X ω i)) := mul_pos hai (Real.exp_pos _)
    dsimp [mX, DOZZ.finiteChaosMass]
    exact lt_of_lt_of_le hterm (Finset.single_le_sum (fun j _ => hterms j)
      (Finset.mem_univ i))
  have hposY (ω : ΩY) : 0 < mY ω := by
    obtain ⟨i, hai⟩ := hapos
    have hterms : ∀ j, 0 ≤ a j * Real.exp (γ * Y ω j - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PY (fun ω => Y ω j)) :=
      fun j => mul_nonneg (ha j) (le_of_lt (Real.exp_pos _))
    have hterm : 0 < a i * Real.exp (γ * Y ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PY (fun ω => Y ω i)) := mul_pos hai (Real.exp_pos _)
    dsimp [mY, DOZZ.finiteChaosMass]
    exact lt_of_lt_of_le hterm (Finset.single_le_sum (fun j _ => hterms j)
      (Finset.mem_univ i))
  have hLaplace (t : ℝ) (ht : 0 ≤ t) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mX ω)) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mY ω)) ∂PY := by
    simpa [mX, mY] using
      kahane_finite_laplace_lintegral_fintype PX PY X Y hX hY a ha γ t ht hcov
  simp only [DOZZ.finiteChaosMoment]
  have hMX := finite_rpow_neg_lintegral_eq_weighted_laplace PX mX hposX
    (finiteChaosMass_aemeasurable PX X hX a γ) q hq
  have hMY := finite_rpow_neg_lintegral_eq_weighted_laplace PY mY hposY
    (finiteChaosMass_aemeasurable PY Y hY a γ) q hq
  have hInt :
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hXexp : (fun ω => ENNReal.ofReal (Real.exp (-t * mX ω))) =
        fun ω => ENNReal.ofReal (Real.exp (-(mX ω * t))) := by
      funext ω
      congr 2
      ring
    have hYexp : (fun ω => ENNReal.ofReal (Real.exp (-t * mY ω))) =
        fun ω => ENNReal.ofReal (Real.exp (-(mY ω * t))) := by
      funext ω
      congr 2
      ring
    gcongr
    rw [← hXexp, ← hYexp]
    exact hLaplace t ht0.le
  rw [hMX, hMY]
  gcongr

/-- Removing the positive-weight side condition also covers the all-zero weight vector: in that
case both negative moments are `⊤`. -/
theorem kahane_finite_negative_power
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ q : ℝ) (hq : 0 < q)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ (-q) ≤ DOZZ.finiteChaosMoment PY Y a γ (-q) := by
  classical
  by_cases hapos : ∃ i, 0 < a i
  · exact kahane_finite_negative_power_of_pos_weight PX PY X Y hX hY a ha hapos γ q hq hcov
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      have hnot : ¬ 0 < a i := fun hi => hapos ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt hnot) (ha i)
    have hmassX (ω : ΩX) : DOZZ.finiteChaosMass PX X a γ ω = 0 := by
      simp [DOZZ.finiteChaosMass, ha0]
    have hmassY (ω : ΩY) : DOZZ.finiteChaosMass PY Y a γ ω = 0 := by
      simp [DOZZ.finiteChaosMass, ha0]
    have hMX : DOZZ.finiteChaosMoment PX X a γ (-q) = ⊤ := by
      rw [DOZZ.finiteChaosMoment]
      simp [hmassX, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hq), hX.1.measure_univ]
    have hMY : DOZZ.finiteChaosMoment PY Y a γ (-q) = ⊤ := by
      rw [DOZZ.finiteChaosMoment]
      simp [hmassY, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hq), hY.1.measure_univ]
    rw [hMX, hMY]

/-- The finite Kahane inequality is established for every nonpositive real power. -/
theorem kahane_finite_power_nonpos
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ p : ℝ) (hp : p ≤ 0)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ p ≤ DOZZ.finiteChaosMoment PY Y a γ p := by
  by_cases hp0 : p = 0
  · simp [DOZZ.finiteChaosMoment, hp0, hX.1.measure_univ, hY.1.measure_univ]
  · have hpneg : p < 0 := lt_of_le_of_ne hp hp0
    have hq : 0 < -p := neg_pos.mpr hpneg
    simpa using kahane_finite_negative_power PX PY X Y hX hY a ha γ (-p) hq hcov


end DOZZ.Proofs
