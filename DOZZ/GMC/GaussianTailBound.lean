/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.GMC.FiniteChaosMean

/-! Exponential Markov bounds for centered one-dimensional Gaussian tails. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Chernoff's upper-tail bound for a centered Gaussian with positive variance. -/
theorem gaussianReal_upper_tail_bound (v : ℝ≥0) (b : ℝ)
    (hv : 0 < v) (hb : 0 ≤ b) :
    gaussianReal 0 v (Set.Ioi b) ≤
      ENNReal.ofReal (Real.exp (-b ^ 2 / (2 * (v : ℝ)))) := by
  let s : ℝ := b / (v : ℝ)
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (s * x))
  let ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * b))
  have hvR : 0 < (v : ℝ) := hv
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hε0 : ε ≠ 0 := by simp [ε, Real.exp_pos]
  have hεtop : ε ≠ ∞ := by simp [ε]
  have hf : Measurable f := by fun_prop
  have hsubset : Set.Ioi b ⊆ {x | ε ≤ f x} := by
    intro x hx
    change ENNReal.ofReal (Real.exp (s * b)) ≤
      ENNReal.ofReal (Real.exp (s * x))
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hx.le hs
  have hExpInt : Integrable (fun x : ℝ => Real.exp (s * x)) (gaussianReal 0 v) :=
    integrable_exp_mul_gaussianReal s
  have hExpNN : 0 ≤ᵐ[gaussianReal 0 v] fun x : ℝ => Real.exp (s * x) :=
    ae_of_all _ (fun x => (Real.exp_pos _).le)
  have hlin : (∫⁻ x, f x ∂gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp ((v : ℝ) * s ^ 2 / 2)) := by
    calc
      ∫⁻ x, f x ∂gaussianReal 0 v =
          ENNReal.ofReal (∫ x, Real.exp (s * x) ∂gaussianReal 0 v) :=
            (ofReal_integral_eq_lintegral_ofReal hExpInt hExpNN).symm
      _ = ENNReal.ofReal (Real.exp ((v : ℝ) * s ^ 2 / 2)) := by
        congr 1
        change mgf id (gaussianReal 0 v) s = _
        rw [mgf_id_gaussianReal]
        simp
  calc
    gaussianReal 0 v (Set.Ioi b) ≤ gaussianReal 0 v {x | ε ≤ f x} :=
      measure_mono hsubset
    _ ≤ (∫⁻ x, f x ∂gaussianReal 0 v) / ε :=
      meas_ge_le_lintegral_div hf.aemeasurable hε0 hεtop
    _ = ENNReal.ofReal (Real.exp (-b ^ 2 / (2 * (v : ℝ)))) := by
      rw [hlin, show ε = ENNReal.ofReal (Real.exp (s * b)) by rfl,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
      congr 2
      dsimp [s]
      field_simp
      ring

/-- Chernoff's lower-tail bound for a centered Gaussian; obtained by symmetry from the upper-tail
bound. -/
theorem gaussianReal_lower_tail_bound (v : ℝ≥0) (b : ℝ)
    (hv : 0 < v) (hb : b ≤ 0) :
    gaussianReal 0 v (Set.Iio b) ≤
      ENNReal.ofReal (Real.exp (-b ^ 2 / (2 * (v : ℝ)))) := by
  have hset : (fun x : ℝ => -x) ⁻¹' Set.Ioi (-b) = Set.Iio b := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    constructor <;> intro hx <;> linarith
  calc
    gaussianReal 0 v (Set.Iio b) =
        gaussianReal 0 v ((fun x : ℝ => -x) ⁻¹' Set.Ioi (-b)) := by rw [hset]
    _ = (gaussianReal 0 v).map (fun x : ℝ => -x) (Set.Ioi (-b)) := by
          rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
    _ = gaussianReal 0 v (Set.Ioi (-b)) := by
          rw [gaussianReal_map_neg]
          simp
    _ ≤ ENNReal.ofReal (Real.exp (-(-b) ^ 2 / (2 * (v : ℝ)))) :=
          gaussianReal_upper_tail_bound v (-b) hv (neg_nonneg.mpr hb)
    _ = _ := by congr 4; ring

/-- A finite Wick tilt shifts a Gaussian barrier coordinate by the covariance pairing; the
barrier-violation expectation is bounded by the Gaussian Chernoff tail of that shifted coordinate.
This form includes the two-root tilt used in the mixed-cutoff GMC kernel. -/
theorem finite_gaussian_tilt_barrier_tail_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (tilt : ι → ℝ) (j : ι) (b : ℝ)
    (hgap : ∑ k, gaussianCovariance P (fun ω => Z ω j)
      (fun ω => Z ω k) * tilt k < b)
    (hv : 0 < gaussianVariance P (fun ω => Z ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ k, tilt k * Z ω k) -
          (∑ k, ∑ l, tilt k * gaussianCovariance P
            (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
      (Set.indicator {ω | b < Z ω j} (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp
          (-(b - ∑ k, gaussianCovariance P (fun ω => Z ω j)
              (fun ω => Z ω k) * tilt k) ^ 2 /
            (2 * gaussianVariance P (fun ω => Z ω j)))) := by
  classical
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ j
  let Zi : Ω → ℝ := fun ω => Z ω j
  let shift : ι → ℝ := fun k => ∑ l, gaussianCovariance P
    (fun ω => Z ω k) (fun ω => Z ω l) * tilt l
  let m : ℝ := ∑ k, gaussianCovariance P
    (fun ω => Z ω j) (fun ω => Z ω k) * tilt k
  let event : (ι → ℝ) → ℝ≥0∞ := fun z => if b < z j then 1 else 0
  have hZi : AEMeasurable Zi P := hZ.2.1 j
  have hvR : 0 < (v : ℝ) := by rw [← hvar]; exact hv
  have hvNN : 0 < v := by exact_mod_cast hvR
  have hgap' : 0 < b - m := sub_pos.mpr hgap
  have hevent : Measurable event := by
    refine Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j)) ?_ ?_
    · exact measurable_const
    · exact measurable_const
  have hTilt := finite_gaussian_tilt P Z hZ tilt event hevent
  have hshiftEvent (ω : Ω) :
      event (fun k => Z ω k + shift k) =
        Set.indicator {ω' | b - m < Zi ω'} (fun _ => (1 : ℝ≥0∞)) ω := by
    change (if b < Z ω j + m then 1 else 0) =
      (if b - m < Zi ω then 1 else 0)
    by_cases h : b < Z ω j + m
    · have h' : b - m < Zi ω := by dsimp [Zi]; linarith
      simp [h, h']
    · have h' : ¬ b - m < Zi ω := by dsimp [Zi]; linarith
      simp [h, h']
  have hTail :
      ∫⁻ ω, event (fun k => Z ω k + shift k) ∂P ≤
        ENNReal.ofReal (Real.exp (-(b - m) ^ 2 /
          (2 * gaussianVariance P (fun ω => Z ω j)))) := by
    have hpre :
        (∫⁻ ω, event (fun k => Z ω k + shift k) ∂P) =
          gaussianReal 0 v (Set.Ioi (b - m)) := by
      calc
        _ = ∫⁻ ω, (Set.indicator {ω | b - m < Zi ω}
            (fun _ => (1 : ℝ≥0∞)) ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ hshiftEvent
        _ = P.map Zi (Set.Ioi (b - m)) := by
              have hset : {ω | b - m < Zi ω} = Zi ⁻¹' Set.Ioi (b - m) := by
                ext ω
                rfl
              rw [hset]
              change (∫⁻ ω, (Zi ⁻¹' Set.Ioi (b - m)).indicator 1 ω ∂P) =
                P.map Zi (Set.Ioi (b - m))
              calc
                _ = P (Zi ⁻¹' Set.Ioi (b - m)) :=
                  lintegral_indicator_one₀
                    (hZi.nullMeasurableSet_preimage measurableSet_Ioi)
                _ = P.map Zi (Set.Ioi (b - m)) :=
                  (Measure.map_apply_of_aemeasurable hZi measurableSet_Ioi).symm
        _ = gaussianReal 0 v (Set.Ioi (b - m)) := by rw [hmap]
    have hgauss := gaussianReal_upper_tail_bound v (b - m) hvNN hgap'.le
    rw [hpre]
    simpa only [← hvar] using hgauss
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ k, tilt k * Z ω k) -
            (∑ k, ∑ l, tilt k * gaussianCovariance P
              (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
            event (Z ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by simp [event, Set.indicator])
    _ = ∫⁻ ω, event (fun k => Z ω k + shift k) ∂P := by
          simpa only [shift] using hTilt
    _ ≤ _ := hTail

/-- A finite Wick tilt also admits a Gaussian lower-tail estimate after the coordinate's shifted
mean has crossed the barrier. This is the coarse-coordinate estimate under the two-root tilt in
the good-mass construction. -/
theorem finite_gaussian_tilt_barrier_lower_tail_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (tilt : ι → ℝ) (j : ι) (b : ℝ)
    (hgap : b < ∑ k, gaussianCovariance P (fun ω => Z ω j)
      (fun ω => Z ω k) * tilt k)
    (hv : 0 < gaussianVariance P (fun ω => Z ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ k, tilt k * Z ω k) -
          (∑ k, ∑ l, tilt k * gaussianCovariance P
            (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
      (Set.indicator {ω | Z ω j < b} (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp
          (-((∑ k, gaussianCovariance P (fun ω => Z ω j)
              (fun ω => Z ω k) * tilt k) - b) ^ 2 /
            (2 * gaussianVariance P (fun ω => Z ω j)))) := by
  classical
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ j
  let Zi : Ω → ℝ := fun ω => Z ω j
  let shift : ι → ℝ := fun k => ∑ l, gaussianCovariance P
    (fun ω => Z ω k) (fun ω => Z ω l) * tilt l
  let m : ℝ := ∑ k, gaussianCovariance P
    (fun ω => Z ω j) (fun ω => Z ω k) * tilt k
  let event : (ι → ℝ) → ℝ≥0∞ := fun z => if z j < b then 1 else 0
  have hZi : AEMeasurable Zi P := hZ.2.1 j
  have hvR : 0 < (v : ℝ) := by rw [← hvar]; exact hv
  have hvNN : 0 < v := by exact_mod_cast hvR
  have hgap' : b - m < 0 := sub_neg.mpr hgap
  have hevent : Measurable event := by
    refine Measurable.ite (measurableSet_lt (measurable_pi_apply j) measurable_const) ?_ ?_
    · exact measurable_const
    · exact measurable_const
  have hTilt := finite_gaussian_tilt P Z hZ tilt event hevent
  have hshiftEvent (ω : Ω) :
      event (fun k => Z ω k + shift k) =
        Set.indicator {ω' | Zi ω' < b - m} (fun _ => (1 : ℝ≥0∞)) ω := by
    change (if Z ω j + m < b then 1 else 0) =
      (if Zi ω < b - m then 1 else 0)
    by_cases h : Z ω j + m < b
    · have h' : Zi ω < b - m := by dsimp [Zi]; linarith
      simp [h, h']
    · have h' : ¬ Zi ω < b - m := by dsimp [Zi]; linarith
      simp [h, h']
  have hTail :
      ∫⁻ ω, event (fun k => Z ω k + shift k) ∂P ≤
        ENNReal.ofReal (Real.exp (-(m - b) ^ 2 /
          (2 * gaussianVariance P (fun ω => Z ω j)))) := by
    have hpre :
        (∫⁻ ω, event (fun k => Z ω k + shift k) ∂P) =
          gaussianReal 0 v (Set.Iio (b - m)) := by
      calc
        _ = ∫⁻ ω, (Set.indicator {ω | Zi ω < b - m}
            (fun _ => (1 : ℝ≥0∞)) ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ hshiftEvent
        _ = P.map Zi (Set.Iio (b - m)) := by
              have hset : {ω | b - m > Zi ω} = Zi ⁻¹' Set.Iio (b - m) := by
                ext ω
                simp [Zi]
              rw [hset]
              change (∫⁻ ω, (Zi ⁻¹' Set.Iio (b - m)).indicator 1 ω ∂P) =
                P.map Zi (Set.Iio (b - m))
              calc
                _ = P (Zi ⁻¹' Set.Iio (b - m)) :=
                  lintegral_indicator_one₀
                    (hZi.nullMeasurableSet_preimage measurableSet_Iio)
                _ = P.map Zi (Set.Iio (b - m)) :=
                  (Measure.map_apply_of_aemeasurable hZi measurableSet_Iio).symm
        _ = gaussianReal 0 v (Set.Iio (b - m)) := by rw [hmap]
    have hgauss := gaussianReal_lower_tail_bound v (b - m) hvNN hgap'.le
    rw [hpre]
    have hsq : -(b - m) ^ 2 = -(m - b) ^ 2 := by ring
    rw [← hvar, hsq] at hgauss
    exact hgauss
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ k, tilt k * Z ω k) -
            (∑ k, ∑ l, tilt k * gaussianCovariance P
              (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
            event (Z ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by simp [event, Set.indicator])
    _ = ∫⁻ ω, event (fun k => Z ω k + shift k) ∂P := by
          simpa only [shift] using hTilt
    _ ≤ _ := hTail

/-- The finite Gaussian tilt corresponding to two equal-charge roots. -/
def twoRootTilt {ι : Type*} [DecidableEq ι]
    (root₁ root₂ : ι) (g : ℝ) : ι → ℝ :=
  fun i => if i = root₁ then g else if i = root₂ then g else 0

/-- The Wick product of two root exponentials is the common two-root Gaussian tilt density,
multiplied by the deterministic exponential of the cross covariance. -/
theorem finite_gaussian_two_root_wick_tilt_integral_identity
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (root₁ root₂ : ι) (h₁₂ : root₁ ≠ root₂) (g : ℝ)
    (B : Ω → ℝ≥0∞) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₁))) *
      ENNReal.ofReal (Real.exp
        (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₂))) * B ω ∂P =
      ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
        (fun ω => Z ω root₁) (fun ω => Z ω root₂))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ i, twoRootTilt root₁ root₂ g i * Z ω i) -
            (∑ i, ∑ j, twoRootTilt root₁ root₂ g i *
              gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
              twoRootTilt root₁ root₂ g j) / 2)) * B ω ∂P := by
  classical
  let tilt : ι → ℝ := twoRootTilt root₁ root₂ g
  have hcoef (i : ι) : tilt i =
      (if i = root₁ then g else 0) + (if i = root₂ then g else 0) := by
    by_cases hi₁ : i = root₁
    · subst i
      simp [tilt, twoRootTilt, h₁₂]
    · by_cases hi₂ : i = root₂
      · subst i
        simp [tilt, twoRootTilt, hi₁]
      · simp [tilt, twoRootTilt, hi₁, hi₂]
  have hlin (ω : Ω) : ∑ i, tilt i * Z ω i =
      g * Z ω root₁ + g * Z ω root₂ := by
    rw [show (∑ i, tilt i * Z ω i) =
        ∑ i, ((if i = root₁ then g else 0) * Z ω i +
          (if i = root₂ then g else 0) * Z ω i) by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoef i]
          ring]
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
  have hquad : (∑ i, ∑ j, tilt i *
      gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * tilt j) =
      g ^ 2 * gaussianVariance P (fun ω => Z ω root₁) +
        g ^ 2 * gaussianCovariance P (fun ω => Z ω root₁)
          (fun ω => Z ω root₂) +
        g ^ 2 * gaussianCovariance P (fun ω => Z ω root₂)
          (fun ω => Z ω root₁) +
        g ^ 2 * gaussianVariance P (fun ω => Z ω root₂) := by
    simp_rw [hcoef]
    simp only [Finset.sum_add_distrib, add_mul, mul_add]
    simp [Finset.sum_ite_eq', gaussianVariance]
    ring
  have hcovsym : gaussianCovariance P (fun ω => Z ω root₁)
      (fun ω => Z ω root₂) = gaussianCovariance P
        (fun ω => Z ω root₂) (fun ω => Z ω root₁) := by
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by ring)
  have hexp (ω : Ω) :
      (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
          (fun ω => Z ω root₁) +
        (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
          (fun ω => Z ω root₂))) =
        g ^ 2 * gaussianCovariance P (fun ω => Z ω root₁)
          (fun ω => Z ω root₂) +
          ((∑ i, tilt i * Z ω i) -
            (∑ i, ∑ j, tilt i * gaussianCovariance P
              (fun ω => Z ω i) (fun ω => Z ω j) * tilt j) / 2) := by
    rw [hlin ω, hquad, hcovsym]
    simp [gaussianVariance]
    ring
  have hfinite : ENNReal.ofReal (Real.exp
      (g ^ 2 * gaussianCovariance P (fun ω => Z ω root₁)
        (fun ω => Z ω root₂))) ≠ ∞ := by simp
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
              (fun ω => Z ω root₁)) +
            (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
              (fun ω => Z ω root₂)))) * B ω ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun ω => by
            have hmul : ENNReal.ofReal (Real.exp
                (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
                  (fun ω => Z ω root₁))) *
                ENNReal.ofReal (Real.exp
                  (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
                    (fun ω => Z ω root₂))) =
                ENNReal.ofReal (Real.exp
                  ((g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
                    (fun ω => Z ω root₁)) +
                  (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
                    (fun ω => Z ω root₂)))) := by
              rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), ← Real.exp_add]
            change (ENNReal.ofReal (Real.exp
                  (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
                    (fun ω => Z ω root₁))) *
                ENNReal.ofReal (Real.exp
                  (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
                    (fun ω => Z ω root₂)))) * B ω = _
            rw [hmul])
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g ^ 2 * gaussianCovariance P (fun ω => Z ω root₁)
            (fun ω => Z ω root₂))) *
          (ENNReal.ofReal (Real.exp
            ((∑ i, tilt i * Z ω i) -
              (∑ i, ∑ j, tilt i * gaussianCovariance P
                (fun ω => Z ω i) (fun ω => Z ω j) * tilt j) / 2)) * B ω) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun ω => by
            change ENNReal.ofReal (Real.exp _) * B ω = _
            rw [hexp ω, Real.exp_add]
            rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
            ac_rfl)
    _ = _ := by
          rw [lintegral_const_mul' _ _ hfinite]


/-- A sharper double-root barrier tail when the coarse variance and covariance errors are a small
fraction of the scale. The exponent approaches the sharp Chernoff rate
`(2g-a)^2 k / 2` as `η` tends to zero. -/
theorem finite_gaussian_tilt_double_root_good_barrier_rate_of_small_error
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z)
    (coarse root₁ root₂ : ι) (k g a C η : ℝ)
    (hg : 0 < g) (hga : a < 2 * g) (hk : 0 < k)
    (hη : 0 < η) (hη1 : η < 1)
    (hCsmall : C ≤ η * k)
    (hoffset : 2 * g * C + 1 ≤ η * (2 * g - a) * k)
    (hvar : |gaussianVariance P (fun ω => Z ω coarse) - k| ≤ C)
    (hcov₁ : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₁) - k| ≤ C)
    (hcov₂ : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₂) - k| ≤ C)
    (h₁₂ : root₁ ≠ root₂) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ i, twoRootTilt root₁ root₂ g i * Z ω i) -
          (∑ i, ∑ j, twoRootTilt root₁ root₂ g i *
            gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
            twoRootTilt root₁ root₂ g j) / 2)) *
      (Set.indicator {ω | Z ω coarse ≤ a * k}
        (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
      ENNReal.ofReal (Real.exp
        (-((1 - η) ^ 2 * (2 * g - a) ^ 2 * k / (2 * (1 + η))))) := by
  classical
  let tilt : ι → ℝ := twoRootTilt root₁ root₂ g
  let m : ℝ := ∑ i, gaussianCovariance P (fun ω => Z ω coarse)
    (fun ω => Z ω i) * tilt i
  have hm : m = g * gaussianCovariance P (fun ω => Z ω coarse)
        (fun ω => Z ω root₁) +
      g * gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₂) := by
    dsimp only [m]
    have hpoint (i : ι) :
        gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω i) * tilt i =
          (if i = root₁ then gaussianCovariance P (fun ω => Z ω coarse)
            (fun ω => Z ω i) * g else 0) +
          (if i = root₂ then gaussianCovariance P (fun ω => Z ω coarse)
            (fun ω => Z ω i) * g else 0) := by
      by_cases hi₁ : i = root₁
      · subst i
        change gaussianCovariance P (fun ω => Z ω coarse)
            (fun ω => Z ω root₁) *
            (if root₁ = root₁ then g else if root₁ = root₂ then g else 0) =
          (if root₁ = root₁ then
            gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₁) * g
            else 0) +
          (if root₁ = root₂ then
            gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₁) * g
            else 0)
        simp [h₁₂]
      · by_cases hi₂ : i = root₂
        · subst i
          change gaussianCovariance P (fun ω => Z ω coarse)
              (fun ω => Z ω root₂) *
              (if root₂ = root₁ then g else if root₂ = root₂ then g else 0) =
            (if root₂ = root₁ then
              gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₂) * g
              else 0) +
            (if root₂ = root₂ then
              gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₂) * g
              else 0)
          simp [hi₁]
        · simp [tilt, twoRootTilt, hi₁, hi₂]
    rw [show (∑ i, gaussianCovariance P (fun ω => Z ω coarse)
        (fun ω => Z ω i) * tilt i) =
        ∑ i, ((if i = root₁ then gaussianCovariance P (fun ω => Z ω coarse)
          (fun ω => Z ω i) * g else 0) +
          (if i = root₂ then gaussianCovariance P (fun ω => Z ω coarse)
            (fun ω => Z ω i) * g else 0)) by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
    ring
  have hcov₁lower : k - C ≤ gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₁) := by linarith [(abs_le.mp hcov₁).1]
  have hcov₂lower : k - C ≤ gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₂) := by linarith [(abs_le.mp hcov₂).1]
  have hmLower : 2 * g * k - 2 * g * C ≤ m := by
    rw [hm]
    have h₁ := mul_le_mul_of_nonneg_left hcov₁lower hg.le
    have h₂ := mul_le_mul_of_nonneg_left hcov₂lower hg.le
    linarith only [h₁, h₂]
  have hbpos : 0 < 2 * g - a := sub_pos.mpr hga
  have hvarLower : k - C ≤ gaussianVariance P (fun ω => Z ω coarse) := by
    linarith [(abs_le.mp hvar).1]
  have hvarUpper : gaussianVariance P (fun ω => Z ω coarse) ≤ (1 + η) * k := by
    have h := (abs_le.mp hvar).2
    linarith only [h, hCsmall]
  have hv : 0 < gaussianVariance P (fun ω => Z ω coarse) := by
    have hηk : η * k < 1 * k := mul_lt_mul_of_pos_right hη1 hk
    have hCk : C < k := by linarith only [hCsmall, hηk]
    linarith only [hvarLower, hCk]
  have hbarrierGap : (1 - η) * (2 * g - a) * k ≤ m - (a * k + 1) := by
    rw [show (1 - η) * (2 * g - a) * k =
      (2 * g - a) * k - η * (2 * g - a) * k by ring]
    rw [show (a * k + 1) = a * k + 1 by rfl]
    linarith only [hmLower, hoffset]
  have hrate : Real.exp (-(m - (a * k + 1)) ^ 2 /
      (2 * gaussianVariance P (fun ω => Z ω coarse))) ≤
      Real.exp (-((1 - η) ^ 2 * (2 * g - a) ^ 2 * k / (2 * (1 + η)))) := by
    have hden : 0 < 2 * gaussianVariance P (fun ω => Z ω coarse) := by positivity
    have hdist0 : 0 ≤ (1 - η) * (2 * g - a) * k := by positivity
    have hquad : (1 - η) ^ 2 * (2 * g - a) ^ 2 * k /
        (2 * (1 + η)) ≤
        (m - (a * k + 1)) ^ 2 /
          (2 * gaussianVariance P (fun ω => Z ω coarse)) := by
      apply (le_div_iff₀ hden).2
      calc
        ((1 - η) ^ 2 * (2 * g - a) ^ 2 * k /
            (2 * (1 + η))) *
            (2 * gaussianVariance P (fun ω => Z ω coarse) : ℝ) ≤
          ((1 - η) ^ 2 * (2 * g - a) ^ 2 * k /
            (2 * (1 + η))) * (2 * ((1 + η) * k)) := by
              apply mul_le_mul_of_nonneg_left
              · linarith only [hvarUpper]
              · positivity
        _ = ((1 - η) * (2 * g - a) * k) ^ 2 := by field_simp
        _ ≤ (m - (a * k + 1)) ^ 2 := by
              exact pow_le_pow_left₀ hdist0 hbarrierGap 2
    exact Real.exp_le_exp.mpr (by
      rw [neg_div]
      exact neg_le_neg hquad)
  have hgapTail : a * k + 1 < m := by
    have hpositive : 0 < (1 - η) * (2 * g - a) * k := by positivity
    linarith [hbarrierGap]
  have htilt := finite_gaussian_tilt_barrier_lower_tail_bound P Z hZ tilt coarse
    (a * k + 1) hgapTail hv
  have hclosed (ω : Ω) :
      (Set.indicator {ω | Z ω coarse ≤ a * k} (fun _ => (1 : ℝ≥0∞)) ω) ≤
        (Set.indicator {ω | Z ω coarse < a * k + 1}
          (fun _ => (1 : ℝ≥0∞)) ω) := by
    change (if Z ω coarse ≤ a * k then (1 : ℝ≥0∞) else 0) ≤
      if Z ω coarse < a * k + 1 then 1 else 0
    by_cases h : Z ω coarse ≤ a * k
    · have h' : Z ω coarse < a * k + 1 := by linarith
      simp [h, h']
    · simp [h]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ i, tilt i * Z ω i) -
            (∑ i, ∑ j, tilt i * gaussianCovariance P
              (fun ω => Z ω i) (fun ω => Z ω j) * tilt j) / 2)) *
          (Set.indicator {ω | Z ω coarse < a * k + 1}
            (fun _ => (1 : ℝ≥0∞)) ω) ∂P := by
          apply lintegral_mono_ae
          exact ae_of_all _ (fun ω => by
            have hweight : 0 ≤ ENNReal.ofReal (Real.exp
                ((∑ i, tilt i * Z ω i) -
                  (∑ i, ∑ j, tilt i * gaussianCovariance P
                    (fun ω => Z ω i) (fun ω => Z ω j) * tilt j) / 2)) := by
              positivity
            exact mul_le_mul_of_nonneg_left (hclosed ω) hweight)
    _ ≤ ENNReal.ofReal (Real.exp
          (-((m - (a * k + 1)) ^ 2 /
            (2 * gaussianVariance P (fun ω => Z ω coarse))))) := by
          have hmean : (∑ i, gaussianCovariance P (fun ω => Z ω coarse)
              (fun ω => Z ω i) * tilt i) = m := rfl
          rw [← hmean]
          simpa [neg_div] using htilt
    _ ≤ ENNReal.ofReal (Real.exp
          (-((1 - η) ^ 2 * (2 * g - a) ^ 2 * k / (2 * (1 + η))))) := by
          simpa [neg_div] using ENNReal.ofReal_le_ofReal hrate

/-- A one-coordinate specialization of the finite tilted barrier estimate. -/
theorem finite_gaussian_tilt_coordinate_tail_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (i j : ι)
    (γ b : ℝ)
    (hgap : γ * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i) < b)
    (hv : 0 < gaussianVariance P (fun ω => Z ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))) *
      (Set.indicator {ω | b < Z ω j} (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp
          (-(b - γ * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i)) ^ 2 /
            (2 * gaussianVariance P (fun ω => Z ω j)))) := by
  classical
  let tilt : ι → ℝ := fun k => if k = i then γ else 0
  have hgap' : ∑ k, gaussianCovariance P (fun ω => Z ω j)
      (fun ω => Z ω k) * tilt k < b := by
    simpa [tilt, mul_comm] using hgap
  have hlin (ω : Ω) : ∑ k, tilt k * Z ω k = γ * Z ω i := by
    simp [tilt]
  have hquad : (∑ k, ∑ l, tilt k * gaussianCovariance P
      (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) =
      γ ^ 2 * gaussianVariance P (fun ω => Z ω i) := by
    simp [tilt, gaussianVariance]
    ring
  have hshift : ∑ k, gaussianCovariance P (fun ω => Z ω j)
      (fun ω => Z ω k) * tilt k =
        γ * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i) := by
    simp [tilt]
    ring
  have hgen := finite_gaussian_tilt_barrier_tail_bound P Z hZ tilt j b hgap' hv
  have hweight (ω : Ω) : Real.exp
      (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i)) =
      Real.exp ((∑ k, tilt k * Z ω k) -
        (∑ k, ∑ l, tilt k * gaussianCovariance P
          (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2) := by
    congr 1
    rw [← hlin ω]
    rw [hquad]
    ring
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ k, tilt k * Z ω k) -
          (∑ k, ∑ l, tilt k * gaussianCovariance P
            (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
          (Set.indicator {ω | b < Z ω j} (fun _ => (1 : ℝ≥0∞)) ω) ∂P := by
            apply lintegral_congr_ae
            exact ae_of_all _ (fun ω => by
              change ENNReal.ofReal (Real.exp
                  (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P
                    (fun ω' => Z ω' i))) *
                (Set.indicator {ω' | b < Z ω' j}
                  (fun _ => (1 : ℝ≥0∞)) ω) =
                ENNReal.ofReal (Real.exp
                  ((∑ k, tilt k * Z ω k) -
                    (∑ k, ∑ l, tilt k * gaussianCovariance P
                      (fun ω' => Z ω' k) (fun ω' => Z ω' l) * tilt l) / 2)) *
                  (Set.indicator {ω' | b < Z ω' j}
                    (fun _ => (1 : ℝ≥0∞)) ω)
              rw [hweight ω])
    _ ≤ ENNReal.ofReal (Real.exp
        (-(b - ∑ k, gaussianCovariance P (fun ω => Z ω j)
          (fun ω => Z ω k) * tilt k) ^ 2 /
          (2 * gaussianVariance P (fun ω => Z ω j)))) := hgen
    _ = _ := by rw [hshift]


/-- Once the barrier slope exceeds the tilted mean slope, Gaussian tails decay exponentially
uniformly when the variance is at most linear in the scale. -/
theorem gaussian_barrier_tail_rate
    (a g C m v k : ℝ)
    (hgap : g < a) (hk : 0 < k)
    (hC : C ≤ (a - g) * k / 2)
    (hmean : m ≤ g * k + C)
    (hv : 0 < v) (hvUpper : v ≤ 2 * k) :
    Real.exp (-((a * k - m) ^ 2) / (2 * v)) ≤
      Real.exp (-((a - g) ^ 2 * k / 16)) := by
  have hdist : (a - g) * k / 2 ≤ a * k - m := by
    linarith only [hC, hmean]
  have hdist0 : 0 ≤ (a - g) * k / 2 := by positivity
  have hden : 0 < 2 * v := by positivity
  have hquad : (a - g) ^ 2 * k / 16 ≤ (a * k - m) ^ 2 / (2 * v) := by
    apply (le_div_iff₀ hden).2
    calc
      ((a - g) ^ 2 * k / 16) * (2 * v) ≤
          ((a - g) ^ 2 * k / 16) * (4 * k) := by
            apply mul_le_mul_of_nonneg_left
            · linarith only [hvUpper]
            · positivity
      _ = ((a - g) * k / 2) ^ 2 := by ring
      _ ≤ (a * k - m) ^ 2 := pow_le_pow_left₀ hdist0 hdist 2
  apply Real.exp_le_exp.mpr
  calc
    -((a * k - m) ^ 2) / (2 * v) =
        -((a * k - m) ^ 2 / (2 * v)) := by rw [neg_div]
    _ ≤ -((a - g) ^ 2 * k / 16) := neg_le_neg hquad

/-- A one-root Wick tilt has an exponentially small coarse-scale barrier tail when the tilted
mean and variance differ from their linear scale asymptotics by a bounded amount. This is the
uniform estimate used for the discarded mass in the good/bad circle construction. -/
theorem finite_gaussian_tilt_coarse_barrier_tail_rate
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (fine coarse : ι)
    (k g a C : ℝ) (hg : 0 < g) (hga : g < a) (hk : 0 < k)
    (hCk : C < k)
    (hvar : |gaussianVariance P (fun ω => Z ω coarse) - k| ≤ C)
    (hcov : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω fine) - k| ≤ C)
    (hgapScale : g * C ≤ (a - g) * k / 2) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * Z ω fine - g ^ 2 / 2 * gaussianVariance P (fun ω => Z ω fine))) *
      (Set.indicator {ω | a * k < Z ω coarse}
        (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
      ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * k / 16))) := by
  have hcovUpper : gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω fine) ≤ k + C := by
    have := (abs_le.mp hcov).2
    linarith only [this]
  have hmean : g * gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω fine) ≤ g * k + g * C := by
    calc
      _ ≤ g * (k + C) := mul_le_mul_of_nonneg_left hcovUpper hg.le
      _ = g * k + g * C := by ring
  have hbarrierGap : g * gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω fine) < a * k := by
    have hstrict : g * k + g * C < a * k := by
      calc
        g * k + g * C ≤ g * k + (a - g) * k / 2 := by linarith only [hgapScale]
        _ < a * k := by linarith only [mul_pos (sub_pos.mpr hga) hk]
    linarith only [hmean, hstrict]
  have hvarLower : k - C ≤ gaussianVariance P (fun ω => Z ω coarse) := by
    have := (abs_le.mp hvar).1
    linarith only [this]
  have hvarUpper : gaussianVariance P (fun ω => Z ω coarse) ≤ k + C := by
    have := (abs_le.mp hvar).2
    linarith only [this]
  have hvariancePos : 0 < gaussianVariance P (fun ω => Z ω coarse) := by
    linarith only [hvarLower, hCk]
  have hvarianceUpper : gaussianVariance P (fun ω => Z ω coarse) ≤ 2 * k := by
    linarith only [hvarUpper, hCk]
  have hgapRate : g * C ≤ (a - g) * k / 2 := hgapScale
  have hmeanRate : g * gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω fine) ≤ g * k + g * C := hmean
  have hrate := gaussian_barrier_tail_rate a g (g * C)
    (g * gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω fine))
    (gaussianVariance P (fun ω => Z ω coarse)) k hga hk hgapRate hmeanRate
    hvariancePos hvarianceUpper
  calc
    _ ≤ ENNReal.ofReal (Real.exp
        (-(a * k - g * gaussianCovariance P (fun ω => Z ω coarse)
          (fun ω => Z ω fine)) ^ 2 /
          (2 * gaussianVariance P (fun ω => Z ω coarse)))) := by
            have htail := finite_gaussian_tilt_coordinate_tail_bound P Z hZ fine coarse
              g (a * k) hbarrierGap hvariancePos
            simpa only [mul_comm] using htail
    _ ≤ ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * k / 16))) := by
          exact ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (by simpa [mul_comm] using hrate))

/-- The exponential barrier tail appearing in the good/bad construction is summable in the
integer scale whenever its rate is positive. -/
theorem summable_gaussian_barrier_tail (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
  have hratio0 : 0 ≤ Real.exp (-c) := Real.exp_nonneg _
  have hratio1 : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith only [hc])
  have hgeom := summable_geometric_of_lt_one hratio0 hratio1
  have hfun : (fun k : ℕ => Real.exp (-c * (k : ℝ))) =
      fun k => Real.exp (-c) ^ k := by
    funext k
    rw [show -c * (k : ℝ) = (k : ℝ) * (-c) by ring, Real.exp_nat_mul]
  rw [hfun]
  exact hgeom



/-- The same spatial covariance calculation for a general exponential tail `exp (-θ k)`.
Separating the tail rate from its origin lets the sharp small-error two-root estimate feed into
the spatial power bound without replacing its exponent by a coarser square. -/
theorem good_barrier_kernel_power_bound_of_rate
    (g θ κ C cov k d ρ : ℝ)
    (hθ : 0 ≤ θ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (hdρ : d ≤ ρ)
    (hcov : cov ≤ Real.log (1 / ρ) + C)
    (hk : Real.log (1 / ρ) - 1 < k)
    (hκ : 0 ≤ κ) (hgap : g ^ 2 - θ ≤ κ) :
    Real.exp (g ^ 2 * cov) * Real.exp (-θ * k) ≤
      Real.exp (g ^ 2 * C + θ) * d ^ (-κ) := by
  have hlogρ : 0 ≤ Real.log (1 / ρ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hρ).2
    linarith only [hρ1]
  have hinv : 1 / ρ ≤ 1 / d := by
    apply (div_le_div_iff₀ hρ hd).2
    linarith only [hdρ]
  have hlog : Real.log (1 / ρ) ≤ Real.log (1 / d) :=
    Real.log_le_log (by positivity) hinv
  have hcov' := mul_le_mul_of_nonneg_left hcov (sq_nonneg g)
  have hk' : -θ * k ≤ -θ * (Real.log (1 / ρ) - 1) :=
    mul_le_mul_of_nonpos_left (le_of_lt hk) (by linarith only [hθ])
  have hexponent : g ^ 2 * cov - θ * k ≤
      g ^ 2 * C + θ + κ * Real.log (1 / d) := by
    calc
      g ^ 2 * cov - θ * k = g ^ 2 * cov + (-θ * k) := by ring
      _ ≤ g ^ 2 * (Real.log (1 / ρ) + C) +
          (-θ * (Real.log (1 / ρ) - 1)) := add_le_add hcov' hk'
      _ = g ^ 2 * C + θ + (g ^ 2 - θ) * Real.log (1 / ρ) := by ring
      _ ≤ g ^ 2 * C + θ + κ * Real.log (1 / ρ) := by
          linarith only [mul_le_mul_of_nonneg_right hgap hlogρ]
      _ ≤ g ^ 2 * C + θ + κ * Real.log (1 / d) := by
          linarith only [mul_le_mul_of_nonneg_left hlog hκ]
  have hExp := Real.exp_le_exp.mpr hexponent
  have hfactor : Real.exp (g ^ 2 * C + θ + κ * Real.log (1 / d)) =
      Real.exp (g ^ 2 * C + θ) * d ^ (-κ) := by
    rw [Real.exp_add, Real.rpow_def_of_pos hd]
    simp only [one_div, Real.log_inv]
    congr 1
    ring_nf
  calc
    Real.exp (g ^ 2 * cov) * Real.exp (-θ * k) =
        Real.exp (g ^ 2 * cov - θ * k) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ ≤ Real.exp (g ^ 2 * C + θ + κ * Real.log (1 / d)) := hExp
    _ = _ := hfactor

/-- A pair of Wick roots restricted to the good coarse barrier has the expected spatial power
bound once the admissible covariance errors are small relative to scale. The two-root tilt tail
and the logarithmic cross-covariance estimate enter separately, matching the good-mass second
moment calculation. -/
theorem finite_gaussian_wick_pair_good_barrier_power_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z)
    (root₁ root₂ coarse : ι) (h₁₂ : root₁ ≠ root₂)
    (g a C η k d ρ κ : ℝ)
    (hg : 0 < g) (hga : a < 2 * g) (hk : 0 < k)
    (hη : 0 < η) (hη1 : η < 1)
    (hCsmall : C ≤ η * k)
    (hoffset : 2 * g * C + 1 ≤ η * (2 * g - a) * k)
    (hvar : |gaussianVariance P (fun ω => Z ω coarse) - k| ≤ C)
    (hcov₁ : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₁) - k| ≤ C)
    (hcov₂ : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₂) - k| ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (hdρ : d ≤ ρ)
    (hcov : gaussianCovariance P (fun ω => Z ω root₁)
      (fun ω => Z ω root₂) ≤ Real.log (1 / ρ) + C)
    (hfloor : Real.log (1 / ρ) - 1 < k)
    (hκ : 0 ≤ κ)
    (hκrate : g ^ 2 -
      ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₁))) *
      ENNReal.ofReal (Real.exp
        (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₂))) *
      Set.indicator {ω | Z ω coarse ≤ a * k} (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ENNReal.ofReal ((Real.exp (g ^ 2 * C +
        ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) * d ^ (-κ))) := by
  let θ : ℝ := (1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))
  let good : Ω → ℝ≥0∞ := Set.indicator {ω | Z ω coarse ≤ a * k}
    (fun _ => (1 : ℝ≥0∞))
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have htail := finite_gaussian_tilt_double_root_good_barrier_rate_of_small_error
    P Z hZ coarse root₁ root₂ k g a C η hg hga hk hη hη1 hCsmall hoffset
    hvar hcov₁ hcov₂ h₁₂
  have hpair := finite_gaussian_two_root_wick_tilt_integral_identity
    P Z root₁ root₂ h₁₂ g good
  have hkernel := good_barrier_kernel_power_bound_of_rate
    g θ κ C (gaussianCovariance P (fun ω => Z ω root₁)
      (fun ω => Z ω root₂)) k d ρ hθ hρ hρ1 hd hdρ hcov hfloor hκ (by
        dsimp [θ]
        exact hκrate)
  have htail' : ∫⁻ ω, ENNReal.ofReal (Real.exp
      ((∑ i, twoRootTilt root₁ root₂ g i * Z ω i) -
        (∑ i, ∑ j, twoRootTilt root₁ root₂ g i *
          gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
          twoRootTilt root₁ root₂ g j) / 2)) * good ω ∂P ≤
      ENNReal.ofReal (Real.exp (-θ * k)) := by
    simpa [good, θ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htail
  have hfactor : ENNReal.ofReal
        (Real.exp (g ^ 2 * gaussianCovariance P (fun ω => Z ω root₁)
          (fun ω => Z ω root₂))) * ENNReal.ofReal (Real.exp (-θ * k)) ≤
      ENNReal.ofReal (Real.exp (g ^ 2 * C + θ) * d ^ (-κ)) := by
    have hreal := hkernel
    have hprod : Real.exp (g ^ 2 * gaussianCovariance P
        (fun ω => Z ω root₁) (fun ω => Z ω root₂)) * Real.exp (-θ * k) ≤
        Real.exp (g ^ 2 * C + θ) * d ^ (-κ) := hreal
    simpa only [← ENNReal.ofReal_mul (Real.exp_nonneg _)] using
      ENNReal.ofReal_le_ofReal hprod
  calc
    _ = ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
          (fun ω => Z ω root₁) (fun ω => Z ω root₂))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ i, twoRootTilt root₁ root₂ g i * Z ω i) -
            (∑ i, ∑ j, twoRootTilt root₁ root₂ g i *
              gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
              twoRootTilt root₁ root₂ g j) / 2)) * good ω ∂P := by
          simpa [good, mul_assoc] using hpair
    _ ≤ ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
          (fun ω => Z ω root₁) (fun ω => Z ω root₂))) *
        ENNReal.ofReal (Real.exp (-θ * k)) := by
          exact mul_le_mul_of_nonneg_left htail' bot_le
    _ ≤ ENNReal.ofReal (Real.exp (g ^ 2 * C + θ) * d ^ (-κ)) := hfactor
    _ = ENNReal.ofReal (Real.exp (g ^ 2 * C +
          ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) * d ^ (-κ)) := by
          rfl

/-- A fixed subcritical charge admits a barrier slope whose two-root power is locally integrable.
This is the scalar parameter choice underlying the good-mass construction. -/
theorem exists_fixed_charge_barrier_parameters (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ a κ : ℝ, γ < a ∧ a < 2 * γ ∧
      κ = γ ^ 2 - (2 * γ - a) ^ 2 / 2 ∧ 0 < κ ∧ κ < 2 := by
  let gap : ℝ := 2 - γ ^ 2 / 2
  let δ : ℝ := min (γ / 2) (gap / (2 * γ + 1))
  have hgap : 0 < gap := by
    have hγsq : γ ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero
    dsimp [gap]
    linarith only [hγsq]
  have hden : 0 < 2 * γ + 1 := by positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith only [hγ]) (div_pos hgap hden)
  have hδγ : δ ≤ γ / 2 := min_le_left _ _
  have hδgap : δ ≤ gap / (2 * γ + 1) := min_le_right _ _
  have hδgap' : (2 * γ + 1) * δ ≤ gap := by
    calc
      (2 * γ + 1) * δ = δ * (2 * γ + 1) := mul_comm _ _
      _ ≤ gap := (le_div_iff₀ hden).mp hδgap
  have hγδ : γ * δ < gap := by
    calc
      γ * δ < (2 * γ + 1) * δ :=
        mul_lt_mul_of_pos_right (by linarith only [hγ]) hδpos
      _ ≤ gap := hδgap'
  refine ⟨γ + δ, γ ^ 2 - (2 * γ - (γ + δ)) ^ 2 / 2, ?_, ?_, rfl, ?_, ?_⟩
  · exact lt_add_of_pos_right _ hδpos
  · linarith only [hδγ, hγ]
  · have hδlt : δ < γ := by linarith only [hδγ, hγ]
    have hsq : (γ - δ) ^ 2 ≤ γ ^ 2 := by
      linarith only [mul_nonneg hδpos.le (show (0 : ℝ) ≤ 2 * γ - δ by linarith only [hδlt, hγ])]
    rw [show 2 * γ - (γ + δ) = γ - δ by ring]
    linarith only [hsq, sq_pos_of_pos hγ]
  · rw [show 2 * γ - (γ + δ) = γ - δ by ring]
    dsimp [gap] at hγδ
    linarith only [hγδ, sq_nonneg δ]

end DOZZ.Proofs
