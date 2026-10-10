/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.PoleSubtracted.Tilt
public import DOZZ.GMC.Construction.GMCGeneralTiltLimit
public import DOZZ.GMC.CircleAverageLimits
public import DOZZ.GMC.CircleAverage
public import DOZZ.GFFStructure.CirclePotential
import DOZZ.ShiftEquations.Mobius.AffineMoment
import Mathlib.Tactic
/-! # Circle tilt at arbitrary nonnegative real times -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- The circle of radius `e^{-m}` at the origin, written as a repinning circle. -/
theorem reflected_circleMeasure_origin_repin (m : ℝ) :
    circleMeasure 0 (-Real.log ‖((Real.exp (-m) : ℝ) : ℂ)‖) = circleMeasure 0 m := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]

/-- On the circle of radius `e^{-m} ≤ 1` the background `log |·|_+` vanishes. -/
theorem reflected_integral_log_normPlus_circle_origin (m : ℝ) (hm : 0 ≤ m) :
    ∫ w, Real.log (normPlus w) ∂circleMeasure 0 m = 0 := by
  have hae : (fun w => Real.log (normPlus w)) =ᵐ[circleMeasure 0 m] fun _ => (0 : ℝ) := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 m] with w hw
    rw [sub_zero] at hw
    have hle : ‖w‖ ≤ 1 := by
      rw [hw]
      exact Real.exp_le_one_iff.mpr (by
        have := hm
        linarith)
    rw [normPlus, max_eq_left hle, Real.log_one]
  rw [integral_congr_ae hae, integral_zero]

/-- **The potential of the circle at the origin**:
`∫ G(x,u) dσ_{0,e^{-m}}(u) = log |x|_+ - log max(e^{-m}, |x|)`. -/
theorem reflected_repinPotential_origin (m : ℝ) (hm : 0 ≤ m) (x : ℂ) :
    repinPotential ((Real.exp (-m) : ℝ) : ℂ) 0 x =
      Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖) := by
  have ha : ((Real.exp (-m) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [repinPotential_eq _ 0 ha x, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), zero_sub, norm_neg]
  have hc : repinConst ((Real.exp (-m) : ℝ) : ℂ) 0 = 0 := by
    unfold repinConst
    rw [reflected_circleMeasure_origin_repin]
    exact reflected_integral_log_normPlus_circle_origin m hm
  rw [hc]
  ring

/-- The circle average at the origin at radius `e^{-m}` has variance `m`. -/
theorem reflected_gaussianVariance_circleAverage_origin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (m : ℝ) (hm : 0 ≤ m) :
    gaussianVariance P (fun ω => Xc ω 0 m) = m := by
  have _ := circleMeasure_isProbability 0 m
  unfold gaussianVariance
  rw [isCircleAverage_covariance P X hX Xc hXc 0 0 m m]
  have hinner : ∀ u, ∫ v, gffKernel u v ∂circleMeasure 0 m =
      Real.log (normPlus u) - Real.log (max (Real.exp (-m)) ‖u‖) := fun u => by
    rw [← reflected_repinPotential_origin m hm u, repinPotential, reflected_circleMeasure_origin_repin]
  simp_rw [hinner]
  have hae : (fun u : ℂ => Real.log (normPlus u) - Real.log (max (Real.exp (-m)) ‖u‖))
      =ᵐ[circleMeasure 0 m] fun _ => m := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 m] with u hu
    rw [sub_zero] at hu
    have hle : ‖u‖ ≤ 1 := by
      rw [hu]
      exact Real.exp_le_one_iff.mpr (by
        have := hm
        linarith)
    rw [normPlus, max_eq_left hle, Real.log_one, hu, max_self, Real.log_exp]
    ring
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]

/-- **Cameron–Martin tilt by the circle average at the origin.** For real `a`, `m ∈ ℕ` and every
measurable functional `H` of the chaos,
`E[e^{a X_m(0) - m a²/2} H(M)] = E[H(e^{γ a Cov(X(·), X_m(0))} M)]`. -/
theorem reflected_lintegral_circleTilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (a m : ℝ) (hm : 0 ≤ m) (H : Measure ℂ → ℝ≥0∞)
    (hH : Measurable H) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) * H (M ω) ∂P =
      ∫⁻ ω, H ((M ω).withDensity ((fun x : ℂ => ENNReal.ofReal (Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖))))))) ∂P := by
  set a' : ℂ := ((Real.exp (-m) : ℝ) : ℂ) with ha'def
  have ha' : a' ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  set L : Ω → ℝ := fun ω => a * Xc ω 0 m with hLdef
  have hL : IsGaussianL2Limit P X L :=
    IsGaussianL2Limit.const_mul (isCircleAverage_isGaussianL2Limit P X hX Xc hXc 0 m) a
  have hVar : gaussianVariance P L = a ^ 2 * m := by
    have h := reflected_gaussianVariance_circleAverage_origin P X hX Xc hXc m hm
    simp only [gaussianVariance, gaussianCovariance] at h ⊢
    have hfun : (fun ω => L ω * L ω) = fun ω => a ^ 2 * (Xc ω 0 m * Xc ω 0 m) := by
      funext ω
      simp only [hLdef]
      ring
    rw [hfun, integral_const_mul, h]
  obtain ⟨B, hB⟩ := exists_abs_repinPotential_le a' 0 ha'
  set c : BoundedContinuousFunction ℂ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => a * repinPotential a' 0 x) (continuous_const.mul (continuous_repinPotential a' 0 ha'))
    (|a| * B) (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)) with hcdef
  have hcx : ∀ x, c x = a * repinPotential a' 0 x := fun x => rfl
  have hK : ∀ r x, gaussianCovariance P (fun ω => Xc ω x r) L =
      a * repinPotentialAvg a' 0 r x := by
    intro r x
    have h := isCircleAverage_covariance P X hX Xc hXc x 0 r m
    rw [← reflected_circleMeasure_origin_repin m] at h
    simp only [gaussianCovariance] at h ⊢
    rw [show repinPotentialAvg a' 0 r x =
        ∫ u, ∫ v, gffKernel u v ∂circleMeasure 0 (-Real.log ‖a'‖) ∂circleMeasure x r from rfl,
      ← h, ← integral_const_mul]
    congr 1
    funext ω
    simp only [hLdef]
    ring
  have hc : TendstoUniformly (fun (r : ℝ) (x : ℂ) =>
      gaussianCovariance P (fun ω => Xc ω x r) L) c atTop := by
    simp_rw [hK]
    have hu := tendstoUniformly_repinPotential a' 0 ha'
    rw [Metric.tendstoUniformly_iff] at hu ⊢
    intro ε hε
    have hpos : 0 < |a| + 1 := by positivity
    filter_upwards [hu (ε / (|a| + 1)) (div_pos hε hpos)] with r hr x
    have h1 := hr x
    rw [Real.dist_eq] at h1 ⊢
    rw [hcx, ← mul_sub, abs_mul]
    calc |a| * |repinPotential a' 0 x - repinPotentialAvg a' 0 r x|
        ≤ |a| * (ε / (|a| + 1)) := mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hpos]
          nlinarith [abs_nonneg a]
  have htilt := equatorGFF_GMC_tilt P X hX γ hγ hγ2 M hM Xc hXc L hL c hc
    (fun _ μ => H μ) (hH.comp measurable_snd)
  have hdens : (fun x => ENNReal.ofReal (Real.exp (γ * c x))) = (fun x : ℂ => ENNReal.ofReal (Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖))))) := by
    funext x
    rw [hcx, reflected_repinPotential_origin m hm x]
    congr 2
    ring
  have hexp : ∀ ω, Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) =
      Real.exp (L ω - gaussianVariance P L / 2) := fun ω => by
    rw [hVar]
    congr 1
    simp only [hLdef]
    ring
  simp_rw [hexp]
  rw [htilt, hdens]

end DOZZ.Proofs
