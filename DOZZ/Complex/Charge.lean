/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.MeanInequalities
public import DOZZ.Complex.Weierstrass

/-!
# Holomorphic Gaussian charge moments

The random exponential is differentiated jointly on a local polydisc. Its
value and first derivative are dominated by the correlated Gaussian/mass
logarithm envelope. The deterministic factor `exp(c z)` is then restored.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex ProbabilityTheory
open scoped Real

namespace DOZZ.Proofs

/-- All real powers below the positive threshold are integrable. -/
theorem integrable_mass_power {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → ℝ) (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (t : ℝ) (ht : t < pstar) : Integrable (fun ω => A ω ^ t) P := by
  by_cases h : 0 ≤ t
  · exact hmom t h ht
  · simpa only [neg_neg] using hinv (-t) (neg_pos.mpr (lt_of_not_ge h))

/-- The strict threshold leaves room for a Hölder exponent larger than one. -/
theorem exists_holder_mass_exponent (t pstar : ℝ) (ht : t < pstar) :
    ∃ p : ℝ, 1 < p ∧ p * t < pstar := by
  have hn : {p : ℝ | p * t < pstar} ∈ 𝓝 1 :=
    (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds
      (isOpen_Iio.mem_nhds (show (1 : ℝ) * t ∈ Iio pstar by simpa only [Set.mem_Iio, one_mul] using ht))
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨1 + ε / 2, by linarith, hb ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

/-- A Gaussian random variable has all linear exponential norm moments. -/
theorem integrable_gaussian_exp_norm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (P : Measure Ω)
    (L : Ω → E) (hL : HasGaussianLaw L P) (K : ℝ) :
    Integrable (fun ω => Real.exp (K * ‖L ω‖)) P := by
  let _ := hL.isGaussian_map
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq (P.map L)
  have hgauss : Integrable (fun ω => Real.exp (C * ‖L ω‖ ^ 2)) P :=
    (integrable_map_measure (by fun_prop) hL.aemeasurable).mp hint
  apply (hgauss.const_mul (Real.exp (K ^ 2 / (4 * C)))).mono'
    ((hL.aemeasurable.norm.const_mul K).exp.aestronglyMeasurable)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hden : 0 < 4 * C := by positivity
    apply (mul_le_mul_iff_right₀ hden).mp
    have heq : (4 * C) * (K ^ 2 / (4 * C) + C * ‖L ω‖ ^ 2) =
        K ^ 2 + 4 * C ^ 2 * ‖L ω‖ ^ 2 := by field_simp
    rw [heq]
    have hs' : 0 ≤ (2 * C * ‖L ω‖ - K) ^ 2 := sq_nonneg _
    nlinarith

/-- The sum of coordinate absolute values is measurable. -/
theorem aemeasurable_gaussian_coordinate_sum {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P) :
    AEMeasurable (fun ω => ∑ i, |L ω i|) P := by
  have hcoord : ∀ i, AEMeasurable (fun ω => |L ω i|) P := by
    intro i
    have hi : AEMeasurable (fun ω => L ω i) P :=
      (measurable_pi_apply i).comp_aemeasurable hL.aemeasurable
    simpa only [Real.norm_eq_abs] using hi.norm
  exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ => hcoord i)

/-- All linear exponential moments of the sum of Gaussian coordinate absolute values exist. -/
theorem integrable_gaussian_exp_coordinate_sum {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (K : ℝ) (hK : 0 ≤ K) : Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|)) P := by
  apply (integrable_gaussian_exp_norm P L hL (K * N)).mono'
    (((aemeasurable_gaussian_coordinate_sum P L hL).const_mul K).exp.aestronglyMeasurable)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hs : ∑ i, |L ω i| ≤ (N : ℝ) * ‖L ω‖ := by
      calc
        _ ≤ ∑ i : Fin N, ‖L ω‖ := Finset.sum_le_sum fun i _ => by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (L ω) i
        _ = _ := by simp
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hK

/-- Young's inequality proves correlated Gaussian/mass integrability below the threshold. -/
theorem integrable_gaussian_exp_mass_power {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (K : ℝ) (hK : 0 ≤ K) (t : ℝ) (ht : t < pstar) :
    Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ t) P := by
  obtain ⟨p, hp, hpt⟩ := exists_holder_mass_exponent t pstar ht
  have hpq := Real.HolderConjugate.conjExponent hp
  have hmass := integrable_mass_power P A pstar hinv hmom (p * t) hpt
  have hgauss := integrable_gaussian_exp_coordinate_sum P L hL
    (K * Real.conjExponent p) (mul_nonneg hK hpq.symm.nonneg)
  apply ((hmass.div_const p).add (hgauss.div_const (Real.conjExponent p))).mono'
    ((((aemeasurable_gaussian_coordinate_sum P L hL).const_mul K).exp.mul
      (hA.pow_const t)).aestronglyMeasurable)
  filter_upwards [hpos] with ω hω
  change ‖Real.exp (K * ∑ i, |L ω i|) * A ω ^ t‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hω _).le)]
  have h := Real.young_inequality_of_nonneg (Real.rpow_pos_of_pos hω t).le
    (Real.exp_pos (K * ∑ i, |L ω i|)).le hpq
  rw [← Real.rpow_mul hω.le, ← Real.exp_mul] at h
  change Real.exp (K * ∑ i, |L ω i|) * A ω ^ t ≤
    A ω ^ (p * t) / p + Real.exp (K * Real.conjExponent p * ∑ i, |L ω i|) / Real.conjExponent p
  have heq : (K * ∑ i, |L ω i|) * Real.conjExponent p =
      K * Real.conjExponent p * ∑ i, |L ω i| := by ring
  rw [heq, mul_comm t p] at h
  simpa only [mul_comm (A ω ^ t) (Real.exp _)] using h

/-- A logarithm is absorbed by arbitrarily small positive and negative powers. -/
theorem abs_log_le_power_sum (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) :
    |Real.log x| ≤ δ⁻¹ * (x ^ δ + x ^ (-δ)) := by
  have hexp : δ * |Real.log x| ≤ Real.exp (δ * |Real.log x|) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hb : Real.exp (δ * |Real.log x|) ≤ x ^ δ + x ^ (-δ) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]
    by_cases hlog : 0 ≤ Real.log x
    · rw [abs_of_nonneg hlog, mul_comm δ]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hlog)]
      have heq : δ * -Real.log x = Real.log x * -δ := by ring
      rw [heq]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left (hexp.trans hb) (inv_nonneg.mpr hδ.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] using h

/-- A Gaussian exponential times a mass power and its logarithm is integrable. -/
theorem integrable_gaussian_exp_mass_power_log {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (K : ℝ) (hK : 0 ≤ K) (t : ℝ) (ht : t < pstar) :
    Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ t * |Real.log (A ω)|) P := by
  let δ := (pstar - t) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr ht)
  have hplus : t + δ < pstar := by dsimp [δ]; linarith
  have hminus : t - δ < pstar := by linarith
  have hint := ((integrable_gaussian_exp_mass_power P L hL A hA hpos pstar hinv hmom K hK
    (t + δ) hplus).add
    (integrable_gaussian_exp_mass_power P L hL A hA hpos pstar hinv hmom K hK
      (t - δ) hminus)).const_mul δ⁻¹
  apply hint.mono' ?_ ?_
  · exact ((((aemeasurable_gaussian_coordinate_sum P L hL).const_mul K).exp.mul
      (hA.pow_const t)).mul (show AEMeasurable (fun ω => |Real.log (A ω)|) P from by
        simpa only [Real.norm_eq_abs] using hA.log.norm)).aestronglyMeasurable
  · filter_upwards [hpos] with ω hω
    change ‖Real.exp (K * ∑ i, |L ω i|) * A ω ^ t * |Real.log (A ω)|‖ ≤
      δ⁻¹ * (Real.exp (K * ∑ i, |L ω i|) * A ω ^ (t + δ) +
        Real.exp (K * ∑ i, |L ω i|) * A ω ^ (t - δ))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := mul_le_mul_of_nonneg_left (abs_log_le_power_sum (A ω) δ hω hδ)
      (mul_nonneg (Real.exp_pos (K * ∑ i, |L ω i|)).le (Real.rpow_pos_of_pos hω t).le)
    rw [Real.rpow_add hω, sub_eq_add_neg, Real.rpow_add hω]
    convert h using 1
    ring

/-- A Gaussian exponential absorbs the sum of absolute Gaussian coordinates. -/
theorem integrable_gaussian_exp_mass_power_sum {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (K : ℝ) (hK : 0 ≤ K) (t : ℝ) (ht : t < pstar) :
    Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ t * (∑ i, |L ω i|)) P := by
  apply (integrable_gaussian_exp_mass_power P L hL A hA hpos pstar hinv hmom
    (K + 1) (by positivity) t ht).mono' ?_ ?_
  · exact ((((aemeasurable_gaussian_coordinate_sum P L hL).const_mul K).exp.mul
      (hA.pow_const t)).mul (aemeasurable_gaussian_coordinate_sum P L hL)).aestronglyMeasurable
  · filter_upwards [hpos] with ω hω
    change ‖Real.exp (K * ∑ i, |L ω i|) * A ω ^ t * (∑ i, |L ω i|)‖ ≤
      Real.exp ((K + 1) * ∑ i, |L ω i|) * A ω ^ t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, one_mul, Real.exp_add]
    have hs : (∑ i, |L ω i|) ≤ Real.exp (∑ i, |L ω i|) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    convert mul_le_mul_of_nonneg_left hs
      (mul_nonneg (Real.exp_pos (K * ∑ i, |L ω i|)).le (Real.rpow_pos_of_pos hω t).le) using 1
    ring

/-- The full first-derivative envelope for a single mass power. -/
theorem integrable_gaussian_mass_envelope_power {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (K : ℝ) (hK : 0 ≤ K) (t : ℝ) (ht : t < pstar) :
    Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ t *
      (1 + ∑ i, |L ω i| + |Real.log (A ω)|)) P := by
  have h := ((integrable_gaussian_exp_mass_power P L hL A hA hpos pstar hinv hmom K hK t ht).add
    (integrable_gaussian_exp_mass_power_sum P L hL A hA hpos pstar hinv hmom K hK t ht)).add
    (integrable_gaussian_exp_mass_power_log P L hL A hA hpos pstar hinv hmom K hK t ht)
  convert h using 1
  ext ω
  simp only [Pi.add_apply]
  ring

/-- The correlated Gaussian/mass/logarithm envelope that dominates the random exponential and
its first derivative. -/
theorem integrable_gaussian_mass_envelope {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (K : ℝ) (hK : 0 ≤ K) (u v : ℝ) (huv : u ≤ v) (hv : v < pstar) :
    Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * (A ω ^ u + A ω ^ v) *
      (1 + ∑ i, |L ω i| + |Real.log (A ω)|)) P := by
  have h := (integrable_gaussian_mass_envelope_power P L hL A hA hpos pstar hinv hmom K hK u
    (huv.trans_lt hv)).add
    (integrable_gaussian_mass_envelope_power P L hL A hA hpos pstar hinv hmom K hK v hv)
  convert h using 1
  ext ω
  simp only [Pi.add_apply]
  ring

/-- The random linear form in the charge exponential. -/
noncomputable def chargeLinear {N : ℕ} (l : Fin N → ℝ) (a : ℝ)
    (sL : (Fin N → ℂ) →L[ℂ] ℂ) : (Fin N → ℂ) →L[ℂ] ℂ :=
  (∑ i, (l i : ℂ) • (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ)) - (a : ℂ) • sL

/-- Evaluation of the charge linear form. -/
theorem chargeLinear_apply {N : ℕ} (l : Fin N → ℝ) (a : ℝ)
    (sL : (Fin N → ℂ) →L[ℂ] ℂ) (z : Fin N → ℂ) :
    chargeLinear l a sL z = (∑ i, z i * (l i : ℂ)) - sL z * (a : ℂ) := by
  simp only [chargeLinear, sub_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  · exact mul_comm _ _

/-- The operator norm of the charge form is bounded by Gaussian coordinates and a logarithm. -/
theorem norm_chargeLinear_le {N : ℕ} (l : Fin N → ℝ) (a : ℝ)
    (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    ‖chargeLinear l a sL‖ ≤ (∑ i, |l i|) + ‖sL‖ * |a| := by
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, norm_real]
    exact (mul_le_mul_of_nonneg_left (norm_coordinate_proj_le_one i) (abs_nonneg _)).trans_eq
      (mul_one _)
  · rw [norm_smul, norm_real, Real.norm_eq_abs, mul_comm]

/-- The actual random charge kernel. -/
noncomputable def chargeKernel {N : ℕ} (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (l : Fin N → ℝ) (A : ℝ) (z : Fin N → ℂ) : ℂ :=
  exp (∑ i, z i * (l i : ℂ)) * (A : ℂ) ^ (-(s₀ + sL z))

/-- Positivity identifies the charge kernel with an exponential of a continuous linear form. -/
theorem chargeKernel_eq_exp {N : ℕ} (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (l : Fin N → ℝ) (A : ℝ) (hA : 0 < A) (z : Fin N → ℂ) :
    chargeKernel s₀ sL l A z = exp (chargeLinear l (Real.log A) sL z - s₀ * (Real.log A : ℂ)) := by
  rw [chargeKernel, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hA.ne'), ← ofReal_log hA.le,
    ← exp_add, chargeLinear_apply]
  congr 1
  ring

/-- The charge kernel has the full complex Fréchet derivative. -/
theorem hasFDerivAt_chargeKernel {N : ℕ} (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (l : Fin N → ℝ) (A : ℝ) (hA : 0 < A) (z : Fin N → ℂ) :
    HasFDerivAt (chargeKernel s₀ sL l A)
      (chargeKernel s₀ sL l A z • chargeLinear l (Real.log A) sL) z := by
  have heq : chargeKernel s₀ sL l A = fun w =>
      exp (chargeLinear l (Real.log A) sL w - s₀ * (Real.log A : ℂ)) :=
    funext (chargeKernel_eq_exp s₀ sL l A hA)
  rw [heq]
  exact ((chargeLinear l (Real.log A) sL).hasFDerivAt.sub_const _).cexp

/-- The norm of a positive real base to a complex power is its real power. -/
theorem norm_cpow_positive (A : ℝ) (hA : 0 < A) (s : ℂ) :
    ‖(A : ℂ) ^ s‖ = A ^ s.re := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hA.ne'), norm_exp, ← ofReal_log hA.le,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, Real.rpow_def_of_pos hA]

/-- Intermediate real powers are bounded by the sum of the endpoint powers. -/
theorem rpow_le_endpoint_sum (A : ℝ) (hA : 0 < A) (u t v : ℝ) (hu : u ≤ t) (hv : t ≤ v) :
    A ^ t ≤ A ^ u + A ^ v := by
  by_cases h : 1 ≤ A
  · exact (Real.rpow_le_rpow_of_exponent_le h hv).trans
      (le_add_of_nonneg_left (Real.rpow_pos_of_pos hA u).le)
  · exact (Real.rpow_le_rpow_of_exponent_ge hA (le_of_not_ge h) hu).trans
      (le_add_of_nonneg_right (Real.rpow_pos_of_pos hA v).le)

/-- The Gaussian exponential is bounded uniformly over parameters of bounded norm. -/
theorem norm_exp_charge_le {N : ℕ} (l : Fin N → ℝ) (z : Fin N → ℂ)
    (K : ℝ) (hK : ‖z‖ ≤ K) :
    ‖exp (∑ i, z i * (l i : ℂ))‖ ≤ Real.exp (K * ∑ i, |l i|) := by
  rw [norm_exp, Finset.mul_sum]
  apply Real.exp_le_exp.mpr
  change Complex.reCLM (∑ i, z i * (l i : ℂ)) ≤ _
  rw [map_sum]
  apply Finset.sum_le_sum
  intro i _
  have hre : (z i * (l i : ℂ)).re ≤ ‖z i * (l i : ℂ)‖ := re_le_norm _
  rw [norm_mul, norm_real] at hre
  exact hre.trans (mul_le_mul_of_nonneg_right ((norm_le_pi_norm z i).trans hK) (abs_nonneg _))

/-- A uniform bound for the charge kernel on a parameter neighborhood. -/
theorem norm_chargeKernel_le {N : ℕ} (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (l : Fin N → ℝ) (A : ℝ) (hA : 0 < A) (z : Fin N → ℂ)
    (K u v : ℝ) (hK : ‖z‖ ≤ K) (hu : u ≤ -(s₀ + sL z).re) (hv : -(s₀ + sL z).re ≤ v) :
    ‖chargeKernel s₀ sL l A z‖ ≤ Real.exp (K * ∑ i, |l i|) * (A ^ u + A ^ v) := by
  rw [chargeKernel, norm_mul, norm_cpow_positive A hA, neg_re]
  exact mul_le_mul (norm_exp_charge_le l z K hK)
    (rpow_le_endpoint_sum A hA u _ v hu hv) (by positivity) (Real.exp_pos _).le

/-- The charge kernel is strongly measurable under the exact AE hypotheses. -/
theorem aestronglyMeasurable_chargeKernel {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) (z : Fin N → ℂ) :
    AEStronglyMeasurable (fun ω => chargeKernel s₀ sL (L ω) (A ω) z) P := by
  have hcoord : ∀ i, AEMeasurable (fun ω => (L ω i : ℂ)) P := fun i =>
    Complex.continuous_ofReal.measurable.comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hL.aemeasurable)
  have hs : AEMeasurable (fun ω => ∑ i, z i * (L ω i : ℂ)) P :=
    Finset.aemeasurable_fun_sum Finset.univ (fun i _ => (hcoord i).const_mul (z i))
  have hlog : AEMeasurable (fun ω => (Real.log (A ω) : ℂ)) P :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable hA.log
  have he := Complex.continuous_exp.measurable.comp_aemeasurable
    (hs.sub (hlog.const_mul (s₀ + sL z)))
  apply he.aestronglyMeasurable.congr
  filter_upwards [hpos] with ω hω
  change exp ((∑ i, z i * (L ω i : ℂ)) - (s₀ + sL z) * (Real.log (A ω) : ℂ)) = _
  rw [chargeKernel, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hω.ne'), ← ofReal_log hω.le, ← exp_add]
  congr 1
  ring

/-- The random charge form is strongly measurable as a continuous linear map. -/
theorem aestronglyMeasurable_chargeLinear {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    AEStronglyMeasurable (fun ω => chargeLinear (L ω) (Real.log (A ω)) sL) P := by
  have hcoord : ∀ i, AEStronglyMeasurable (fun ω => (L ω i : ℂ)) P := fun i =>
    (Complex.continuous_ofReal.measurable.comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hL.aemeasurable)).aestronglyMeasurable
  have hlog : AEStronglyMeasurable (fun ω => (Real.log (A ω) : ℂ)) P :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable hA.log).aestronglyMeasurable
  exact (Finset.aestronglyMeasurable_fun_sum Finset.univ
    (fun i _ => (hcoord i).smul aestronglyMeasurable_const)).sub
      (hlog.smul aestronglyMeasurable_const)

/-- The first derivative shares an integrable envelope with the value. -/
theorem norm_chargeKernel_deriv_le {N : ℕ} (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (l : Fin N → ℝ) (A : ℝ) (hA : 0 < A) (z : Fin N → ℂ)
    (K u v : ℝ) (hK : ‖z‖ ≤ K) (hu : u ≤ -(s₀ + sL z).re) (hv : -(s₀ + sL z).re ≤ v) :
    ‖chargeKernel s₀ sL l A z • chargeLinear l (Real.log A) sL‖ ≤
      (1 + ‖sL‖) * (Real.exp (K * ∑ i, |l i|) * (A ^ u + A ^ v) *
        (1 + ∑ i, |l i| + |Real.log A|)) := by
  rw [norm_smul]
  have hlin := norm_chargeLinear_le l (Real.log A) sL
  have hs : (∑ i, |l i|) + ‖sL‖ * |Real.log A| ≤
      (1 + ‖sL‖) * (1 + ∑ i, |l i| + |Real.log A|) := by
    have hsum : 0 ≤ ∑ i, |l i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    nlinarith [norm_nonneg sL, abs_nonneg (Real.log A)]
  have h := mul_le_mul (norm_chargeKernel_le s₀ sL l A hA z K u v hK hu hv)
    (hlin.trans hs) (norm_nonneg _) (by positivity)
  convert h using 1
  ring

/-- Pointwise charge integrability follows from the strict moment margin. -/
theorem integrable_chargeKernel {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) (z : Fin N → ℂ)
    (hz : -(s₀ + sL z).re < pstar) :
    Integrable (fun ω => chargeKernel s₀ sL (L ω) (A ω) z) P := by
  have h := (integrable_gaussian_exp_mass_power P L hL A hA hpos pstar hinv hmom
    ‖z‖ (norm_nonneg _) (-(s₀ + sL z).re) hz).const_mul 2
  apply h.mono' (aestronglyMeasurable_chargeKernel P L hL A hA hpos s₀ sL z)
  filter_upwards [hpos] with ω hω
  have hb := norm_chargeKernel_le s₀ sL (L ω) (A ω) hω z ‖z‖
    (-(s₀ + sL z).re) (-(s₀ + sL z).re) le_rfl le_rfl le_rfl
  convert hb using 1
  ring

/-- Dominated differentiation on a polydisc inside a fixed interval of mass exponents. -/
theorem differentiableOn_chargeIntegral_polydisc {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i)
    (K u v : ℝ) (hK : 0 ≤ K) (huv : u ≤ v) (hv : v < pstar)
    (hparam : ∀ z ∈ complexPolydisc a R,
      ‖z‖ ≤ K ∧ u ≤ -(s₀ + sL z).re ∧ -(s₀ + sL z).re ≤ v) :
    DifferentiableOn ℂ (fun z => ∫ ω, chargeKernel s₀ sL (L ω) (A ω) z ∂P)
      (complexPolydisc a R) := by
  let F := fun z ω => chargeKernel s₀ sL (L ω) (A ω) z
  let F' := fun z ω => F z ω • chargeLinear (L ω) (Real.log (A ω)) sL
  let bound := fun ω => (1 + ‖sL‖) * (Real.exp (K * ∑ i, |L ω i|) *
    (A ω ^ u + A ω ^ v) * (1 + ∑ i, |L ω i| + |Real.log (A ω)|))
  have ha := mem_complexPolydisc_center a R hR
  have hb : Integrable bound P :=
    (integrable_gaussian_mass_envelope P L hL A hA hpos pstar hinv hmom K hK u v huv hv).const_mul _
  have hmeas : ∀ z, AEStronglyMeasurable (F z) P :=
    aestronglyMeasurable_chargeKernel P L hL A hA hpos s₀ sL
  have hmeas' : ∀ z, AEStronglyMeasurable (F' z) P := fun z =>
    (hmeas z).smul (aestronglyMeasurable_chargeLinear P L hL A hA sL)
  have hbase : Integrable (F a) P := integrable_chargeKernel P L hL A hA hpos
    pstar hinv hmom s₀ sL a ((hparam a ha).2.2.trans_lt hv)
  exact (differentiableOn_integral_polydisc P a R hR F F' bound
    (fun z _ => hmeas z) (fun z _ => hmeas' z) hbase hb
    (by
      filter_upwards [hpos] with ω hω
      intro z hz
      exact norm_chargeKernel_deriv_le s₀ sL (L ω) (A ω) hω z K u v
        (hparam z hz).1 (hparam z hz).2.1 (hparam z hz).2.2)
    (by
      filter_upwards [hpos] with ω hω
      intro z _
      exact hasFDerivAt_chargeKernel s₀ sL (L ω) (A ω) hω z)).1

/-- The affine real mass exponent is continuous. -/
theorem continuous_charge_exponent {N : ℕ} (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    Continuous (fun z => -(s₀ + sL z).re) := by fun_prop

/-- Local polydisc domination gives holomorphy on the whole strict moment domain. -/
theorem differentiableOn_chargeIntegral {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (hL : HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => ∫ ω, chargeKernel s₀ sL (L ω) (A ω) z ∂P)
      {z ∈ U | -(s₀ + sL z).re < pstar} := by
  intro a ha
  let t := -(s₀ + sL a).re
  let δ := (pstar - t) / 2
  let u := t - δ
  let v := t + δ
  let K := ‖a‖ + 1
  have hδ : 0 < δ := half_pos (sub_pos.mpr ha.2)
  have huv : u ≤ v := by dsimp [u, v]; linarith
  have ht : t < pstar := ha.2
  have hv : v < pstar := by dsimp [v, δ]; linarith
  let W := U ∩ (fun z => -(s₀ + sL z).re) ⁻¹' Ioo u v ∩ (fun z => ‖z‖) ⁻¹' Iio K
  have hW : IsOpen W := (hU.inter (isOpen_Ioo.preimage (continuous_charge_exponent s₀ sL))).inter
    (isOpen_Iio.preimage continuous_norm)
  have haW : a ∈ W := ⟨⟨ha.1, by change u < t ∧ t < v; dsimp [u, v]; constructor <;> linarith⟩,
    by change ‖a‖ < K; dsimp [K]; linarith⟩
  obtain ⟨R, hR, _, hsub⟩ := exists_closed_polydisc_subset_open W hW a haW
  have hd := differentiableOn_chargeIntegral_polydisc P L hL A hA hpos pstar hinv hmom s₀ sL
    a R hR K u v (by dsimp [K]; positivity) huv hv
    (fun z hz => ⟨(hsub hz).2.le, (hsub hz).1.2.1.le, (hsub hz).1.2.2.le⟩)
  exact (hd.differentiableAt ((isOpen_complexPolydisc a R).mem_nhds
    (mem_complexPolydisc_center a R hR))).differentiableWithinAt

/-- Factoring the deterministic exponential out of the charge expectation. -/
theorem integral_gaussian_charge_factor {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (L : Ω → Fin N → ℝ) (A : Ω → ℝ)
    (c : (Fin N → ℂ) → ℂ) (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) (z : Fin N → ℂ) :
    (∫ ω, exp (c z + ∑ i, z i * (L ω i : ℂ)) * (A ω : ℂ) ^ (-(s₀ + sL z)) ∂P) =
      exp (c z) * ∫ ω, chargeKernel s₀ sL (L ω) (A ω) z ∂P := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    change exp (c z + ∑ i, z i * (L ω i : ℂ)) * (A ω : ℂ) ^ (-(s₀ + sL z)) =
      exp (c z) * chargeKernel s₀ sL (L ω) (A ω) z
    rw [chargeKernel, exp_add, mul_assoc]

/-- Proof of `DOZZ.differentiableOn_gaussian_charge_moment`: the Gaussian charge moment, allowing
correlation with the positive mass. -/
theorem differentiableOn_gaussian_charge_moment {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (L : Ω → Fin N → ℝ) (hL : ProbabilityTheory.HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ) (hpstar : 0 < pstar)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (c : (Fin N → ℂ) → ℂ) (hc : DifferentiableOn ℂ c U)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    (∀ z ∈ {z ∈ U | -(s₀ + sL z).re < pstar},
      Integrable (fun ω => Complex.exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z))) P) ∧
    DifferentiableOn ℂ
      (fun z => ∫ ω, Complex.exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z)) ∂P)
      {z ∈ U | -(s₀ + sL z).re < pstar} := by
  have hzero := hmom 0 le_rfl hpstar
  have hcharge := differentiableOn_chargeIntegral P L hL A hA hpos pstar hinv hmom U hU s₀ sL
  constructor
  · intro z hz
    have h := (integrable_chargeKernel P L hL A hA hpos pstar hinv hmom s₀ sL z hz.2).const_mul
      (exp (c z))
    convert h using 1
    ext ω
    rw [chargeKernel, exp_add, mul_assoc]
  · have heq : (fun z => ∫ ω, exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z)) ∂P) =
        (fun z => exp (c z) * ∫ ω, chargeKernel s₀ sL (L ω) (A ω) z ∂P) :=
      funext (integral_gaussian_charge_factor P L A c s₀ sL)
    rw [heq]
    exact (hc.mono (fun _ hz => hz.1)).cexp.mul hcharge

end DOZZ.Proofs
