/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosNegativePower
public import DOZZ.GMC.FiniteChaosMean
public import DOZZ.GMC.Moments.ChaosLawFDD
public import DOZZ.Statements.GMC.FieldChaosMass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Negative-power Kahane comparison for continuum Gaussian fields. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The pointwise variance of a jointly measurable centered Gaussian field is measurable in its
spatial variable. -/
theorem centeredGaussianField_variance_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ) :
    Measurable (fun x => DOZZ.gaussianVariance P (fun ω => Φ ω x)) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have hPprob : IsProbabilityMeasure P := hzero.1
  let f : S × Ω → ℝ := fun q => Φ q.2 q.1
  have hf : Measurable f := by
    exact hΦ.1.comp (by fun_prop : Measurable fun q : S × Ω => (q.2, q.1))
  have hf2 : Measurable (fun q : S × Ω => f q * f q) := hf.mul hf
  have hint : Measurable (fun x => ∫ ω, f (x, ω) * f (x, ω) ∂P) := by
    exact hf2.stronglyMeasurable.integral_prod_right.measurable
  have heq : (fun x => DOZZ.gaussianVariance P (fun ω => Φ ω x)) =
      fun x => ∫ ω, f (x, ω) * f (x, ω) ∂P := by
    funext x
    rfl
  rw [heq]
  exact hint

/-- The covariance kernel of a jointly measurable centered Gaussian field is measurable. -/
theorem centeredGaussianField_covariance_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ) :
    Measurable (fun xy : S × S =>
      DOZZ.gaussianCovariance P (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2)) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have : IsProbabilityMeasure P := hzero.1
  let f : (S × S) × Ω → ℝ := fun q => Φ q.2 q.1.1 * Φ q.2 q.1.2
  have hf : Measurable f := by
    apply Measurable.mul
    · exact hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.1))
    · exact hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.2))
  have hint : Measurable (fun xy => ∫ ω, f (xy, ω) ∂P) := by
    exact hf.stronglyMeasurable.integral_prod_right.measurable
  have heq : (fun xy : S × S =>
      DOZZ.gaussianCovariance P (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2)) =
      fun xy => ∫ ω, f (xy, ω) ∂P := by
    funext xy
    rfl
  rw [heq]
  exact hint

/-- Every point evaluation of a centered Gaussian field has the centered Gaussian law whose
variance is its covariance-form diagonal. -/
theorem centeredGaussianField_pointwise_law
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ) (x : S) :
    HasLaw (fun ω => Φ ω x)
      (gaussianReal 0 (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal) P := by
  let Z : Ω → Fin 1 → ℝ := fun ω _ => Φ ω x
  have hZ : DOZZ.IsCenteredJointlyGaussian P Z := hΦ.2 1 (fun _ => x)
  obtain ⟨v, hmap, _, hvar⟩ :=
    DOZZ.Proofs.coordinate_mean_variance P Z hZ (0 : Fin 1)
  have hv : (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal = v := by
    rw [hvar]
    simp
  refine ⟨hZ.2.1 0, ?_⟩
  simpa [Z, hv] using hmap

/-- A bounded nonnegative measurable weight is integrable under the normalized version of a
finite reference measure. -/
theorem centeredGaussianField_bounded_weight_integrable
    {S : Type*} [MeasurableSpace S] [Nonempty S] (ν : FiniteMeasure S)
    (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) :
    Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) := by
  obtain ⟨c, hc⟩ := hhb
  refine (integrable_const (c : ℝ)).mono'
    (measurable_coe_nnreal_real.comp hh).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg (h x))]
  exact_mod_cast hc x

/-- Almost every field section has an integrable weighted Wick density under a probability
reference measure. -/
theorem centeredGaussianField_ae_integrable_weighted_wick
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have : IsProbabilityMeasure P := hzero.1
  have hv : Measurable (fun x =>
      (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal) :=
    measurable_real_toNNReal.comp (centeredGaussianField_variance_measurable P Φ hΦ)
  have hLaw : ∀ x, HasLaw (fun ω => Φ ω x)
      (gaussianReal 0 ((DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal)) P :=
    centeredGaussianField_pointwise_law P Φ hΦ
  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    obtain ⟨v, _, _, hvar⟩ :=
      DOZZ.Proofs.coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x)
        (hΦ.2 1 (fun _ => x)) (0 : Fin 1)
    rw [hvar]
    positivity
  have hsections := ae_integrable_weighted_wick_sections (ν.normalize : Measure S) Φ
    (fun x => (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal)
    (fun x => (h x : ℝ)) γ hΦ.1 hv (measurable_coe_nnreal_real.comp hh) hLaw
    (fun x => NNReal.coe_nonneg (h x))
    (centeredGaussianField_bounded_weight_integrable ν h hh hhb)
  filter_upwards [hsections] with ω hω
  have hEq : (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        ((DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal : ℝ))) =
      fun x => (h x : ℝ) *
        Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Φ ω x)) := by
    funext x
    exact congrArg (fun t : ℝ => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 * t))
      (Real.coe_toNNReal _ (hvar_nonneg x))
  exact hω.congr (ae_of_all _ fun x => congrFun hEq x)

/-- The finite-cutoff field chaos mass is measurable. -/
theorem centeredGaussianField_fieldChaosMass_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) [SFinite ν] (h : S → ℝ≥0) (hh : Measurable h) (γ : ℝ) :
    Measurable (fun ω => DOZZ.fieldChaosMass P Φ ν h γ ω) := by
  have hv := centeredGaussianField_variance_measurable P Φ hΦ
  have hvInt : Measurable (fun x => ∫ ω, Φ ω x ^ 2 ∂P) := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hv
  have hfield : Measurable (fun q : Ω × S => Φ q.1 q.2) := hΦ.1
  have hvarInt : Measurable (fun q : Ω × S => ∫ ω, Φ ω q.2 ^ 2 ∂P) :=
    hvInt.comp measurable_snd
  have hlog : Measurable (fun q : Ω × S => γ * Φ q.1 q.2 - γ ^ 2 / 2 *
      (∫ ω, Φ ω q.2 ^ 2 ∂P)) := by fun_prop
  have hexp : Measurable (fun q : Ω × S => ENNReal.ofReal
      (Real.exp (γ * Φ q.1 q.2 - γ ^ 2 / 2 *
        (∫ ω, Φ ω q.2 ^ 2 ∂P)))) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp hlog)
  have hf : Measurable (fun q : Ω × S => (h q.2 : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (γ * Φ q.1 q.2 - γ ^ 2 / 2 *
        (∫ ω, Φ ω q.2 ^ 2 ∂P)))) :=
    (measurable_coe_nnreal_ennreal.comp (hh.comp measurable_snd)).mul hexp
  unfold DOZZ.fieldChaosMass
  exact hf.lintegral_prod_right' (ν := ν)

theorem ae_empirical_average_tendsto
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → S → ℝ)
    (hjoint : Measurable (fun p : Ω × S => f p.1 p.2))
    (hint : ∀ᵐ ω ∂P, Integrable (f ω) ν) :
    ∀ᵐ ω ∂P, ∀ᵐ q ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ : ℕ => ν)
  have hQ : IsProbabilityMeasure Q := by infer_instance
  have hEvalIdent (i : ℕ) : IdentDistrib (fun q : ℕ → S => q i) id Q ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, ?_⟩
    simpa [Q] using (Measure.infinitePi_map_eval (fun _ : ℕ => ν) i)
  have hCoordIdent (i : ℕ) :
      IdentDistrib (fun q : ℕ → S => q i) (fun q => q 0) Q Q :=
    (hEvalIdent i).trans (hEvalIdent 0).symm
  have hindepCoord : iIndepFun (fun i (q : ℕ → S) => q i) Q := by
    simpa [Q] using
      (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id)
        (by fun_prop))
  have hInner (ω : Ω) (hω : Integrable (f ω) ν) :
      ∀ᵐ q ∂Q,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
          atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    have hfmeas : Measurable (f ω) :=
      hjoint.comp (by fun_prop : Measurable fun x : S => (ω, x))
    have hindep := hindepCoord.comp (fun _ => f ω) (fun _ => hfmeas)
    have hindep' : Pairwise (fun i j =>
        (fun q => f ω (q i)) ⟂ᵢ[Q] (fun q => f ω (q j))) := by
      intro i j hij
      exact hindep.indepFun hij
    have hident : ∀ i, IdentDistrib (fun q => f ω (q i))
        (fun q => f ω (q 0)) Q Q := by
      intro i
      exact (hCoordIdent i).comp hfmeas
    have hsampleIdent : IdentDistrib (fun q => f ω (q 0)) (f ω) Q ν :=
      (hEvalIdent 0).comp hfmeas
    have hsampleInt : Integrable (fun q => f ω (q 0)) Q :=
      hsampleIdent.integrable_iff.mpr hω
    have hmean : (∫ q, f ω (q 0) ∂Q) = ∫ x, f ω x ∂ν :=
      hsampleIdent.integral_eq
    have hlln := ProbabilityTheory.strong_law_ae (μ := Q)
      (fun i (q : ℕ → S) => f ω (q i)) hsampleInt hindep' hident
    filter_upwards [hlln] with q hq
    simpa only [smul_eq_mul, ← Fin.sum_univ_eq_sum_range, hmean] using hq
  have hIter : ∀ᵐ ω ∂P, ∀ᵐ q ∂Q,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    filter_upwards [hint] with ω hω
    exact hInner ω hω
  exact hIter

theorem fieldChaosMass_eq_ofReal_normalized_integral
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω)
    (hint : Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S)) :
    DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω =
      ENNReal.ofReal ((ν.mass : ℝ) * ∫ x, (h x : ℝ) *
        Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Φ ω x)) ∂(ν.normalize : Measure S)) := by
  let f : S → ℝ := fun x => (h x : ℝ) *
    Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := by
    exact congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
  have hintegrand (x : S) :
      (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P)) = ENNReal.ofReal (f x) := by
    have hv : DOZZ.gaussianVariance P (fun ω => Φ ω x) =
        ∫ ω', Φ ω' x ^ 2 ∂P := by
      simp [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two]
    rw [← hv]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg (h x))]
  unfold DOZZ.fieldChaosMass
  rw [show (fun x => (h x : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) =
      fun x => ENNReal.ofReal (f x) from funext hintegrand]
  rw [hνeq, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ hf_nonneg)]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]

theorem centeredGaussianField_covariance_order_samples
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∀ n, ∀ᵐ u ∂Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S)),
      ∀ i j : Fin n,
        DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i.val)) (fun ω => Φ ω (u j.val)) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i.val)) (fun ω => Ψ ω (u j.val)) := by
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := by
    exact congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hρν : (ν.normalize : Measure S) ≪ (ν : Measure S) := by
    rw [hνeq]
    apply Measure.absolutelyContinuous_smul
    exact ENNReal.coe_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν)
  have hρprod : (ν.normalize : Measure S).prod (ν.normalize : Measure S) ≪
      (ν : Measure S).prod ν := hρν.prod hρν
  have hcvX := centeredGaussianField_covariance_measurable PX Φ hΦ
  have hcvY := centeredGaussianField_covariance_measurable PY Ψ hΨ
  have hvX := centeredGaussianField_variance_measurable PX Φ hΦ
  have hvY := centeredGaussianField_variance_measurable PY Ψ hΨ
  have hcovNorm : ∀ᵐ xy ∂(ν.normalize : Measure S).prod (ν.normalize : Measure S),
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) :=
    hρprod.ae_le hcov
  have hdiagNorm : ∀ᵐ x ∂(ν.normalize : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := hρν.ae_le hdiag
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S))
  have hQ : IsProbabilityMeasure Q := by infer_instance
  have hpair (i j : ℕ) (hij : i ≠ j) :
      Q.map (fun u : ℕ → S => (u i, u j)) =
        (ν.normalize : Measure S).prod (ν.normalize : Measure S) := by
    simpa [Q] using (Measure.infinitePi_map_eval_prod
      (P := fun _ : ℕ => (ν.normalize : Measure S)) hij)
  have heval (i : ℕ) : Q.map (fun u : ℕ → S => u i) =
      (ν.normalize : Measure S) := by
    simpa [Q] using
      (Measure.infinitePi_map_eval (fun _ : ℕ => (ν.normalize : Measure S)) i)
  have hpairMeas (i j : ℕ) : Measurable (fun u : ℕ → S => (u i, u j)) := by
    fun_prop
  have hevalMeas (i : ℕ) : Measurable (fun u : ℕ → S => u i) := by
    fun_prop
  have hcovSample (i j : ℕ) (hij : i ≠ j) : ∀ᵐ u ∂Q,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i)) (fun ω => Φ ω (u j)) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i)) (fun ω => Ψ ω (u j)) := by
    have hset : MeasurableSet {xy : S × S |
        DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2)} :=
      measurableSet_le hcvX hcvY
    have hpull : ∀ᵐ u ∂Q.map (fun u : ℕ → S => (u i, u j)),
        DOZZ.gaussianCovariance PX (fun ω => Φ ω (u.1)) (fun ω => Φ ω (u.2)) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u.1)) (fun ω => Ψ ω (u.2)) := by
      rw [hpair i j hij]
      exact hcovNorm
    filter_upwards [(ae_map_iff (hpairMeas i j).aemeasurable hset).1 hpull] with u hu
    exact hu
  have hdiagSample (i : ℕ) : ∀ᵐ u ∂Q,
      DOZZ.gaussianVariance PX (fun ω => Φ ω (u i)) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i)) := by
    have hset : MeasurableSet {x : S |
        DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
          DOZZ.gaussianVariance PY (fun ω => Ψ ω x)} := measurableSet_le hvX hvY
    have hpull : ∀ᵐ x ∂Q.map (fun u : ℕ → S => u i),
        DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
          DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
      rw [heval i]
      exact hdiagNorm
    filter_upwards [(ae_map_iff (hevalMeas i).aemeasurable hset).1 hpull] with u hu
    exact hu
  intro n
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i.val = j.val
  · have hij' : i = j := Fin.ext hij
    subst j
    exact hdiagSample i.val
  · exact hcovSample i.val j.val hij

private theorem lintegral_order_of_laplace_approximants
    {ΩX ΩY A : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace A]
    (PX : Measure ΩX) (PY : Measure ΩY) (Q : Measure A)
    [IsProbabilityMeasure PX] [IsProbabilityMeasure PY] [IsProbabilityMeasure Q]
    (FX : ℕ → ΩX × A → ℝ≥0∞) (FY : ℕ → ΩY × A → ℝ≥0∞)
    (LX : ΩX → ℝ≥0∞) (LY : ΩY → ℝ≥0∞)
    (hFX : ∀ n, Measurable (FX n)) (hFY : ∀ n, Measurable (FY n))
    (hLX : Measurable LX) (hLY : Measurable LY)
    (hboundX : ∀ n p, FX n p ≤ 1) (hboundY : ∀ n p, FY n p ≤ 1)
    (horder : ∀ n, ∫⁻ p, FX n p ∂PX.prod Q ≤ ∫⁻ p, FY n p ∂PY.prod Q)
    (hlimX : ∀ᵐ p ∂PX.prod Q, Tendsto (fun n => FX n p) atTop (𝓝 (LX p.1)))
    (hlimY : ∀ᵐ p ∂PY.prod Q, Tendsto (fun n => FY n p) atTop (𝓝 (LY p.1))) :
    ∫⁻ ω, LX ω ∂PX ≤ ∫⁻ ω, LY ω ∂PY := by
  have hfinX : ∫⁻ p, (1 : ℝ≥0∞) ∂PX.prod Q ≠ ∞ := by simp
  have hfinY : ∫⁻ p, (1 : ℝ≥0∞) ∂PY.prod Q ≠ ∞ := by simp
  have hDCTX := tendsto_lintegral_of_dominated_convergence
    (bound := fun _ : ΩX × A => (1 : ℝ≥0∞)) hFX
    (fun n => ae_of_all _ (hboundX n)) hfinX hlimX
  have hDCTY := tendsto_lintegral_of_dominated_convergence
    (bound := fun _ : ΩY × A => (1 : ℝ≥0∞)) hFY
    (fun n => ae_of_all _ (hboundY n)) hfinY hlimY
  have hprodX : ∫⁻ p, LX p.1 ∂PX.prod Q = ∫⁻ ω, LX ω ∂PX := by
    calc
      ∫⁻ p, LX p.1 ∂PX.prod Q = ∫⁻ ω, ∫⁻ a, LX ω ∂Q ∂PX :=
        lintegral_prod (fun p : ΩX × A => LX p.1)
          (hLX.comp measurable_fst).aemeasurable
      _ = ∫⁻ ω, LX ω ∂PX := by simp
  have hprodY : ∫⁻ p, LY p.1 ∂PY.prod Q = ∫⁻ ω, LY ω ∂PY := by
    calc
      ∫⁻ p, LY p.1 ∂PY.prod Q = ∫⁻ ω, ∫⁻ a, LY ω ∂Q ∂PY :=
        lintegral_prod (fun p : ΩY × A => LY p.1)
          (hLY.comp measurable_fst).aemeasurable
      _ = ∫⁻ ω, LY ω ∂PY := by simp
  rw [hprodX] at hDCTX
  rw [hprodY] at hDCTY
  exact le_of_tendsto_of_tendsto hDCTX hDCTY (Filter.Eventually.of_forall horder)

private theorem kahane_field_laplace_of_nonzero_finite_measure
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c)
    (γ s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX ≤
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY := by
  classical
  have hPXzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have hPYzero := hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have : IsProbabilityMeasure PX := hPXzero.1
  have : IsProbabilityMeasure PY := hPYzero.1
  let ρ : Measure S := ν.normalize
  have hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have : IsProbabilityMeasure ρ := hρprob
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ : ℕ => ρ)
  have : IsProbabilityMeasure Q := by infer_instance
  let c : ℝ := (ν.mass : ℝ)
  let wx : ΩX → S → ℝ := fun ω x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance PX (fun ω => Φ ω x))
  let wy : ΩY → S → ℝ := fun ω x => (h x : ℝ) * Real.exp
    (γ * Ψ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance PY (fun ω => Ψ ω x))
  have hwickX : Measurable (fun p : ΩX × S => wx p.1 p.2) := by
    have hvar := centeredGaussianField_variance_measurable PX Φ hΦ
    have hvar' : Measurable (fun p : ΩX × S =>
        DOZZ.gaussianVariance PX (fun ω => Φ ω p.2)) := hvar.comp measurable_snd
    have hfield : Measurable (fun p : ΩX × S => Φ p.1 p.2) := hΦ.1
    have hweight : Measurable (fun p : ΩX × S => (h p.2 : ℝ)) :=
      (measurable_coe_nnreal_real.comp hh).comp measurable_snd
    have hlog : Measurable (fun p : ΩX × S => γ * Φ p.1 p.2 - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PX (fun ω => Φ ω p.2)) :=
      (measurable_const.mul hΦ.1).sub (measurable_const.mul hvar')
    exact hweight.mul (Real.measurable_exp.comp hlog)
  have hwickY : Measurable (fun p : ΩY × S => wy p.1 p.2) := by
    have hvar := centeredGaussianField_variance_measurable PY Ψ hΨ
    have hvar' : Measurable (fun p : ΩY × S =>
        DOZZ.gaussianVariance PY (fun ω => Ψ ω p.2)) := hvar.comp measurable_snd
    have hfield : Measurable (fun p : ΩY × S => Ψ p.1 p.2) := hΨ.1
    have hweight : Measurable (fun p : ΩY × S => (h p.2 : ℝ)) :=
      (measurable_coe_nnreal_real.comp hh).comp measurable_snd
    have hlog : Measurable (fun p : ΩY × S => γ * Ψ p.1 p.2 - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PY (fun ω => Ψ ω p.2)) :=
      (measurable_const.mul hΨ.1).sub (measurable_const.mul hvar')
    exact hweight.mul (Real.measurable_exp.comp hlog)
  have hintX : ∀ᵐ ω ∂PX, Integrable (wx ω) ρ := by
    simpa [wx, ρ] using centeredGaussianField_ae_integrable_weighted_wick
      PX Φ hΦ ν h hh hhb γ
  have hintY : ∀ᵐ ω ∂PY, Integrable (wy ω) ρ := by
    simpa [wy, ρ] using centeredGaussianField_ae_integrable_weighted_wick
      PY Ψ hΨ ν h hh hhb γ
  have havgX := ae_empirical_average_tendsto PX ρ wx hwickX hintX
  have havgY := ae_empirical_average_tendsto PY ρ wy hwickY hintY
  have hρmeasX : Measurable (fun ω => ∫ x, wx ω x ∂ρ) :=
    hwickX.stronglyMeasurable.integral_prod_right'.measurable
  have hρmeasY : Measurable (fun ω => ∫ x, wy ω x ∂ρ) :=
    hwickY.stronglyMeasurable.integral_prod_right'.measurable
  let limitX : ΩX → ℝ := fun ω => c * ∫ x, wx ω x ∂ρ
  let limitY : ΩY → ℝ := fun ω => c * ∫ x, wy ω x ∂ρ
  let avgX : ℕ → ΩX × (ℕ → S) → ℝ := fun n p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, wx p.1 (p.2 i.val)
  let avgY : ℕ → ΩY × (ℕ → S) → ℝ := fun n p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, wy p.1 (p.2 i.val)
  let approxX : ℕ → ΩX × (ℕ → S) → ℝ := fun n p => c * avgX n p
  let approxY : ℕ → ΩY × (ℕ → S) → ℝ := fun n p => c * avgY n p
  let FX : ℕ → ΩX × (ℕ → S) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-s * approxX n p))
  let FY : ℕ → ΩY × (ℕ → S) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-s * approxY n p))
  have htermX (n : ℕ) (i : Fin n) :
      Measurable (fun p : ΩX × (ℕ → S) => wx p.1 (p.2 i.val)) := by
    have harg : Measurable (fun p : ΩX × (ℕ → S) => (p.1, p.2 i.val)) :=
      measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd)
    exact hwickX.comp harg
  have htermY (n : ℕ) (i : Fin n) :
      Measurable (fun p : ΩY × (ℕ → S) => wy p.1 (p.2 i.val)) := by
    have harg : Measurable (fun p : ΩY × (ℕ → S) => (p.1, p.2 i.val)) :=
      measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd)
    exact hwickY.comp harg
  have happroxXmeas (n : ℕ) : Measurable (fun p : ΩX × (ℕ → S) => approxX n p) := by
    dsimp [approxX, avgX]
    apply measurable_const.mul
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact htermX n i
  have happroxYmeas (n : ℕ) : Measurable (fun p : ΩY × (ℕ → S) => approxY n p) := by
    dsimp [approxY, avgY]
    apply measurable_const.mul
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact htermY n i
  have hFXmeas (n : ℕ) : Measurable (FX n) := by
    dsimp [FX]
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (happroxXmeas n)))
  have hFYmeas (n : ℕ) : Measurable (FY n) := by
    dsimp [FY]
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (happroxYmeas n)))
  have hformulaX (n : ℕ) (ω : ΩX) (u : ℕ → S) :
      DOZZ.finiteChaosMass PX (fun ω (i : Fin n) => Φ ω (u i.val))
        (fun (i : Fin n) => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω =
          approxX n (ω, u) := by
    simp only [DOZZ.finiteChaosMass]
    dsimp [approxX, avgX, wx]
    calc
      (∑ i : Fin n, (c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) *
          Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
            DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) =
          ∑ i : Fin n, (c * (n : ℝ)⁻¹) *
            ((h (u i.val) : ℝ) * Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = (c * (n : ℝ)⁻¹) * ∑ i : Fin n,
            ((h (u i.val) : ℝ) * Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) := by rw [Finset.mul_sum]
      _ = c * ((n : ℝ)⁻¹ * ∑ i : Fin n, wx ω (u i.val)) := by ring
  have hformulaY (n : ℕ) (ω : ΩY) (u : ℕ → S) :
      DOZZ.finiteChaosMass PY (fun ω (i : Fin n) => Ψ ω (u i.val))
        (fun (i : Fin n) => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω =
          approxY n (ω, u) := by
    simp only [DOZZ.finiteChaosMass]
    dsimp [approxY, avgY, wy]
    calc
      (∑ i : Fin n, (c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) *
          Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
            DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) =
          ∑ i : Fin n, (c * (n : ℝ)⁻¹) *
            ((h (u i.val) : ℝ) * Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = (c * (n : ℝ)⁻¹) * ∑ i : Fin n,
            ((h (u i.val) : ℝ) * Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) := by rw [Finset.mul_sum]
      _ = c * ((n : ℝ)⁻¹ * ∑ i : Fin n, wy ω (u i.val)) := by ring
  have hsample := centeredGaussianField_covariance_order_samples PX PY Φ Ψ hΦ hΨ
    ν hν hcov hdiag
  have hfiniteOrder (n : ℕ) : ∀ᵐ u ∂Q,
      (∫⁻ ω, FX n (ω, u) ∂PX) ≤ ∫⁻ ω, FY n (ω, u) ∂PY := by
    have hsampleN : ∀ᵐ u ∂Q,
        ∀ i j : Fin n,
          DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i.val)) (fun ω => Φ ω (u j.val)) ≤
            DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i.val)) (fun ω => Ψ ω (u j.val)) := by
      simpa [Q, ρ] using hsample n
    filter_upwards [hsampleN] with u hu
    let Xn : ΩX → Fin n → ℝ := fun ω i => Φ ω (u i.val)
    let Yn : ΩY → Fin n → ℝ := fun ω i => Ψ ω (u i.val)
    have hXn : DOZZ.IsCenteredJointlyGaussian PX Xn := hΦ.2 n (fun i => u i.val)
    have hYn : DOZZ.IsCenteredJointlyGaussian PY Yn := hΨ.2 n (fun i => u i.val)
    have ha : ∀ i : Fin n, 0 ≤ c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ) := by
      intro i
      exact mul_nonneg (mul_nonneg (by dsimp [c]; positivity)
        (inv_nonneg.mpr (Nat.cast_nonneg n))) (NNReal.coe_nonneg _)
    have hfin := kahane_finite_laplace_lintegral_fintype PX PY Xn Yn hXn hYn
      (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) ha γ s hs
      (fun i j => hu i j)
    calc
      (∫⁻ ω, FX n (ω, u) ∂PX) =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
            DOZZ.finiteChaosMass PX Xn
              (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂PX := by
                apply lintegral_congr_ae
                exact ae_of_all _ fun ω => by
                  simpa [FX, Xn] using congrArg
                    (fun m : ℝ => ENNReal.ofReal (Real.exp (-s * m)))
                    (hformulaX n ω u).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
            DOZZ.finiteChaosMass PY Yn
              (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂PY := hfin
      _ = ∫⁻ ω, FY n (ω, u) ∂PY := by
            apply lintegral_congr_ae
            exact ae_of_all _ fun ω => by
              simpa [FY, Yn] using congrArg
                (fun m : ℝ => ENNReal.ofReal (Real.exp (-s * m)))
                (hformulaY n ω u)
  have hproductOrder (n : ℕ) :
      ∫⁻ p, FX n p ∂PX.prod Q ≤ ∫⁻ p, FY n p ∂PY.prod Q := by
    have hswapX := lintegral_lintegral_swap (μ := PX) (ν := Q)
      (f := fun ω u => FX n (ω, u)) (hFXmeas n).aemeasurable
    have hswapY := lintegral_lintegral_swap (μ := PY) (ν := Q)
      (f := fun ω u => FY n (ω, u)) (hFYmeas n).aemeasurable
    calc
      _ = ∫⁻ u, ∫⁻ ω, FX n (ω, u) ∂PX ∂Q := by
        rw [lintegral_prod (FX n) (hFXmeas n).aemeasurable, hswapX]
      _ ≤ ∫⁻ u, ∫⁻ ω, FY n (ω, u) ∂PY ∂Q := lintegral_mono_ae (hfiniteOrder n)
      _ = ∫⁻ p, FY n p ∂PY.prod Q := by
        rw [lintegral_prod (FY n) (hFYmeas n).aemeasurable, hswapY]
  have hboundX (n : ℕ) (p : ΩX × (ℕ → S)) : FX n p ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, wx p.1 (p.2 i.val) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
    have havg : 0 ≤ avgX n p := by
      dsimp [avgX]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum
    have happ : 0 ≤ approxX n p := by
      dsimp [approxX]
      exact mul_nonneg (by dsimp [c]; positivity) havg
    have hexp : Real.exp (-s * approxX n p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) happ)
    simpa [FX] using ENNReal.ofReal_le_ofReal hexp
  have hboundY (n : ℕ) (p : ΩY × (ℕ → S)) : FY n p ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, wy p.1 (p.2 i.val) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
    have havg : 0 ≤ avgY n p := by
      dsimp [avgY]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum
    have happ : 0 ≤ approxY n p := by
      dsimp [approxY]
      exact mul_nonneg (by dsimp [c]; positivity) havg
    have hexp : Real.exp (-s * approxY n p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) happ)
    simpa [FY] using ENNReal.ofReal_le_ofReal hexp
  have hlimitXNested : ∀ᵐ ω ∂PX, ∀ᵐ u ∂Q,
      Tendsto (fun n => FX n (ω, u)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-s * limitX ω)))) := by
    have havgX' : ∀ᵐ ω ∂PX, ∀ᵐ u ∂Q,
        Tendsto (fun n => avgX n (ω, u)) atTop (𝓝 (∫ x, wx ω x ∂ρ)) := by
      simpa [avgX, Q, ρ] using havgX
    filter_upwards [havgX'] with ω havg
    filter_upwards [havg] with u havg'
    have hmass : Tendsto (fun n => approxX n (ω, u)) atTop (𝓝 (limitX ω)) := by
      simpa [approxX, limitX] using tendsto_const_nhds.mul havg'
    have harg : Tendsto (fun n => -s * approxX n (ω, u)) atTop (𝓝 (-s * limitX ω)) :=
      tendsto_const_nhds.mul hmass
    have hexp := (Real.continuous_exp.tendsto (-s * limitX ω)).comp harg
    exact ENNReal.tendsto_ofReal hexp
  have hlimitYNested : ∀ᵐ ω ∂PY, ∀ᵐ u ∂Q,
      Tendsto (fun n => FY n (ω, u)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-s * limitY ω)))) := by
    have havgY' : ∀ᵐ ω ∂PY, ∀ᵐ u ∂Q,
        Tendsto (fun n => avgY n (ω, u)) atTop (𝓝 (∫ x, wy ω x ∂ρ)) := by
      simpa [avgY, Q, ρ] using havgY
    filter_upwards [havgY'] with ω havg
    filter_upwards [havg] with u havg'
    have hmass : Tendsto (fun n => approxY n (ω, u)) atTop (𝓝 (limitY ω)) := by
      simpa [approxY, limitY] using tendsto_const_nhds.mul havg'
    have harg : Tendsto (fun n => -s * approxY n (ω, u)) atTop (𝓝 (-s * limitY ω)) :=
      tendsto_const_nhds.mul hmass
    have hexp := (Real.continuous_exp.tendsto (-s * limitY ω)).comp harg
    exact ENNReal.tendsto_ofReal hexp
  have hlimitMeasX : Measurable (fun p : ΩX × (ℕ → S) =>
      ENNReal.ofReal (Real.exp (-s * limitX p.1))) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul
        ((measurable_const.mul hρmeasX).comp measurable_fst)))
  have hlimitMeasY : Measurable (fun p : ΩY × (ℕ → S) =>
      ENNReal.ofReal (Real.exp (-s * limitY p.1))) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul
        ((measurable_const.mul hρmeasY).comp measurable_fst)))
  have hseqMeasX : ∀ n, Measurable (fun p : ΩX × (ℕ → S) => FX n p) := hFXmeas
  have hseqMeasY : ∀ n, Measurable (fun p : ΩY × (ℕ → S) => FY n p) := hFYmeas
  have hsetX : MeasurableSet {p : ΩX × (ℕ → S) |
      Tendsto (fun n => FX n p) atTop (𝓝 (ENNReal.ofReal (Real.exp (-s * limitX p.1))))} := by
    exact measurableSet_tendsto_fun (l := atTop) hseqMeasX hlimitMeasX
  have hsetY : MeasurableSet {p : ΩY × (ℕ → S) |
      Tendsto (fun n => FY n p) atTop (𝓝 (ENNReal.ofReal (Real.exp (-s * limitY p.1))))} := by
    exact measurableSet_tendsto_fun (l := atTop) hseqMeasY hlimitMeasY
  have hlimitX : ∀ᵐ p ∂PX.prod Q,
      Tendsto (fun n => FX n p) atTop (𝓝 (ENNReal.ofReal (Real.exp (-s * limitX p.1)))) :=
    Measure.ae_prod_iff_ae_ae hsetX |>.2 hlimitXNested
  have hlimitY : ∀ᵐ p ∂PY.prod Q,
      Tendsto (fun n => FY n p) atTop (𝓝 (ENNReal.ofReal (Real.exp (-s * limitY p.1)))) :=
    Measure.ae_prod_iff_ae_ae hsetY |>.2 hlimitYNested
  have hlimitOrder := lintegral_order_of_laplace_approximants PX PY Q FX FY
    (fun ω => ENNReal.ofReal (Real.exp (-s * limitX ω)))
    (fun ω => ENNReal.ofReal (Real.exp (-s * limitY ω)))
    hFXmeas hFYmeas
    (ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hρmeasX))))
    (ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hρmeasY))))
    hboundX hboundY hproductOrder hlimitX hlimitY
  have htargetX :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
        (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitX ω)) ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hintX] with ω hInt
    have hfieldMass := fieldChaosMass_eq_ofReal_normalized_integral PX Φ ν h γ ω
      (by simpa [wx, ρ] using hInt)
    have hlimNonneg : 0 ≤ limitX ω := by
      dsimp [limitX, c]
      apply mul_nonneg
      · positivity
      · exact integral_nonneg_of_ae (ae_of_all _ fun x =>
          mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
    have htoReal : (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal = limitX ω := by
      rw [hfieldMass]
      exact ENNReal.toReal_ofReal hlimNonneg
    rw [htoReal]
  have htargetY :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
        (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitY ω)) ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hintY] with ω hInt
    have hfieldMass := fieldChaosMass_eq_ofReal_normalized_integral PY Ψ ν h γ ω
      (by simpa [wy, ρ] using hInt)
    have hlimNonneg : 0 ≤ limitY ω := by
      dsimp [limitY, c]
      apply mul_nonneg
      · positivity
      · exact integral_nonneg_of_ae (ae_of_all _ fun x =>
          mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
    have htoReal : (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal = limitY ω := by
      rw [hfieldMass]
      exact ENNReal.toReal_ofReal hlimNonneg
    rw [htoReal]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitX ω)) ∂PX := htargetX
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitY ω)) ∂PY := hlimitOrder
    _ = _ := htargetY.symm

theorem centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hzero : ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) = 0) :
    ∀ ω, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω = 0 := by
  have hbaseInt : Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) :=
    centeredGaussianField_bounded_weight_integrable ν h hh hhb
  have hbaseZero : (fun x => (h x : ℝ)) =ᵐ[(ν.normalize : Measure S)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => NNReal.coe_nonneg (h x)) hbaseInt).mp hzero
  intro ω
  let f : S → ℝ := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hzeroF : f =ᵐ[(ν.normalize : Measure S)] 0 := by
    filter_upwards [hbaseZero] with x hx
    simp [f, hx]
  have hIntF : Integrable f (ν.normalize : Measure S) :=
    (integrable_congr hzeroF).mpr (integrable_const (0 : ℝ))
  have hmass := fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hIntF
  rw [hmass]
  have hfint : ∫ x, f x ∂(ν.normalize : Measure S) = 0 := by
    rw [integral_congr_ae hzeroF]
    simp
  rw [hfint]
  simp

theorem centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S)) :
    ∀ᵐ ω ∂P, 0 < DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω := by
  have hbaseInt : Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) :=
    centeredGaussianField_bounded_weight_integrable ν h hh hhb
  have hbaseSupport : 0 < (ν.normalize : Measure S) (Function.support fun x => (h x : ℝ)) :=
    (integral_pos_iff_support_of_nonneg
      (f := fun x => (h x : ℝ)) (μ := (ν.normalize : Measure S))
      (fun x => NNReal.coe_nonneg (h x)) hbaseInt).mp hpos
  have hPzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have : IsProbabilityMeasure P := hPzero.1
  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    obtain ⟨v, _, _, hvar⟩ :=
      DOZZ.Proofs.coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x)
        (hΦ.2 1 (fun _ => x)) (0 : Fin 1)
    rw [hvar]
    positivity
  have hint := centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ
  filter_upwards [hint] with ω hω
  let f : S → ℝ := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hf_nonneg (x : S) : 0 ≤ f x :=
    mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
  have hfsupport : Function.support f = Function.support fun x => (h x : ℝ) := by
    ext x
    simp [f, Function.mem_support, Real.exp_ne_zero]
  have hfpos : 0 < ∫ x, f x ∂(ν.normalize : Measure S) := by
    rw [integral_pos_iff_support_of_nonneg hf_nonneg hω, hfsupport]
    exact hbaseSupport
  have hrepresentation := fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω (by simpa [f] using hω)
  have hmasspos : 0 < (ν.mass : ℝ) := by
    have hmassne : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
    exact_mod_cast (pos_iff_ne_zero.mpr hmassne : 0 < ν.mass)
  rw [hrepresentation]
  exact ENNReal.ofReal_pos.mpr (mul_pos hmasspos hfpos)

theorem fieldChaosMass_eq_ofReal_modified_toReal_ae
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S)) :
    let M := fun ω => DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω
    let m := fun ω => if (M ω).toReal = 0 then 1 else (M ω).toReal
    ∀ᵐ ω ∂P, M ω = ENNReal.ofReal (m ω) := by
  dsimp
  have hint := centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ
  have hmasspos := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    P Φ hΦ ν hν h hh hhb γ hpos
  filter_upwards [hint, hmasspos] with ω hω hposω
  have hrepresentation := fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω (by simpa using hω)
  have hfinite : DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ≠ ∞ := by
    rw [hrepresentation]
    exact ENNReal.ofReal_ne_top
  have htoRealPos : 0 < (DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal :=
    ENNReal.toReal_pos hposω.ne' hfinite
  simp [ne_of_gt htoRealPos, hfinite]

theorem kahane_field_laplace_of_nonzero_finite_measure_eq
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c)
    (γ s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX ≤
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY :=
  kahane_field_laplace_of_nonzero_finite_measure PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ s hs
    hcov hdiag

/-- Kahane's comparison for all nonpositive powers of continuum field chaos. -/
theorem kahane_field_power_nonpos
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p ≤ 0)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≤
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  classical
  have hPXzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have hPYzero := hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have : IsProbabilityMeasure PX := hPXzero.1
  have : IsProbabilityMeasure PY := hPYzero.1
  by_cases hp0 : p = 0
  · simp [hp0, hPXzero.1.measure_univ, hPYzero.1.measure_univ]
  have hpneg : p < 0 := lt_of_le_of_ne hp hp0
  by_cases hνzero : ν = 0
  · have hmassX (ω : ΩX) : DOZZ.fieldChaosMass PX Φ ν h γ ω = 0 := by
      simp [DOZZ.fieldChaosMass, hνzero]
    have hmassY (ω : ΩY) : DOZZ.fieldChaosMass PY Ψ ν h γ ω = 0 := by
      simp [DOZZ.fieldChaosMass, hνzero]
    have hMX : ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX = ⊤ := by
      calc
        _ = ∫⁻ _ω : ΩX, ⊤ ∂PX := by
          apply lintegral_congr_ae
          exact ae_of_all _ fun ω => by
            change DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p = ⊤
            simp [hmassX ω, ENNReal.zero_rpow_of_neg hpneg]
        _ = ⊤ := by simp [hPXzero.1.measure_univ]
    have hMY : ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY = ⊤ := by
      calc
        _ = ∫⁻ _ω : ΩY, ⊤ ∂PY := by
          apply lintegral_congr_ae
          exact ae_of_all _ fun ω => by
            change DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p = ⊤
            simp [hmassY ω, ENNReal.zero_rpow_of_neg hpneg]
        _ = ⊤ := by simp [hPYzero.1.measure_univ]
    rw [hMX, hMY]
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    apply hνzero
    have hcoerce := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero
    simpa [νf] using hcoerce
  have hS : Nonempty S := by
    have hUniv : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνzero
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
    exact ⟨x⟩
  have : Nonempty S := hS
  let ρ : Measure S := νf.normalize
  have hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have : IsProbabilityMeasure ρ := hρprob
  let α : ℝ := ∫ x, (h x : ℝ) ∂ρ
  have hαnonneg : 0 ≤ α := by
    dsimp [α]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => NNReal.coe_nonneg (h x))
  by_cases hα0 : α = 0
  · have hmassX := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PX Φ νf h hh hhb γ (by simpa [α, ρ] using hα0)
    have hmassY := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PY Ψ νf h hh hhb γ (by simpa [α, ρ] using hα0)
    have hMX : ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX = ⊤ := by
      calc
        _ = ∫⁻ _ω : ΩX, ⊤ ∂PX := by
          apply lintegral_congr_ae
          exact ae_of_all _ fun ω => by
            change DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p = ⊤
            simp [show ν = (νf : Measure S) by rfl, hmassX ω,
              ENNReal.zero_rpow_of_neg hpneg]
        _ = ⊤ := by simp [hPXzero.1.measure_univ]
    have hMY : ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY = ⊤ := by
      calc
        _ = ∫⁻ _ω : ΩY, ⊤ ∂PY := by
          apply lintegral_congr_ae
          exact ae_of_all _ fun ω => by
            change DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p = ⊤
            simp [show ν = (νf : Measure S) by rfl, hmassY ω,
              ENNReal.zero_rpow_of_neg hpneg]
        _ = ⊤ := by simp [hPYzero.1.measure_univ]
    rw [hMX, hMY]
  have hαpos : 0 < α := lt_of_le_of_ne hαnonneg (Ne.symm hα0)
  have hcov' : ∀ᵐ xy ∂(νf : Measure S).prod νf,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) := by
    filter_upwards [hcov] with xy hxy
    simpa [DOZZ.gaussianCovariance] using hxy
  have hdiag' : ∀ᵐ x ∂(νf : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
    filter_upwards [hdiag] with x hx
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx
  let MX : ΩX → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass PX Φ ν h γ ω
  let MY : ΩY → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass PY Ψ ν h γ ω
  let mX : ΩX → ℝ := fun ω => if (MX ω).toReal = 0 then 1 else (MX ω).toReal
  let mY : ΩY → ℝ := fun ω => if (MY ω).toReal = 0 then 1 else (MY ω).toReal
  have hmassMeasX := centeredGaussianField_fieldChaosMass_measurable PX Φ hΦ ν h hh γ
  have hmassMeasY := centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ ν h hh γ
  have hmXMeas : Measurable mX := by
    apply Measurable.ite
      (measurableSet_eq_fun hmassMeasX.ennreal_toReal measurable_const)
    · exact measurable_const
    · exact hmassMeasX.ennreal_toReal
  have hmYMeas : Measurable mY := by
    apply Measurable.ite
      (measurableSet_eq_fun hmassMeasY.ennreal_toReal measurable_const)
    · exact measurable_const
    · exact hmassMeasY.ennreal_toReal
  have hmX : ∀ ω, 0 < mX ω := by
    intro ω
    dsimp [mX]
    split_ifs with hzero
    · norm_num
    · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
  have hmY : ∀ ω, 0 < mY ω := by
    intro ω
    dsimp [mY]
    split_ifs with hzero
    · norm_num
    · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
  have hintX := centeredGaussianField_ae_integrable_weighted_wick PX Φ hΦ νf h hh hhb γ
  have hintY := centeredGaussianField_ae_integrable_weighted_wick PY Ψ hΨ νf h hh hhb γ
  have hmassPosX := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    PX Φ hΦ νf hνf h hh hhb γ (by simpa [ρ, α] using hαpos)
  have hmassPosY := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    PY Ψ hΨ νf hνf h hh hhb γ (by simpa [ρ, α] using hαpos)
  have hmassEqX : ∀ᵐ ω ∂PX, MX ω = ENNReal.ofReal (mX ω) := by
    change ∀ᵐ ω ∂PX,
      DOZZ.fieldChaosMass PX Φ ν h γ ω = ENNReal.ofReal
        (if (DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal = 0 then 1 else
          (DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal)
    exact fieldChaosMass_eq_ofReal_modified_toReal_ae
      PX Φ hΦ νf hνf h hh hhb γ (by simpa [ρ, α] using hαpos)
  have hmassEqY : ∀ᵐ ω ∂PY, MY ω = ENNReal.ofReal (mY ω) := by
    change ∀ᵐ ω ∂PY,
      DOZZ.fieldChaosMass PY Ψ ν h γ ω = ENNReal.ofReal
        (if (DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal = 0 then 1 else
          (DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal)
    exact fieldChaosMass_eq_ofReal_modified_toReal_ae
      PY Ψ hΨ νf hνf h hh hhb γ (by simpa [ρ, α] using hαpos)
  have htoRealEqX : ∀ᵐ ω ∂PX, (MX ω).toReal = mX ω := by
    filter_upwards [hmassEqX] with ω hω
    rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmX ω))]
  have htoRealEqY : ∀ᵐ ω ∂PY, (MY ω).toReal = mY ω := by
    filter_upwards [hmassEqY] with ω hω
    rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmY ω))]
  have hLaplace (t : ℝ) (ht : 0 ≤ t) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mX ω)) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mY ω)) ∂PY := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (MX ω).toReal)) ∂PX := by
        apply lintegral_congr_ae
        filter_upwards [htoRealEqX] with ω hω
        rw [hω]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (MY ω).toReal)) ∂PY := by
        have hcv : ∀ᵐ xy ∂(νf : Measure S).prod νf,
            DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
              DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) := hcov'
        have hdg : ∀ᵐ x ∂(νf : Measure S),
            DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
              DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := hdiag'
        simpa [νf, MX, MY] using kahane_field_laplace_of_nonzero_finite_measure_eq
          PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ t ht hcv hdg
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mY ω)) ∂PY := by
        apply lintegral_congr_ae
        filter_upwards [htoRealEqY] with ω hω
        rw [hω]
  have hMellinX := finite_rpow_neg_lintegral_eq_weighted_laplace PX mX hmX
    hmXMeas.aemeasurable (-p) (neg_pos.mpr hpneg)
  have hMellinY := finite_rpow_neg_lintegral_eq_weighted_laplace PY mY hmY
    hmYMeas.aemeasurable (-p) (neg_pos.mpr hpneg)
  have hMellinCompare :
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume ≤
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p - 1)) *
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
  have hMomentX :
      ∫⁻ ω, MX ω ^ p ∂PX = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hmassEqX] with ω hω
    rw [hω]
    rfl
  have hMomentY :
      ∫⁻ ω, MY ω ^ p ∂PY = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hmassEqY] with ω hω
    rw [hω]
    rfl
  calc
    _ = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX := hMomentX
    _ = ENNReal.ofReal (1 / Real.Gamma (-p)) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume := by
          simpa only [neg_neg] using hMellinX
    _ ≤ ENNReal.ofReal (1 / Real.Gamma (-p)) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume := by
          exact mul_le_mul_of_nonneg_left hMellinCompare (by positivity)
    _ = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY := by
          symm
          simpa only [neg_neg] using hMellinY
    _ = _ := hMomentY.symm


end DOZZ.Proofs
