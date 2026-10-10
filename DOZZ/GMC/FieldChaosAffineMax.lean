/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosSampling
public import DOZZ.GMC.KahaneAffineMaxL1

/-! Continuum covariance comparison for finite maxima of affine tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Spatial sampling transfers the finite affine-max Kahane comparison to normalized field
masses. Joint integrability ensures convergence in mean of the sampled masses. -/
theorem kahane_field_normalized_affine_max
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S] [Fintype κ] [Nonempty κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) (a b : κ → ℝ)
    (hcov : ∀ᵐ q ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω q.1) (fun ω => Φ ω q.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω q.1) (fun ω => Ψ ω q.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    (∫ ω, affineMax a b (∫ x, fieldWickDensity PX Φ h γ ω x
      ∂(ν.normalize : Measure S)) ∂PX) ≤
      ∫ ω, affineMax a b (∫ x, fieldWickDensity PY Ψ h γ ω x
        ∂(ν.normalize : Measure S)) ∂PY := by
  classical
  have : IsProbabilityMeasure PX := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  have : IsProbabilityMeasure PY := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let ρ : Measure S := ν.normalize
  let Q := Measure.infinitePi (fun _ : ℕ => ρ)
  let fX := fieldWickDensity PX Φ h γ
  let fY := fieldWickDensity PY Ψ h γ
  let mX : ΩX → ℝ := fun ω => ∫ x, fX ω x ∂ρ
  let mY : ΩY → ℝ := fun ω => ∫ x, fY ω x ∂ρ
  let avgX : ℕ → ΩX × (ℕ → S) → ℝ :=
    fun n p => (n : ℝ)⁻¹ * ∑ i : Fin n, fX p.1 (p.2 i.val)
  let avgY : ℕ → ΩY × (ℕ → S) → ℝ :=
    fun n p => (n : ℝ)⁻¹ * ∑ i : Fin n, fY p.1 (p.2 i.val)
  have hfX := (fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).1
  have hfY := (fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).1
  have hmX : Integrable mX PX := hfX.integral_prod_left
  have hmY : Integrable mY PY := hfY.integral_prod_left
  have havgX (n : ℕ) : Integrable (avgX n) (PX.prod Q) :=
    spatial_empirical_average_integrable PX ρ fX hfX n
  have havgY (n : ℕ) : Integrable (avgY n) (PY.prod Q) :=
    spatial_empirical_average_integrable PY ρ fY hfY n
  have hIX (n : ℕ) := affineMax_comp_integrable (PX.prod Q) (avgX n) (havgX n) a b
  have hIY (n : ℕ) := affineMax_comp_integrable (PY.prod Q) (avgY n) (havgY n) a b
  have hsample := centeredGaussianField_covariance_order_samples PX PY Φ Ψ hΦ hΨ ν hν hcov hdiag
  have hformulaX (n : ℕ) (ω : ΩX) (u : ℕ → S) :
      DOZZ.finiteChaosMass PX (fun ω (i : Fin n) => Φ ω (u i.val))
        (fun i => (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω = avgX n (ω, u) := by
    dsimp [DOZZ.finiteChaosMass, avgX, fX, fieldWickDensity]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hformulaY (n : ℕ) (ω : ΩY) (u : ℕ → S) :
      DOZZ.finiteChaosMass PY (fun ω (i : Fin n) => Ψ ω (u i.val))
        (fun i => (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω = avgY n (ω, u) := by
    dsimp [DOZZ.finiteChaosMass, avgY, fY, fieldWickDensity]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have horder (n : ℕ) : (∫ p, affineMax a b (avgX n p) ∂(PX.prod Q)) ≤
      ∫ p, affineMax a b (avgY n p) ∂(PY.prod Q) := by
    rw [integral_prod_symm _ (hIX n), integral_prod_symm _ (hIY n)]
    apply integral_mono_ae (hIX n).integral_prod_right (hIY n).integral_prod_right
    filter_upwards [hsample n] with u hu
    have hc := kahane_finite_affine_max PX PY
      (fun ω (i : Fin n) => Φ ω (u i.val)) (fun ω (i : Fin n) => Ψ ω (u i.val))
      (hΦ.2 n (fun i => u i.val)) (hΨ.2 n (fun i => u i.val))
      (fun i => (n : ℝ)⁻¹ * (h (u i.val) : ℝ))
      (fun i => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (NNReal.coe_nonneg _)) γ a b hu
    simpa only [hformulaX, hformulaY] using hc
  have hL1X := spatial_empirical_average_L1 PX ρ fX
    (fieldWickDensity_measurable PX Φ hΦ h hh γ) hfX
    (fun ω x => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
  have hL1Y := spatial_empirical_average_L1 PY ρ fY
    (fieldWickDensity_measurable PY Ψ hΨ h hh γ) hfY
    (fun ω x => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
  have htX := affineMax_integral_tendsto_of_L1 (PX.prod Q) avgX (fun p => mX p.1)
    havgX (hmX.comp_fst Q) hL1X a b
  have htY := affineMax_integral_tendsto_of_L1 (PY.prod Q) avgY (fun p => mY p.1)
    havgY (hmY.comp_fst Q) hL1Y a b
  have hlimit := le_of_tendsto_of_tendsto htX htY (Eventually.of_forall horder)
  have hprodX : (∫ p : ΩX × (ℕ → S), affineMax a b (mX p.1) ∂(PX.prod Q)) =
      ∫ ω, affineMax a b (mX ω) ∂PX := by
    rw [integral_prod _ ((affineMax_comp_integrable PX mX hmX a b).comp_fst Q)]
    simp only [integral_const, probReal_univ, one_smul]
  have hprodY : (∫ p : ΩY × (ℕ → S), affineMax a b (mY p.1) ∂(PY.prod Q)) =
      ∫ ω, affineMax a b (mY ω) ∂PY := by
    rw [integral_prod _ ((affineMax_comp_integrable PY mY hmY a b).comp_fst Q)]
    simp only [integral_const, probReal_univ, one_smul]
  rwa [hprodX, hprodY] at hlimit

/-- Covariance order compares affine maxima of the real values of field masses. -/
theorem kahane_field_affine_max
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ] [Nonempty κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) (a b : κ → ℝ)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX ≤ ∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    (∫ ω, affineMax a b ((DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal) ∂PX) ≤
      ∫ ω, affineMax a b ((DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal) ∂PY := by
  classical
  let : IsProbabilityMeasure PX := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let : IsProbabilityMeasure PY := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  by_cases hν0 : ν = 0
  · simp [hν0, DOZZ.fieldChaosMass]
  let : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)
    exact ⟨x⟩
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    exact hν0 (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero)
  let c : ℝ := νf.mass
  have hscale (x : ℝ) : affineMax (fun i => a i * c) b x = affineMax a b (c * x) := by
    unfold affineMax
    congr 1
    funext i
    ring
  have hcmp := kahane_field_normalized_affine_max PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ
    (fun i => a i * c) b
    (by simpa [νf, DOZZ.gaussianCovariance] using hcov)
    (by simpa [νf, DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hdiag)
  simp_rw [hscale] at hcmp
  have hrepX : (fun ω => affineMax a b ((DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal)) =ᵐ[PX]
      (fun ω => affineMax a b (c * ∫ x, fieldWickDensity PX Φ h γ ω x
        ∂(νf.normalize : Measure S))) := by
    filter_upwards [centeredGaussianField_ae_integrable_weighted_wick PX Φ hΦ νf h hh hhb γ]
      with ω hω
    change affineMax a b ((DOZZ.fieldChaosMass PX Φ (νf : Measure S) h γ ω).toReal) = _
    rw [fieldChaosMass_eq_ofReal_normalized_integral PX Φ νf h γ ω hω,
      ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg _) (integral_nonneg fun _ =>
        mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)))]
    rfl
  have hrepY : (fun ω => affineMax a b ((DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal)) =ᵐ[PY]
      (fun ω => affineMax a b (c * ∫ x, fieldWickDensity PY Ψ h γ ω x
        ∂(νf.normalize : Measure S))) := by
    filter_upwards [centeredGaussianField_ae_integrable_weighted_wick PY Ψ hΨ νf h hh hhb γ]
      with ω hω
    change affineMax a b ((DOZZ.fieldChaosMass PY Ψ (νf : Measure S) h γ ω).toReal) = _
    rw [fieldChaosMass_eq_ofReal_normalized_integral PY Ψ νf h γ ω hω,
      ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg _) (integral_nonneg fun _ =>
        mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)))]
    rfl
  rwa [integral_congr_ae hrepX, integral_congr_ae hrepY]



end DOZZ.Proofs
