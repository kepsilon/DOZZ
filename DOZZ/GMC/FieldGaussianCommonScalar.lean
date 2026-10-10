/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianCommonScalar
public import DOZZ.GMC.FieldChaosFiniteness

/-! Adding a common independent Gaussian scalar to a measurable Gaussian field. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A common independent Gaussian scalar preserves jointly measurable Gaussian fields. -/
theorem independent_common_scalar_add_isCenteredGaussianField
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ) (c : ℝ) :
    DOZZ.IsCenteredGaussianField (P.prod (gaussianReal 0 1))
      (fun ω x => Φ ω.1 x + c * ω.2) := by
  constructor
  · have hfield : Measurable (fun q : (Ω × ℝ) × S => Φ q.1.1 q.2) :=
      hΦ.1.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact hfield.add (measurable_const.mul (measurable_snd.comp measurable_fst))
  · intro n x
    exact independent_common_scalar_add_isCenteredJointlyGaussian
      P (fun ω i => Φ ω (x i)) (hΦ.2 n x) c

/-- The common scalar adds its variance to every field covariance. -/
theorem gaussianCovariance_field_independent_common_scalar_add
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (c : ℝ) (x y : S) :
    DOZZ.gaussianCovariance (P.prod (gaussianReal 0 1))
      (fun ω => Φ ω.1 x + c * ω.2) (fun ω => Φ ω.1 y + c * ω.2) =
        DOZZ.gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y) + c ^ 2 := by
  let xy : Fin 2 → S := fun i => if i = 0 then x else y
  simpa [xy] using gaussianCovariance_independent_common_scalar_add
    P (fun ω i => Φ ω (xy i)) (hΦ.2 2 xy) c (0 : Fin 2) (1 : Fin 2)

/-- The common Gaussian scalar multiplies the continuum mass by one Wick exponential. -/
theorem fieldChaosMass_independent_common_scalar_factor
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) (h : S → ℝ≥0) (γ c : ℝ) (ω : Ω) (z : ℝ) :
    DOZZ.fieldChaosMass (P.prod (gaussianReal 0 1))
        (fun ω x => Φ ω.1 x + c * ω.2) ν h γ (ω, z) =
      ENNReal.ofReal (Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2)) *
        DOZZ.fieldChaosMass P Φ ν h γ ω := by
  have hvar (x : S) :
      (∫ u : Ω × ℝ, (Φ u.1 x + c * u.2) ^ 2 ∂P.prod (gaussianReal 0 1)) =
        (∫ u, Φ u x ^ 2 ∂P) + c ^ 2 := by
    simpa [DOZZ.gaussianCovariance, pow_two] using
      gaussianCovariance_field_independent_common_scalar_add P Φ hΦ c x x
  unfold DOZZ.fieldChaosMass
  have hpoint (x : S) :
      (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp (γ * (Φ ω x + c * z) - γ ^ 2 / 2 *
        ∫ u : Ω × ℝ, (Φ u.1 x + c * u.2) ^ 2 ∂P.prod (gaussianReal 0 1))) =
      ENNReal.ofReal (Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2)) *
        ((h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp
          (γ * Φ ω x - γ ^ 2 / 2 * ∫ u, Φ u x ^ 2 ∂P))) := by
    rw [hvar]
    rw [show γ * (Φ ω x + c * z) - γ ^ 2 / 2 * ((∫ u, Φ u x ^ 2 ∂P) + c ^ 2) =
      (γ * c * z - γ ^ 2 / 2 * c ^ 2) +
        (γ * Φ ω x - γ ^ 2 / 2 * ∫ u, Φ u x ^ 2 ∂P) by ring,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    ac_rfl
  calc
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2)) *
        ((h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp
          (γ * Φ ω x - γ ^ 2 / 2 * ∫ u, Φ u x ^ 2 ∂P))) ∂ν := by
      apply lintegral_congr_ae
      exact ae_of_all _ hpoint
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The common Gaussian scalar contributes the usual exponential factor to every field moment. -/
theorem fieldChaosMoment_independent_common_scalar_factor
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ b : ℝ≥0, ∀ x, h x ≤ b) (γ c p : ℝ) :
    (∫⁻ ω, DOZZ.fieldChaosMass (P.prod (gaussianReal 0 1))
        (fun ω x => Φ ω.1 x + c * ω.2) ν h γ ω ^ p ∂P.prod (gaussianReal 0 1)) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p))) *
        ∫⁻ ω, DOZZ.fieldChaosMass P Φ ν h γ ω ^ p ∂P := by
  classical
  let : IsProbabilityMeasure P := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let Q : Measure ℝ := gaussianReal 0 1
  let M : Ω → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass P Φ ν h γ ω
  let G : ℝ → ℝ := fun z => Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2)
  let F : Ω → ℝ≥0∞ := fun ω => M ω ^ p
  let H : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (G z) ^ p
  have hFmeas : AEMeasurable F P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h hh γ).aemeasurable
  have hmassFinite : ∀ᵐ ω ∂P, M ω ≠ ∞ := by
    by_cases hνzero : ν = 0
    · simp [M, DOZZ.fieldChaosMass, hνzero]
    · have hS : Nonempty S := by
        obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero
          (Measure.measure_univ_ne_zero.mpr hνzero)
        exact ⟨x⟩
      let : Nonempty S := hS
      exact centeredGaussianField_fieldChaosMass_ne_top_ae P Φ hΦ
        ⟨ν, inferInstance⟩ h hh hhb γ
  have hGmeas : Measurable G := by
    dsimp [G]
    fun_prop
  have hHmeas : AEMeasurable H Q := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hGmeas.comp_aemeasurable measurable_id.aemeasurable).ennreal_ofReal
  have hGpositive (z : ℝ) : 0 < G z := Real.exp_pos _
  have hGpow (z : ℝ) : G z ^ p =
      Real.exp ((p * γ * c) * z - p * (γ ^ 2 / 2 * c ^ 2)) := by
    dsimp [G]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hGintegrable : Integrable (fun z => G z ^ p) Q := by
    have hbase : Integrable (fun z : ℝ => Real.exp ((p * γ * c) * z)) Q :=
      integrable_exp_mul_gaussianReal _
    have hrepr : (fun z : ℝ => G z ^ p) = fun z =>
        Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) * Real.exp ((p * γ * c) * z) := by
      funext z
      rw [hGpow z, ← Real.exp_add]
      congr 1
      ring
    rw [hrepr]
    exact hbase.const_mul _
  have hGmean : (∫ z, G z ^ p ∂Q) =
      Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p)) := by
    have hmgf : (∫ z : ℝ, Real.exp ((p * γ * c) * z) ∂Q) =
        Real.exp ((p * γ * c) ^ 2 / 2) := by
      calc
        (∫ z : ℝ, Real.exp ((p * γ * c) * z) ∂Q) = mgf id Q (p * γ * c) := rfl
        _ = Real.exp ((p * γ * c) ^ 2 / 2) := by
          rw [mgf_id_gaussianReal]
          simp
    calc
      (∫ z, G z ^ p ∂Q) =
          Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) *
            ∫ z, Real.exp ((p * γ * c) * z) ∂Q := by
              calc
                _ = ∫ z, Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) *
                      Real.exp ((p * γ * c) * z) ∂Q := by
                        congr 1
                        funext z
                        rw [hGpow z, ← Real.exp_add]
                        congr 1
                        ring
                _ = _ := integral_const_mul _ _
      _ = Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) *
            Real.exp ((p * γ * c) ^ 2 / 2) := by rw [hmgf]
      _ = Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p)) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hHintegral : (∫⁻ z, H z ∂Q) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p))) := by
    have hnonneg : 0 ≤ᵐ[Q] fun z => G z ^ p :=
      Filter.Eventually.of_forall fun z => Real.rpow_nonneg (le_of_lt (hGpositive z)) p
    rw [show (fun z => H z) = fun z => ENNReal.ofReal (G z ^ p) by
      funext z
      dsimp [H]
      exact ENNReal.ofReal_rpow_of_pos (hGpositive z)]
    rw [← ofReal_integral_eq_lintegral_ofReal hGintegrable hnonneg, hGmean]
  have hfactor : ∀ᵐ u ∂P.prod Q,
      DOZZ.fieldChaosMass (P.prod Q) (fun ω x => Φ ω.1 x + c * ω.2) ν h γ u ^ p =
        F u.1 * H u.2 := by
    have hfst : MeasurePreserving Prod.fst (P.prod Q) P := measurePreserving_fst
    filter_upwards [hfst.quasiMeasurePreserving.ae hmassFinite] with u hu
    rw [fieldChaosMass_independent_common_scalar_factor P Φ hΦ ν h γ c u.1 u.2]
    change (ENNReal.ofReal (G u.2) * M u.1) ^ p = F u.1 * H u.2
    rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hu]
    exact mul_comm _ _
  calc
    _ = ∫⁻ u, F u.1 * H u.2 ∂P.prod Q := lintegral_congr_ae hfactor
    _ = (∫⁻ ω, F ω ∂P) * ∫⁻ z, H z ∂Q := lintegral_prod_mul hFmeas hHmeas
    _ = _ := by rw [hHintegral]; exact mul_comm _ _


end DOZZ.Proofs
