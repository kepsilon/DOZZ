/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.FieldGaussianCommonScalar
public import DOZZ.Correlations.Tails.ProbabilityPullback
public import DOZZ.Correlations.Symmetry.CorrelatedScalarLimit
/-! Preserving the exact common-Gaussian comparison factor at the chaos limit. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A common independent Gaussian has the exact Wick factor for any limiting mass observable,
without assuming that its negative moment is finite. -/
theorem reflected_common_scalar_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (γ c p : ℝ) :
    (∫⁻ u : Ω × ℝ, ENNReal.ofReal
      (Real.exp (γ*c*u.2-γ^2/2*c^2) * Z u.1) ^ p ∂P.prod (gaussianReal 0 1)) =
      ENNReal.ofReal (Real.exp (γ^2*c^2/2*(p^2-p))) *
        ∫⁻ ω, ENNReal.ofReal (Z ω) ^ p ∂P := by
  let Q : Measure ℝ := gaussianReal 0 1
  let G : ℝ → ℝ := fun z => Real.exp (γ*c*z-γ^2/2*c^2)
  have hGp (z : ℝ) : G z ^ p =
      Real.exp (-(p*(γ^2/2*c^2))) * Real.exp ((p*γ*c)*z) := by
    dsimp only [G]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  have hGi : Integrable (fun z => G z ^ p) Q := by
    simp_rw [hGp]
    exact (integrable_exp_mul_gaussianReal (p*γ*c)).const_mul _
  have hGmean : (∫ z, G z ^ p ∂Q) = Real.exp (γ^2*c^2/2*(p^2-p)) := by
    simp_rw [hGp]
    rw [integral_const_mul]
    have hm : (∫ z : ℝ, Real.exp ((p*γ*c)*z) ∂Q) = Real.exp ((p*γ*c)^2/2) := by
      change mgf id Q (p*γ*c) = _
      rw [mgf_id_gaussianReal]
      simp
    rw [hm, ← Real.exp_add]
    congr 1
    ring
  have hH : (∫⁻ z, ENNReal.ofReal (G z) ^ p ∂Q) =
      ENNReal.ofReal (Real.exp (γ^2*c^2/2*(p^2-p))) := by
    rw [show (fun z => ENNReal.ofReal (G z) ^ p) = fun z => ENNReal.ofReal (G z ^ p) by
      funext z
      exact ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hGi
      (ae_of_all _ fun z => Real.rpow_nonneg (Real.exp_pos _).le p), hGmean]
  have hF : AEMeasurable (fun ω => ENNReal.ofReal (Z ω) ^ p) P :=
    hZ.ennreal_ofReal.pow_const p
  have hGm : AEMeasurable (fun z => ENNReal.ofReal (G z) ^ p) Q := by
    have hm : Measurable G := by dsimp only [G]; fun_prop
    exact hm.ennreal_ofReal.aemeasurable.pow_const p
  have he (u : Ω × ℝ) : ENNReal.ofReal (G u.2 * Z u.1) ^ p =
      ENNReal.ofReal (Z u.1) ^ p * ENNReal.ofReal (G u.2) ^ p := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, mul_comm]
  change (∫⁻ u : Ω × ℝ, ENNReal.ofReal (G u.2 * Z u.1) ^ p ∂P.prod Q) = _
  simp_rw [he]
  rw [lintegral_prod_mul hF hGm, hH, mul_comm]

/-- The literal common-Gaussian field mass converges to the multiplied actual limiting mass. -/
theorem reflected_common_scalar_field_limit
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (Φ : ℝ → Ω → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField P (Φ r))
    (ν : Measure S) (h : S → ℝ≥0) (γ c : ℝ) (Z : Ω → ℝ)
    (hconv : TendstoInMeasure P (fun r ω => (fieldChaosMass P (Φ r) ν h γ ω).toReal) atTop Z) :
    TendstoInMeasure (P.prod (gaussianReal 0 1))
      (fun r u => (fieldChaosMass (P.prod (gaussianReal 0 1))
        (fun u x => Φ r u.1 x + c*u.2) ν h γ u).toReal) atTop
      (fun u : Ω × ℝ => Real.exp (γ*c*u.2-γ^2/2*c^2) * Z u.1) := by
  have hc := tendstoInMeasure_measurePreserving P (P.prod (gaussianReal 0 1))
    Prod.fst measurePreserving_fst _ _ atTop hconv
  have hG : Measurable (fun u : Ω × ℝ => Real.exp (γ*c*u.2-γ^2/2*c^2)) := by fun_prop
  have ht := tendstoInMeasure_mul_same_space _ _ _ hG hc
  apply TendstoInMeasure.congr _ (Filter.EventuallyEq.refl _ _) ht
  intro r
  apply ae_of_all
  rintro ⟨ω, z⟩
  dsimp only
  rw [fieldChaosMass_independent_common_scalar_factor P (Φ r) (hΦ r) ν h γ c ω z,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

end DOZZ.Proofs
