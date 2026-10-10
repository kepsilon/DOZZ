/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.LocalSingularMass
public import DOZZ.GMC.Construction.RootedCircleMassLimit

/-! Exact polar removal at a translated insertion. This is the measure-level
substitution preceding identification of the translated lateral chaos law. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Logarithmic distance from an insertion; its value at the root is unused. -/
noncomputable def translatedLogRadius (z x : ℂ) : ℝ := -Real.log ‖x - z‖

/-- Remove the inward radial Wick factor, including the off-center Gaussian origin.
The multiplier is retained on the plane before pushing to the radial coordinate. -/
noncomputable def translatedPolarMeasure (γ N : ℝ) (A : TwoSidedPath)
    (M : Measure ℂ) (F : ℂ → ℝ) (z : ℂ) : Measure ℝ :=
  (M.withDensity (fun x => ENNReal.ofReal (F x) *
    (if x = z then 0 else ENNReal.ofReal
      (Real.exp (-γ * (N + A (translatedLogRadius z x)) +
        γ * Q γ * |translatedLogRadius z x|))))).map
      (translatedLogRadius z)

/-- The translated radial map is measurable on the whole plane. -/
theorem measurable_translatedLogRadius (z : ℂ) :
    Measurable (translatedLogRadius z) := by
  unfold translatedLogRadius
  fun_prop

/-- The removal density is measurable for any measurable multiplier. -/
theorem measurable_translatedPolarDensity (γ N : ℝ) (A : TwoSidedPath)
    (F : ℂ → ℝ) (hF : Measurable F) (z : ℂ) :
    Measurable (fun x => ENNReal.ofReal (F x) *
      (if x = z then 0 else ENNReal.ofReal
        (Real.exp (-γ * (N + A (translatedLogRadius z x)) +
          γ * Q γ * |translatedLogRadius z x|)))) := by
  apply (ENNReal.measurable_ofReal.comp hF).mul
  apply Measurable.ite (measurableSet_singleton z) measurable_const
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp
      ((measurable_const.mul (measurable_const.add
        (A.continuous.measurable.comp (measurable_translatedLogRadius z)))).add
        ((continuous_abs.measurable.comp
          (measurable_translatedLogRadius z)).const_mul (γ * Q γ))))

/-- Any measurable radial test integrates by the literal weighted pushforward formula. -/
theorem translatedPolar_lintegral (γ N : ℝ) (A : TwoSidedPath)
    (M : Measure ℂ) (F : ℂ → ℝ) (hF : Measurable F) (z : ℂ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ t, f t ∂translatedPolarMeasure γ N A M F z =
      ∫⁻ x, (ENNReal.ofReal (F x) *
        (if x = z then 0 else ENNReal.ofReal
          (Real.exp (-γ * (N + A (translatedLogRadius z x)) +
            γ * Q γ * |translatedLogRadius z x|)))) *
          f (translatedLogRadius z x) ∂M := by
  unfold translatedPolarMeasure
  rw [lintegral_map hf (measurable_translatedLogRadius z)]
  exact lintegral_withDensity_eq_lintegral_mul M
      (measurable_translatedPolarDensity γ N A F hF z)
      (hf.comp (measurable_translatedLogRadius z))

/-- The actual singular mass is a drifted radial exponential integral against the
translated projected measure. The root is removed using atomlessness, rather than
altering the infinite insertion weight of `DOZZ.localSingularMass`. -/
theorem localSingularMass_translatedPolar
    (γ α N : ℝ) (A : TwoSidedPath) (M : Measure ℂ)
    (F : ℂ → ℝ) (hF : Measurable F) (z : ℂ) (hMz : M {z} = 0) :
    localSingularMass (fun _ : Unit => M) F z γ α () =
      ENNReal.ofReal (Real.exp (γ * N)) *
        ∫⁻ t, (if 0 < t then
          ENNReal.ofReal (Real.exp (γ * (A t - (Q γ - α) * t))) else 0)
          ∂translatedPolarMeasure γ N A M F z := by
  classical
  let f : ℝ → ℝ≥0∞ := fun t => if 0 < t then
    ENNReal.ofReal (Real.exp (γ * (A t - (Q γ - α) * t))) else 0
  have hf : Measurable f := by
    apply Measurable.ite measurableSet_Ioi
    · exact ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp
          ((A.continuous.measurable.sub (measurable_id.const_mul (Q γ - α))).const_mul γ))
    · exact measurable_const
  change (∫⁻ x, (if x ∈ Metric.ball z 1 then ENNReal.ofReal (F x) *
    ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) else 0) ∂M) =
      ENNReal.ofReal (Real.exp (γ * N)) *
        ∫⁻ t, f t ∂translatedPolarMeasure γ N A M F z
  rw [translatedPolar_lintegral γ N A M F hF z f hf]
  rw [← lintegral_const_mul' (ENNReal.ofReal (Real.exp (γ * N)))
    (fun x : ℂ => (ENNReal.ofReal (F x) *
      (if x = z then 0 else ENNReal.ofReal
        (Real.exp (-γ * (N + A (translatedLogRadius z x)) +
          γ * Q γ * |translatedLogRadius z x|)))) *
            f (translatedLogRadius z x)) ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  have hne : ∀ᵐ x ∂M, x ≠ z := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using hMz
  filter_upwards [hne] with x hx
  have hd : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have ht : 0 < translatedLogRadius z x ↔ x ∈ Metric.ball z 1 := by
    rw [translatedLogRadius, neg_pos, Real.log_neg_iff hd]
    simp only [Metric.mem_ball, dist_eq_norm]
  by_cases hb : x ∈ Metric.ball z 1
  · have htp := ht.mpr hb
    simp only [hb, hx, ite_true, ite_false, f, htp,
      abs_of_pos htp]
    have hpow : ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) =
        ENNReal.ofReal (‖x - z‖ ^ (-γ * α)) := ENNReal.ofReal_rpow_of_pos hd
    rw [hpow]
    symm
    calc
      _ = ENNReal.ofReal (F x) *
          (ENNReal.ofReal (Real.exp (γ * N)) *
            ENNReal.ofReal (Real.exp (-γ * (N + A (translatedLogRadius z x)) +
              γ * Q γ * translatedLogRadius z x)) *
            ENNReal.ofReal (Real.exp (γ *
              (A (translatedLogRadius z x) -
                (Q γ - α) * translatedLogRadius z x)))) := by ac_rfl
      _ = ENNReal.ofReal (F x) * ENNReal.ofReal
          (‖x - z‖ ^ (-γ * α)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le]
        congr 2
        rw [← Real.exp_add, ← Real.exp_add, Real.rpow_def_of_pos hd]
        congr 1
        unfold translatedLogRadius
        ring
  · have htp : ¬0 < translatedLogRadius z x := mt ht.mp hb
    simp only [hb, ite_false, f, htp, mul_zero]

/-- Apply polar removal to the supplied GMC itself, on its common root-atom null event. -/
theorem localSingularMass_translatedPolar_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α : ℝ) (N : Ω → ℝ) (A : Ω → TwoSidedPath)
    (F : ℂ → ℝ) (hF : Measurable F) (z : ℂ) :
    ∀ᵐ ω ∂P, localSingularMass M F z γ α ω =
      ENNReal.ofReal (Real.exp (γ * N ω)) *
        ∫⁻ t, (if 0 < t then
          ENNReal.ofReal (Real.exp (γ * (A ω t - (Q γ - α) * t))) else 0)
          ∂translatedPolarMeasure γ (N ω) (A ω) (M ω) F z := by
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM z] with ω hω
  exact localSingularMass_translatedPolar γ α (N ω) (A ω) (M ω) F hF z hω


end DOZZ.Proofs
