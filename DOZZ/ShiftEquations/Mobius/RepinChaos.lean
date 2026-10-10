/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.RepinPotential
public import DOZZ.Statements.Defs.RegularizedGMC
import DOZZ.ShiftEquations.Mobius.AffinePush

/-!
# The chaos of the repinned field

For `ψ(y) = a y + b` the regularized chaos of the repinned circle averages
`X̂_r(y) = X_{r - log|a|}(ψ y) - L` is, sample by sample, the pullback through `ψ` of the
regularized chaos of `X` at cutoff `r - log|a|`, tilted by `e^{-γ L - γ² Var L / 2}` and by the
deterministic factor `e^{γ² C_r(x)} w(x)`, where `C_r(x) = E[X_r(x) L]` and
`w(x) = |ψ⁻¹x|₊⁻⁴ / (|x|₊⁻⁴ |a|²)` is the ratio of background densities. As `r → ∞`,
`C_r → c` uniformly (the repinning potential), so the regularized chaoses converge in probability
to the repinned chaos `ψ⁻¹_*(M e^{-γ L - γ² Var L/2 + γ² c} w)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The inverse affine map `ψ⁻¹(x) = (x - b)/a`. -/
noncomputable def affineInv (a b : ℂ) (x : ℂ) : ℂ := (x - b) / a

theorem affineInv_affine (a b : ℂ) (ha : a ≠ 0) (y : ℂ) : affineInv a b (a * y + b) = y := by
  unfold affineInv
  field_simp
  ring

theorem continuous_affineInv (a b : ℂ) : Continuous (affineInv a b) := by
  unfold affineInv
  fun_prop

/-- The ratio of background densities `w(x) = |ψ⁻¹x|₊⁻⁴ / (|x|₊⁻⁴ |a|²)`. -/
noncomputable def repinWeight (a b : ℂ) (x : ℂ) : ℝ :=
  normPlus (affineInv a b x) ^ (-4 : ℝ) / (normPlus x ^ (-4 : ℝ) * ‖a‖ ^ 2)

theorem normPlus_pos' (x : ℂ) : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem continuous_normPlus' : Continuous normPlus := by
  unfold normPlus
  fun_prop

theorem repinWeight_pos (a b : ℂ) (ha : a ≠ 0) (x : ℂ) : 0 < repinWeight a b x := by
  unfold repinWeight
  have := normPlus_pos' (affineInv a b x)
  have := normPlus_pos' x
  have : 0 < ‖a‖ := norm_pos_iff.mpr ha
  positivity

theorem continuous_repinWeight (a b : ℂ) (ha : a ≠ 0) : Continuous (repinWeight a b) := by
  unfold repinWeight
  have h1 : Continuous fun x => normPlus (affineInv a b x) ^ (-4 : ℝ) :=
    (continuous_normPlus'.comp (continuous_affineInv a b)).rpow_const
      fun x => Or.inl (normPlus_pos' _).ne'
  have h2 : Continuous fun x => normPlus x ^ (-4 : ℝ) * ‖a‖ ^ 2 :=
    (continuous_normPlus'.rpow_const fun x => Or.inl (normPlus_pos' x).ne').mul
      continuous_const
  exact h1.div h2 fun x => by
    have := normPlus_pos' x
    have : 0 < ‖a‖ := norm_pos_iff.mpr ha
    positivity

/-- The background ratio is bounded. -/
theorem repinWeight_le (a b : ℂ) (ha : a ≠ 0) (x : ℂ) :
    repinWeight a b x ≤ (‖a‖ + ‖b‖ + 1) ^ (4 : ℝ) / ‖a‖ ^ 2 := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hy := normPlus_pos' (affineInv a b x)
  have hx := normPlus_pos' x
  have hcmp : normPlus x ≤ (‖a‖ + ‖b‖ + 1) * normPlus (affineInv a b x) := by
    have := AffineKernel.normPlus_affine_le a b (affineInv a b x)
    have he : a * affineInv a b x + b = x := by unfold affineInv; field_simp; ring
    rwa [he] at this
  unfold repinWeight
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hK : 0 < ‖a‖ + ‖b‖ + 1 := by positivity
  rw [Real.rpow_neg hy.le, Real.rpow_neg hx.le]
  have h4 : normPlus x ^ (4 : ℝ) ≤ ((‖a‖ + ‖b‖ + 1) * normPlus (affineInv a b x)) ^ (4 : ℝ) :=
    Real.rpow_le_rpow hx.le hcmp (by norm_num)
  rw [Real.mul_rpow hK.le hy.le] at h4
  have hy4 : 0 < normPlus (affineInv a b x) ^ (4 : ℝ) := Real.rpow_pos_of_pos hy _
  have hx4 : 0 < normPlus x ^ (4 : ℝ) := Real.rpow_pos_of_pos hx _
  field_simp
  nlinarith [hy4, hx4, h4, sq_nonneg ‖a‖]

/-- The repinned circle-average process `X̂_r(y) = X_{r - log|a|}(ψ y) - L`. -/
noncomputable def repinCircle {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (L : Ω → ℝ) (a b : ℂ) :
    Ω → ℂ → ℝ → ℝ :=
  fun ω y r => Xc ω (a * y + b) (r - Real.log ‖a‖) - L ω

/-- Second moment of a difference of square-integrable variables. -/
theorem integral_sub_sq_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U V : Ω → ℝ}
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) :
    ∫ ω, (U ω - V ω) ^ 2 ∂P =
      ∫ ω, U ω ^ 2 ∂P - 2 * ∫ ω, U ω * V ω ∂P + ∫ ω, V ω ^ 2 ∂P := by
  have h1 := hU.integrable_sq
  have h2 : Integrable (fun ω => U ω * V ω) P := hU.integrable_mul hV
  have h3 := hV.integrable_sq
  have h2' : Integrable (fun ω => 2 * U ω * V ω) P :=
    (h2.const_mul 2).congr (ae_of_all _ fun ω => by simp only; ring)
  have hA : Integrable (fun ω => U ω ^ 2 - 2 * U ω * V ω) P := h1.sub h2'
  simp_rw [sub_sq]
  rw [integral_add hA h3, integral_sub h1 h2',
    show (fun ω => 2 * U ω * V ω) = fun ω => 2 * (U ω * V ω) by funext ω; ring,
    integral_const_mul]

/-- The variance profile of a jointly measurable process is measurable. -/
theorem measurable_integral_sq_section {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] (Y : Ω → ℂ → ℝ) (hY : Measurable fun p : Ω × ℂ => Y p.1 p.2) :
    Measurable fun x => ∫ ω, Y ω x ^ 2 ∂P := by
  have hq : Measurable (fun p : ℂ × Ω => Y p.2 p.1 ^ 2) :=
    (hY.comp measurable_swap).pow_const 2
  exact hq.stronglyMeasurable.integral_prod_right.measurable

/-- A regularized chaos integral as a Lebesgue integral. -/
theorem integral_regularizedGMC_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (hmeas : Measurable fun p : Ω × ℂ => Xc p.1 p.2 r)
    (ω : Ω) (f : ℂ → ℝ) :
    ∫ x, f x ∂regularizedGMC P Xc γ r ω =
      ∫ x, Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
        normPlus x ^ (-4 : ℝ) * f x := by
  have hsec : Measurable fun x => Xc ω x r := hmeas.comp (measurable_const.prodMk measurable_id)
  have hV := measurable_integral_sq_section P (fun ω x => Xc ω x r) hmeas
  have hn : Measurable normPlus := continuous_normPlus'.measurable
  unfold regularizedGMC
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (normPlus_pos' x).le _)), smul_eq_mul]

/-- The repinned circle process is jointly measurable. -/
theorem measurable_repinCircle {Ω : Type*} [MeasurableSpace Ω] (Xc : Ω → ℂ → ℝ → ℝ)
    (L : Ω → ℝ) (hmeas : ∀ r, Measurable fun p : Ω × ℂ => Xc p.1 p.2 r) (hL : Measurable L)
    (a b : ℂ) (r : ℝ) : Measurable fun p : Ω × ℂ => repinCircle Xc L a b p.1 p.2 r :=
  ((hmeas (r - Real.log ‖a‖)).comp (measurable_fst.prodMk
    ((measurable_const.mul measurable_snd).add measurable_const))).sub (hL.comp measurable_fst)

/-- **The repinned regularized chaos, sample by sample.** Integrating against the regularized
chaos of the repinned circle averages is integrating against the regularized chaos of `X` at
the shifted cutoff, after the change of variables `x = ψ y` and a tilt. -/
theorem integral_regularizedGMC_repinCircle {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] (Xc : Ω → ℂ → ℝ → ℝ) (L : Ω → ℝ)
    (hmeas : ∀ r, Measurable fun p : Ω × ℂ => Xc p.1 p.2 r) (hL : Measurable L)
    (hXc2 : ∀ x r, MemLp (fun ω => Xc ω x r) 2 P) (hL2 : MemLp L 2 P)
    (a b : ℂ) (ha : a ≠ 0) (γ r : ℝ) (ω : Ω) (f : ℂ → ℝ) :
    ∫ y, f y ∂regularizedGMC P (repinCircle Xc L a b) γ r ω =
      Real.exp (-γ * L ω - γ ^ 2 / 2 * ∫ ω', L ω' ^ 2 ∂P) *
        ∫ x, f (affineInv a b x) *
          Real.exp (γ ^ 2 * ∫ ω', Xc ω' x (r - Real.log ‖a‖) * L ω' ∂P) * repinWeight a b x
          ∂regularizedGMC P Xc γ (r - Real.log ‖a‖) ω := by
  rw [integral_regularizedGMC_eq P _ γ r (measurable_repinCircle Xc L hmeas hL a b r) ω,
    integral_regularizedGMC_eq P Xc γ _ (hmeas _) ω]
  have hcv : ∀ G : ℂ → ℝ, ∫ x, G x = ‖a‖ ^ 2 * ∫ y, G (a * y + b) := fun G => by
    rw [affinePush_integral_comp a b ha G]
    have : ‖a‖ ^ 2 ≠ 0 := by positivity
    field_simp
  conv_rhs => rw [hcv, ← mul_assoc, ← integral_const_mul]
  congr 1
  funext y
  simp only [repinCircle]
  rw [integral_sub_sq_eq (hXc2 _ _) hL2]
  unfold repinWeight
  rw [affineInv_affine a b ha y]
  have hp1 : 0 < normPlus (a * y + b) ^ (-4 : ℝ) := Real.rpow_pos_of_pos (normPlus_pos' _) _
  have ha2 : 0 < ‖a‖ ^ 2 := by have := norm_pos_iff.mpr ha; positivity
  set V := ∫ ω', Xc ω' (a * y + b) (r - Real.log ‖a‖) ^ 2 ∂P
  set C := ∫ ω', Xc ω' (a * y + b) (r - Real.log ‖a‖) * L ω' ∂P
  set VL := ∫ ω', L ω' ^ 2 ∂P
  rw [show γ * (Xc ω (a * y + b) (r - Real.log ‖a‖) - L ω) - γ ^ 2 / 2 * (V - 2 * C + VL) =
      (-γ * L ω - γ ^ 2 / 2 * VL) + (γ * Xc ω (a * y + b) (r - Real.log ‖a‖) - γ ^ 2 / 2 * V) +
        γ ^ 2 * C by ring, Real.exp_add, Real.exp_add]
  field_simp

/-- **The repinned chaos** `ψ⁻¹_*(M e^{-γ L - γ² V/2 + γ² c} w)`. -/
noncomputable def repinChaos {Ω : Type*} (M : Ω → Measure ℂ) (L : Ω → ℝ) (a b : ℂ) (γ V : ℝ)
    (ω : Ω) : Measure ℂ :=
  ((M ω).withDensity fun x => ENNReal.ofReal (Real.exp (-γ * L ω - γ ^ 2 / 2 * V +
    γ ^ 2 * repinPotential a b x) * repinWeight a b x)).map (affineInv a b)

/-- Integrals against the repinned chaos. -/
theorem integral_repinChaos {Ω : Type*} (M : Ω → Measure ℂ) (L : Ω → ℝ) (a b : ℂ)
    (ha : a ≠ 0) (γ V : ℝ) (ω : Ω) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂repinChaos M L a b γ V ω =
      Real.exp (-γ * L ω - γ ^ 2 / 2 * V) *
        ∫ x, f (affineInv a b x) * Real.exp (γ ^ 2 * repinPotential a b x) *
          repinWeight a b x ∂M ω := by
  have hc := continuous_repinPotential a b ha
  have hw := continuous_repinWeight a b ha
  unfold repinChaos
  rw [integral_map (continuous_affineInv a b).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (repinWeight_pos a b ha x).le),
    smul_eq_mul, Real.exp_add]
  ring

/-- The repinned chaos of a finite measure is finite. -/
theorem isFiniteMeasure_repinChaos {Ω : Type*} (M : Ω → Measure ℂ) (L : Ω → ℝ) (a b : ℂ)
    (ha : a ≠ 0) (γ V : ℝ) (ω : Ω) [IsFiniteMeasure (M ω)] :
    IsFiniteMeasure (repinChaos M L a b γ V ω) := by
  obtain ⟨C, hC⟩ := exists_abs_repinPotential_le a b ha
  unfold repinChaos
  have : IsFiniteMeasure ((M ω).withDensity fun x => ENNReal.ofReal (Real.exp (-γ * L ω -
      γ ^ 2 / 2 * V + γ ^ 2 * repinPotential a b x) * repinWeight a b x)) := by
    refine isFiniteMeasure_withDensity_ofReal (HasFiniteIntegral.of_bounded (C :=
      Real.exp (|-γ * L ω - γ ^ 2 / 2 * V| + γ ^ 2 * C) *
        ((‖a‖ + ‖b‖ + 1) ^ (4 : ℝ) / ‖a‖ ^ 2)) (ae_of_all _ fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (repinWeight_pos a b ha x).le)]
    refine mul_le_mul (Real.exp_le_exp.mpr ?_) (repinWeight_le a b ha x)
      (repinWeight_pos a b ha x).le (Real.exp_pos _).le
    have h1 := le_abs_self (-γ * L ω - γ ^ 2 / 2 * V)
    have h2 : γ ^ 2 * repinPotential a b x ≤ γ ^ 2 * C :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC x)) (sq_nonneg γ)
    linarith
  infer_instance

end DOZZ.Proofs

end
