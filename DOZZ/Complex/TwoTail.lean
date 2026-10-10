/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Charge
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Probability.Moments.ComplexMGF

/-!
# Two-tail meromorphic continuation and residues

The upper-tail estimate supplies the positive-strip holomorphic remainder.
Inverse moments extend its lower-tail correction through exponent zero. The residues
are punctured-neighborhood limits, so no values at the poles are asserted.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex Asymptotics ProbabilityTheory
open scoped Real

namespace DOZZ.Proofs

/-- A measurable globally bounded kernel is locally integrable. -/
theorem locallyIntegrableOn_of_bound (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖g t‖ ≤ C) :
    LocallyIntegrableOn g (Ioi 0) := by
  apply (locallyIntegrableOn_const (c := C) (s := Ioi 0)).mono hg
  exact Eventually.of_forall fun t => (hb t).trans_eq (Real.norm_of_nonneg hC).symm

/-- Vanishing below one gives every power bound at the lower endpoint. -/
theorem isBigO_at_zero_of_eq_zero (g : ℝ → ℂ) (hg : ∀ t, t ≤ 1 → g t = 0) (b : ℝ) :
    g =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply IsBigO.of_bound 0
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  rw [hg t ht.le, norm_zero, zero_mul]

/-- Vanishing above one gives every power bound at the upper endpoint. -/
theorem isBigO_at_top_of_eq_zero (g : ℝ → ℂ) (hg : ∀ t, 1 < t → g t = 0) (a : ℝ) :
    g =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  apply IsBigO.of_bound 0
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [hg t ht, norm_zero, zero_mul]

/-- A power bound above one supplies the corresponding upper Mellin endpoint. -/
theorem isBigO_at_top_of_power_bound (g : ℝ → ℂ) (C β : ℝ)
    (hb : ∀ t, 1 ≤ t → ‖g t‖ ≤ C * t ^ (-β)) :
    g =O[atTop] (fun t : ℝ => t ^ (-β)) := by
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  exact (hb t ht).trans_eq (by rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)])

/-- Upper-tail Mellin convergence and holomorphy on the entire left half-plane. -/
theorem mellin_upper_kernel (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (C β : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, ‖g t‖ ≤ C)
    (hzero : ∀ t, t ≤ 1 → g t = 0)
    (hpower : ∀ t, 1 ≤ t → ‖g t‖ ≤ C * t ^ (-β)) :
    (∀ s : ℂ, s.re < β → MellinConvergent g s) ∧
      DifferentiableOn ℂ (mellin g) {s | s.re < β} := by
  have hloc := locallyIntegrableOn_of_bound g hg C hC hbound
  have htop := isBigO_at_top_of_power_bound g C β hpower
  constructor
  · intro s hs
    exact mellinConvergent_of_isBigO_rpow hloc htop hs
      (isBigO_at_zero_of_eq_zero g hzero (s.re - 1)) (by linarith)
  · intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow hloc htop hs
      (isBigO_at_zero_of_eq_zero g hzero (s.re - 1)) (by linarith)).differentiableWithinAt

/-- Lower-tail Mellin convergence and holomorphy to the right of a lower endpoint. -/
theorem mellin_lower_kernel (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (C b : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, ‖g t‖ ≤ C)
    (hzero : ∀ t, 1 < t → g t = 0)
    (hpower : g =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b))) :
    (∀ s : ℂ, b < s.re → MellinConvergent g s) ∧
      DifferentiableOn ℂ (mellin g) {s | b < s.re} := by
  have hloc := locallyIntegrableOn_of_bound g hg C hC hbound
  constructor
  · intro s hs
    exact mellinConvergent_of_isBigO_rpow hloc
      (isBigO_at_top_of_eq_zero g hzero (s.re + 1)) (by linarith) hpower hs
  · intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow hloc
      (isBigO_at_top_of_eq_zero g hzero (s.re + 1)) (by linarith) hpower hs).differentiableWithinAt

/-- A globally bounded lower kernel has lower endpoint zero. -/
theorem mellin_bounded_lower_kernel (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, ‖g t‖ ≤ C)
    (hzero : ∀ t, 1 < t → g t = 0) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent g s) ∧
      DifferentiableOn ℂ (mellin g) {s | 0 < s.re} := by
  apply mellin_lower_kernel g hg C 0 hC hbound hzero
  apply IsBigO.of_bound C
  exact Eventually.of_forall fun t => by simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using hbound t

/-- Positive real powers are exponential moments of the logarithm. -/
theorem integrable_exp_log_of_power {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hpos : ∀ᵐ ω ∂P, 0 < Y ω) (p : ℝ)
    (hp : Integrable (fun ω => Y ω ^ p) P) :
    Integrable (fun ω => Real.exp (p * Real.log (Y ω))) P := by
  apply hp.congr
  filter_upwards [hpos] with ω hω
  rw [Real.rpow_def_of_pos hω, mul_comm]

/-- A positive variable has its complex moment equal to the logarithm's complex MGF. -/
theorem integral_cpow_eq_complexMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hpos : ∀ᵐ ω ∂P, 0 < Y ω) (s : ℂ) :
    (∫ ω, (Y ω : ℂ) ^ s ∂P) = complexMGF (fun ω => Real.log (Y ω)) P s := by
  apply integral_congr_ae
  filter_upwards [hpos] with ω hω
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hω.ne'), ← ofReal_log hω.le, mul_comm]

/-- The open interval of real integrable powers lies inside the logarithmic MGF domain. -/
theorem subset_interior_integrableExpSet_log {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (S : Set ℝ) (hS : IsOpen S) (hmom : ∀ p ∈ S, Integrable (fun ω => Y ω ^ p) P) :
    S ⊆ interior (integrableExpSet (fun ω => Real.log (Y ω)) P) := by
  rw [hS.subset_interior_iff]
  intro p hp
  exact integrable_exp_log_of_power P Y hpos p (hmom p hp)

/-- Ordinary complex moments of a positive variable on any open real exponent domain. -/
theorem complexMoments_of_positive_real_powers {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω) (S : Set ℝ) (hS : IsOpen S)
    (hmom : ∀ p ∈ S, Integrable (fun ω => Y ω ^ p) P) :
    (∀ s : ℂ, s.re ∈ S → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P) {s | s.re ∈ S} := by
  have hsub := subset_interior_integrableExpSet_log P Y hpos S hS hmom
  constructor
  · intro s hs
    apply (integrable_cexp_mul_of_re_mem_integrableExpSet hY.log (interior_subset (hsub hs))).congr
    filter_upwards [hpos] with ω hω
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hω.ne'), ← ofReal_log hω.le, mul_comm]
  · exact (differentiableOn_complexMGF.mono (fun s hs => hsub hs)).congr
      (fun s _ => integral_cpow_eq_complexMGF P Y hpos s)

/-- The positive event is null measurable under the almost-everywhere measurability hypothesis. -/
theorem nullMeasurableSet_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    NullMeasurableSet {ω | 0 < Y ω} P :=
  hY.nullMeasurableSet_preimage measurableSet_Ioi

/-- Restricting to the positive event gives strict positivity almost everywhere. -/
theorem ae_positive_restrict {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    ∀ᵐ ω ∂P.restrict {ω | 0 < Y ω}, 0 < Y ω :=
  ae_restrict_mem₀ (nullMeasurableSet_positive P Y hY)

/-- Away from exponent zero, the zero event contributes zero to a nonnegative complex moment. -/
theorem cpow_eq_positive_indicator_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (s : ℂ) (hs : s ≠ 0) :
    (fun ω => (Y ω : ℂ) ^ s) =ᵐ[P]
      {ω | 0 < Y ω}.indicator (fun ω => (Y ω : ℂ) ^ s) := by
  filter_upwards [hpos] with ω hω
  by_cases h : 0 < Y ω
  · exact (indicator_of_mem (show ω ∈ {ω | 0 < Y ω} from h) (fun ω : Ω => (Y ω : ℂ) ^ s)).symm
  · have heq : Y ω = 0 := le_antisymm (le_of_not_gt h) hω
    rw [indicator_of_notMem (show ω ∉ {ω | 0 < Y ω} from h), heq, ofReal_zero, zero_cpow hs]

/-- Nonnegative ordinary complex moments on a positive open real exponent domain. -/
theorem complexMoments_of_nonnegative_real_powers {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (S : Set ℝ) (hS : IsOpen S) (hSpos : S ⊆ Ioi 0)
    (hmom : ∀ p ∈ S, Integrable (fun ω => Y ω ^ p) P) :
    (∀ s : ℂ, s.re ∈ S → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P) {s | s.re ∈ S} := by
  let μ := P.restrict {ω | 0 < Y ω}
  have hpositive : ∀ᵐ ω ∂μ, 0 < Y ω := ae_positive_restrict P Y hY
  have hrestricted := complexMoments_of_positive_real_powers μ Y hY.restrict hpositive S hS
    (fun p hp => (hmom p hp).integrableOn)
  have hn : NullMeasurableSet {ω | 0 < Y ω} P := nullMeasurableSet_positive P Y hY
  have hne : ∀ s : ℂ, s.re ∈ S → s ≠ 0 := by
    intro s hs heq
    have := hSpos hs
    simp only [heq, zero_re, Set.mem_Ioi, lt_self_iff_false] at this
  have heq : EqOn (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂μ) {s | s.re ∈ S} := by
    intro s hs
    change (∫ ω, (Y ω : ℂ) ^ s ∂P) = ∫ ω in {ω | 0 < Y ω}, (Y ω : ℂ) ^ s ∂P
    rw [← integral_indicator₀ hn]
    exact integral_congr_ae (cpow_eq_positive_indicator_ae P Y hpos s (hne s hs))
  constructor
  · intro s hs
    have hint : IntegrableOn (fun ω => (Y ω : ℂ) ^ s) {ω | 0 < Y ω} P := hrestricted.1 s hs
    exact (hint.integrable_indicator₀ hn).congr
      (cpow_eq_positive_indicator_ae P Y hpos s (hne s hs)).symm
  · exact hrestricted.2.congr (fun s hs => heq hs)

/-- The part of a real tail below one. -/
noncomputable def lowerTailKernel (T : ℝ → ℝ) : ℝ → ℂ :=
  (Ioc 0 1).indicator (fun t => (T t : ℂ))

/-- The upper-tail error after subtracting the two leading powers. -/
noncomputable def upperTailErrorKernel (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun t => ((T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂) : ℝ) : ℂ))

/-- The leading upper-tail power kernel. -/
noncomputable def upperTailPowerKernel (c β : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun t => ((c * t ^ (-β) : ℝ) : ℂ))

/-- The lower-tail kernel is measurable. -/
theorem measurable_lowerTailKernel (T : ℝ → ℝ) (hT : Measurable T) :
    Measurable (lowerTailKernel T) :=
  (Complex.continuous_ofReal.measurable.comp hT).indicator measurableSet_Ioc

/-- The subtracted upper-tail kernel is measurable. -/
theorem measurable_upperTailErrorKernel (T : ℝ → ℝ) (hT : Measurable T)
    (c₁ c₂ β₁ β₂ : ℝ) : Measurable (upperTailErrorKernel T c₁ c₂ β₁ β₂) :=
  (Complex.continuous_ofReal.measurable.comp
    ((hT.sub ((measurable_id.pow_const (-β₁)).const_mul c₁)).sub
      ((measurable_id.pow_const (-β₂)).const_mul c₂))).indicator measurableSet_Ioi

/-- A probability tail bounds the lower-tail kernel by one. -/
theorem norm_lowerTailKernel_le (T : ℝ → ℝ) (hT : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (t : ℝ) :
    ‖lowerTailKernel T t‖ ≤ 1 := by
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [lowerTailKernel, indicator_of_mem ht, norm_real, Real.norm_of_nonneg (hT t).1]
    exact (hT t).2
  · rw [lowerTailKernel, indicator_of_notMem ht, norm_zero]
    exact zero_le_one

/-- The lower-tail transform converges and is holomorphic for positive real part. -/
theorem mellin_lowerTailKernel (T : ℝ → ℝ) (hT : Measurable T)
    (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent (lowerTailKernel T) s) ∧
      DifferentiableOn ℂ (mellin (lowerTailKernel T)) {s | 0 < s.re} := by
  apply mellin_bounded_lower_kernel (lowerTailKernel T)
    (measurable_lowerTailKernel T hT).aestronglyMeasurable 1 zero_le_one
    (norm_lowerTailKernel_le T hb)
  intro t ht
  exact indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr ht) h.2) _

/-- The subtracted upper-tail kernel retains the stated faster power bound. -/
theorem norm_upperTailErrorKernel_le_power (T : ℝ → ℝ) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₃ : 0 ≤ c₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃))
    (t : ℝ) (ht : 1 ≤ t) :
    ‖upperTailErrorKernel T c₁ c₂ β₁ β₂ t‖ ≤ c₃ * t ^ (-β₃) := by
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [upperTailErrorKernel, indicator_of_mem h, norm_real, Real.norm_eq_abs]
    exact htail t ht
  · rw [upperTailErrorKernel, indicator_of_notMem h, norm_zero]
    exact mul_nonneg hc₃ (Real.rpow_nonneg (by linarith) _)

/-- Positive decay makes the upper error globally bounded. -/
theorem norm_upperTailErrorKernel_le (T : ℝ → ℝ) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃))
    (t : ℝ) : ‖upperTailErrorKernel T c₁ c₂ β₁ β₂ t‖ ≤ c₃ := by
  by_cases ht : 1 < t
  · exact (norm_upperTailErrorKernel_le_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₃ htail t ht.le).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos ht.le (neg_nonpos.mpr hβ₃))
        hc₃).trans_eq (mul_one _))
  · rw [upperTailErrorKernel, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from ht), norm_zero]
    exact hc₃

/-- The upper error transform converges and is holomorphic to the left of the third exponent. -/
theorem mellin_upperTailErrorKernel (T : ℝ → ℝ) (hT : Measurable T)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ) (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s : ℂ, s.re < β₃ → MellinConvergent (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) ∧
      DifferentiableOn ℂ (mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂)) {s | s.re < β₃} := by
  apply mellin_upper_kernel _ (measurable_upperTailErrorKernel T hT c₁ c₂ β₁ β₂).aestronglyMeasurable
    c₃ β₃ hc₃ (norm_upperTailErrorKernel_le T c₁ c₂ c₃ β₁ β₂ β₃ hc₃ hβ₃ htail)
  · intro t ht
    exact indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr ht) _
  · exact norm_upperTailErrorKernel_le_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₃ htail

/-- Two powers and a faster error imply a single upper power bound. -/
theorem tail_le_first_power (T : ℝ → ℝ) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (_hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hβ₁₂ : β₁ ≤ β₂) (hβ₂₃ : β₂ ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃))
    (t : ℝ) (ht : 1 ≤ t) : T t ≤ (c₁ + c₂ + c₃) * t ^ (-β₁) := by
  have h := (le_abs_self (T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂))).trans (htail t ht)
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hβ₁₂)) hc₂
  have h₃ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg (hβ₁₂.trans hβ₂₃))) hc₃
  nlinarith

/-- The full tail's Mellin transform converges in the original positive moment strip. -/
theorem mellin_full_tail (T : ℝ → ℝ) (hT : Measurable T)
    (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (C β : ℝ)
    (htop : ∀ t, 1 ≤ t → T t ≤ C * t ^ (-β)) (s : ℂ)
    (hs : 0 < s.re ∧ s.re < β) : MellinConvergent (fun t => (T t : ℂ)) s := by
  have hg : AEStronglyMeasurable (fun t => (T t : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp hT).aestronglyMeasurable
  have hbound : ∀ t, ‖(T t : ℂ)‖ ≤ 1 := fun t => by
    rw [norm_real, Real.norm_of_nonneg (hb t).1]; exact (hb t).2
  apply mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_of_bound _ hg 1 zero_le_one hbound)
    (isBigO_at_top_of_power_bound _ C β fun t ht => by
      rw [norm_real, Real.norm_of_nonneg (hb t).1]; exact htop t ht) hs.2
    (b := 0)
  · apply IsBigO.of_bound 1
    exact Eventually.of_forall fun t => by
      simpa only [neg_zero, Real.rpow_zero, norm_one, one_mul] using hbound t
  · exact hs.1

/-- The leading upper power has its elementary rational Mellin transform. -/
theorem hasMellin_upperTailPowerKernel (c β : ℝ) (s : ℂ) (hs : s.re < β) :
    HasMellin (upperTailPowerKernel c β) s ((c : ℂ) / ((β : ℂ) - s)) := by
  let a : ℂ := s - 1 - (β : ℂ)
  have ha : a.re < -1 := by dsimp [a]; linarith
  have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • upperTailPowerKernel c β t) =
      (Ioi (1 : ℝ)).indicator (fun t => (c : ℂ) * (t : ℂ) ^ a) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · have htpos : 0 < t := lt_trans zero_lt_one ht
      rw [upperTailPowerKernel, indicator_of_mem ht, indicator_of_mem ht,
        ofReal_mul, ofReal_cpow htpos.le, ofReal_neg, smul_eq_mul]
      rw [mul_left_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr htpos.ne')]
      rfl
    · rw [upperTailPowerKernel, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ ht => lt_trans zero_lt_one ht
  have hint : IntegrableOn (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ a) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).const_mul _
  constructor
  · rw [MellinConvergent, heq]
    exact hint.integrable_indicator measurableSet_Ioi |>.integrableOn
  · rw [mellin, heq, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset hsub, integral_const_mul,
      integral_Ioi_cpow_of_lt ha zero_lt_one, ofReal_one, one_cpow]
    have he : a + 1 = -((β : ℂ) - s) := by dsimp [a]; ring
    rw [he, div_neg, neg_div, neg_neg]
    ring

/-- A tail is the sum of its lower part, upper error, and leading powers on the integration domain. -/
theorem tail_kernel_decomposition (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) :
    EqOn (fun t => (T t : ℂ))
      (fun t => (lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t) +
        (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)) (Ioi 0) := by
  intro t ht
  change (T t : ℂ) = (lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t) +
    (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)
  by_cases h : t ≤ 1
  · simp only [lowerTailKernel, upperTailErrorKernel, upperTailPowerKernel,
      indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, h⟩),
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr h)]
    simp only [add_zero]
  · have h1 : 1 < t := lt_of_not_ge h
    simp only [lowerTailKernel, upperTailErrorKernel, upperTailPowerKernel,
      indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr h1) h.2),
      indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1)]
    push_cast
    ring

/-- The full Mellin transform is the rational subtraction plus the two remainder transforms. -/
theorem mellin_tail_decomposition (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ)
    (h₁ : s.re < β₁) (h₂ : s.re < β₂)
    (hl : MellinConvergent (lowerTailKernel T) s)
    (he : MellinConvergent (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) :
    s * mellin (fun t => (T t : ℂ)) s = twoTailRational c₁ c₂ β₁ β₂ s +
      s * (mellin (lowerTailKernel T) s + mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) := by
  have hp₁ := hasMellin_upperTailPowerKernel c₁ β₁ s h₁
  have hp₂ := hasMellin_upperTailPowerKernel c₂ β₂ s h₂
  have hr := hasMellin_add hl he
  have hp := hasMellin_add hp₁.1 hp₂.1
  have hall := hasMellin_add hr.1 hp.1
  have hfull : mellin (fun t => (T t : ℂ)) s =
      mellin (fun t => lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t +
        (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact congrArg (fun w : ℂ => (t : ℂ) ^ (s - 1) • w)
      (tail_kernel_decomposition T c₁ c₂ β₁ β₂ ht)
  rw [hfull, hall.2, hr.2, hp.2, hp₁.2, hp₂.2, twoTailRational]
  ring

/-- Mellin convergence of a nonnegative real tail gives its real weighted integrability. -/
theorem integrable_real_tail_of_mellin (T : ℝ → ℝ) (hT : Measurable T)
    (hn : ∀ t, 0 ≤ T t) (p : ℝ) (hm : MellinConvergent (fun t => (T t : ℂ)) (p : ℂ)) :
    IntegrableOn (fun t => T t * t ^ (p - 1)) (Ioi 0) := by
  have h := (mellin_convergent_iff_norm (T := Ioi 0) Subset.rfl measurableSet_Ioi
    ((Complex.continuous_ofReal.measurable.comp hT).aestronglyMeasurable.restrict)).mp hm
  apply h.congr
  filter_upwards with t
  change t ^ (p - 1) * ‖(T t : ℂ)‖ = T t * t ^ (p - 1)
  rw [norm_real, Real.norm_of_nonneg (hn t), mul_comm]

/-- The real moment layer cake expressed as a complex Mellin identity. -/
theorem complexMoment_real_eq_mellin_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (p : ℝ) (hp : 0 < p)
    (hm : MellinConvergent (fun t => (realUpperTail P Y hY t : ℂ)) (p : ℂ)) :
    Integrable (fun ω => Y ω ^ p) P ∧
      (∫ ω, (Y ω : ℂ) ^ (p : ℂ) ∂P) = (p : ℂ) *
        mellin (fun t => (realUpperTail P Y hY t : ℂ)) (p : ℂ) := by
  let T := realUpperTail P Y hY
  have ht := integrable_real_tail_of_mellin T (measurable_realUpperTail P Y hY)
    (fun t => (realUpperTail_bounds P Y hY t).1) p hm
  have hreal := integral_rpow_eq_tail_of_integrable P Y hY hpos p hp ht
  refine ⟨hreal.1, ?_⟩
  have hcpow : (fun ω => (Y ω : ℂ) ^ (p : ℂ)) =ᵐ[P] (fun ω => ((Y ω ^ p : ℝ) : ℂ)) :=
    hpos.mono fun ω hω => (ofReal_cpow hω p).symm
  rw [integral_congr_ae hcpow, integral_complex_ofReal, hreal.2, ofReal_mul]
  congr 1
  rw [mellin, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change ((realUpperTail P Y hY t * t ^ (p - 1) : ℝ) : ℂ) =
    (t : ℂ) ^ ((p : ℂ) - 1) * (realUpperTail P Y hY t : ℂ)
  rw [ofReal_mul, ofReal_cpow ht.le, ofReal_sub, ofReal_one, mul_comm]

/-- The positive moment strip is real-convex and connected. -/
theorem convex_positiveMomentStrip (β : ℝ) : Convex ℝ (positiveMomentStrip β) := by
  exact (convex_Ioo (0 : ℝ) β).linear_preimage Complex.reLm

/-- Scalar identity on a moment strip from all its positive real exponents. -/
theorem eqOn_positiveMomentStrip_of_real (β : ℝ) (hβ : 0 < β) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (positiveMomentStrip β))
    (hg : DifferentiableOn ℂ g (positiveMomentStrip β))
    (heq : ∀ p : ℝ, 0 < p → p < β → f (p : ℂ) = g (p : ℂ)) :
    EqOn f g (positiveMomentStrip β) := by
  have ha : ((β / 2 : ℝ) : ℂ) ∈ positiveMomentStrip β :=
    mem_positiveMomentStrip_real (half_pos hβ) (half_lt_self hβ)
  apply (hf.analyticOnNhd (isOpen_positiveMomentStrip β)).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd (isOpen_positiveMomentStrip β)) (convex_positiveMomentStrip β).isPreconnected ha
  apply frequently_eq_of_real_interval (β / 2) (β / 2) (half_pos hβ)
  intro p hp
  have h := abs_lt.mp hp
  apply heq p <;> linarith

/-- The positive-strip remainder after upper-tail subtraction. -/
noncomputable def twoTailRemainder (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) : ℂ :=
  s * (mellin (lowerTailKernel T) s + mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s)

/-- Both remainder kernels are holomorphic throughout the larger positive strip. -/
theorem differentiableOn_twoTailRemainder (T : ℝ → ℝ) (hT : Measurable T)
    (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    DifferentiableOn ℂ (twoTailRemainder T c₁ c₂ β₁ β₂) (positiveMomentStrip β₃) := by
  exact differentiableOn_id.mul
    (((mellin_lowerTailKernel T hT hb).2.mono (fun _ hs => hs.1)).add
      ((mellin_upperTailErrorKernel T hT c₁ c₂ c₃ β₁ β₂ β₃ hc₃ hβ₃ htail).2.mono
        (fun _ hs => hs.2)))

/-- The rational part is holomorphic strictly to the left of both poles. -/
theorem differentiableOn_twoTailRational_left (c₁ c₂ β₁ β₂ : ℝ) (hβ : β₁ ≤ β₂) :
    DifferentiableOn ℂ (twoTailRational c₁ c₂ β₁ β₂) {s : ℂ | s.re < β₁} := by
  intro s hs
  change s.re < β₁ at hs
  have hne₁ : (β₁ : ℂ) - s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [ofReal_re] at hr
    linarith
  have hne₂ : (β₂ : ℂ) - s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [ofReal_re] at hr
    linarith
  exact (((differentiableAt_const (c := (c₁ : ℂ))).mul differentiableAt_id).div
    ((differentiableAt_const (c := (β₁ : ℂ))).sub differentiableAt_id) hne₁ |>.add
    (((differentiableAt_const (c := (c₂ : ℂ))).mul differentiableAt_id).div
      ((differentiableAt_const (c := (β₂ : ℂ))).sub differentiableAt_id) hne₂)).differentiableWithinAt

/-- A holomorphic remainder added to the rational part is meromorphic. -/
theorem meromorphicOn_twoTailRational_add (c₁ c₂ β₁ β₂ : ℝ) (r : ℂ → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hr : DifferentiableOn ℂ r U) :
    MeromorphicOn (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) U := by
  have hrat : MeromorphicOn (twoTailRational c₁ c₂ β₁ β₂) U :=
    fun s _ => meromorphic_twoTailRational c₁ c₂ β₁ β₂ s
  exact hrat.add ((hr.analyticOnNhd hU).meromorphicOn)

/-- Proof of `DOZZ.complexMoment_two_tail_residues`: the two-power continuation built from the
displayed tail estimate. -/
theorem complexMoment_two_tail_residues {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ < β₂) (hβ₂₃ : β₂ < β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s ∈ positiveMomentStrip β₁, Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
    DifferentiableOn ℂ (fun s => ∫ ω, (Y ω : ℂ) ^ s ∂P) (positiveMomentStrip β₁) ∧
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (positiveMomentStrip β₃) ∧
      MeromorphicOn (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s)
        (positiveMomentStrip β₃) ∧
      (∀ s ∈ positiveMomentStrip β₁,
        (∫ ω, (Y ω : ℂ) ^ s ∂P) = twoTailRational c₁ c₂ β₁ β₂ s + r s) ∧
      Tendsto (fun s => (s - (β₁ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₁ : ℂ)) (𝓝 (-(β₁ * c₁ : ℝ) : ℂ)) ∧
      Tendsto (fun s => (s - (β₂ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₂ : ℂ)) (𝓝 (-(β₂ * c₂ : ℝ) : ℂ)) := by
  let T := realUpperTail P Y hY
  have hT := measurable_realUpperTail P Y hY
  have hb := realUpperTail_bounds P Y hY
  have hβ₃ : 0 < β₃ := hβ₁.trans (hβ₁₂.trans hβ₂₃)
  have htop := tail_le_first_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₁.le hc₂.le hc₃.le hβ₁₂.le hβ₂₃.le htail
  have hmoment : ∀ p ∈ Ioo (0 : ℝ) β₁, Integrable (fun ω => Y ω ^ p) P := by
    intro p hp
    exact (complexMoment_real_eq_mellin_tail P Y hY hpos p hp.1
      (mellin_full_tail T hT hb (c₁ + c₂ + c₃) β₁ htop (p : ℂ) hp)).1
  have hord := complexMoments_of_nonnegative_real_powers P Y hY hpos (Ioo 0 β₁) isOpen_Ioo
    (fun _ hp => hp.1) hmoment
  let r := twoTailRemainder T c₁ c₂ β₁ β₂
  have hr : DifferentiableOn ℂ r (positiveMomentStrip β₃) :=
    differentiableOn_twoTailRemainder T hT hb c₁ c₂ c₃ β₁ β₂ β₃ hc₃.le hβ₃.le htail
  have hsub : positiveMomentStrip β₁ ⊆ positiveMomentStrip β₃ :=
    fun _ hs => ⟨hs.1, hs.2.trans (hβ₁₂.trans hβ₂₃)⟩
  have hformula : EqOn (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) (positiveMomentStrip β₁) := by
    apply eqOn_positiveMomentStrip_of_real β₁ hβ₁ _ _ hord.2
      (((differentiableOn_twoTailRational_left c₁ c₂ β₁ β₂ hβ₁₂.le).mono
        (fun _ hs => hs.2)).add (hr.mono hsub))
    intro p hp hpβ
    rw [(complexMoment_real_eq_mellin_tail P Y hY hpos p hp
      (mellin_full_tail T hT hb (c₁ + c₂ + c₃) β₁ htop (p : ℂ) ⟨hp, hpβ⟩)).2]
    exact mellin_tail_decomposition T c₁ c₂ β₁ β₂ (p : ℂ) hpβ (hpβ.trans hβ₁₂)
      ((mellin_lowerTailKernel T hT hb).1 _ hp)
      ((mellin_upperTailErrorKernel T hT c₁ c₂ c₃ β₁ β₂ β₃ hc₃.le hβ₃.le htail).1 _
        (hpβ.trans (hβ₁₂.trans hβ₂₃)))
  have hmem₁ := mem_positiveMomentStrip_real hβ₁ (hβ₁₂.trans hβ₂₃)
  have hmem₂ := mem_positiveMomentStrip_real (hβ₁.trans hβ₁₂) hβ₂₃
  refine ⟨hord.1, hord.2, r, hr,
    meromorphicOn_twoTailRational_add c₁ c₂ β₁ β₂ r _ (isOpen_positiveMomentStrip β₃) hr,
    fun s hs => hformula hs, ?_, ?_⟩
  · exact tendsto_twoTailRational_first c₁ c₂ β₁ β₂ hβ₁₂.ne r
      (hr.continuousOn.continuousAt ((isOpen_positiveMomentStrip β₃).mem_nhds hmem₁))
  · exact tendsto_twoTailRational_second c₁ c₂ β₁ β₂ hβ₁₂.ne r
      (hr.continuousOn.continuousAt ((isOpen_positiveMomentStrip β₃).mem_nhds hmem₂))

/-- The complementary probability tail is nonnegative and bounded by one. -/
theorem lowerProbability_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) (t : ℝ) :
    0 ≤ 1 - realUpperTail P Y hY t ∧ 1 - realUpperTail P Y hY t ≤ 1 := by
  have h := realUpperTail_bounds P Y hY t
  constructor <;> linarith

/-- The complement of the strict upper event is the lower probability used here. -/
theorem lowerProbability_eq_integral_indicator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) (t : ℝ) :
    1 - realUpperTail P Y hY t = ∫ ω, {ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ)) ω ∂P := by
  have hu : NullMeasurableSet {ω | t < Y ω} P := hY.nullMeasurableSet_preimage measurableSet_Ioi
  have hl : NullMeasurableSet {ω | Y ω ≤ t} P := hY.nullMeasurableSet_preimage measurableSet_Iic
  have heq : {ω | Y ω ≤ t} = {ω | t < Y ω}ᶜ := by ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
  rw [integral_indicator₀ hl, integral_const]
  simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  have h := probReal_compl_eq_one_sub₀ hu
  rw [heq]
  exact h.symm

/-- Markov's lower-tail bound from one inverse moment; no independence or density is used. -/
theorem lowerProbability_le_inverseMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω) (q : ℝ) (hq : 0 < q)
    (hint : Integrable (fun ω => Y ω ^ (-q)) P) (t : ℝ) (ht : 0 < t) :
    1 - realUpperTail P Y hY t ≤ (∫ ω, Y ω ^ (-q) ∂P) * t ^ q := by
  have hl : NullMeasurableSet {ω | Y ω ≤ t} P := hY.nullMeasurableSet_preimage measurableSet_Iic
  have hconst : Integrable ({ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator₀ hl
  have hbound : ∀ᵐ ω ∂P, {ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ)) ω ≤
      t ^ q * Y ω ^ (-q) := by
    filter_upwards [hpos] with ω hω
    by_cases h : Y ω ≤ t
    · rw [indicator_of_mem (show ω ∈ {ω | Y ω ≤ t} from h)]
      have hp := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hω h (neg_nonpos.mpr hq.le)) (Real.rpow_pos_of_pos ht q).le
      have heq : t ^ q * t ^ (-q) = 1 := by rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
      exact heq ▸ hp
    · rw [indicator_of_notMem (show ω ∉ {ω | Y ω ≤ t} from h)]
      exact mul_nonneg (Real.rpow_pos_of_pos ht q).le (Real.rpow_pos_of_pos hω (-q)).le
  rw [lowerProbability_eq_integral_indicator P Y hY t]
  have h := integral_mono_ae hconst (hint.const_mul (t ^ q)) hbound
  rw [integral_const_mul, mul_comm] at h
  exact h

/-- Inverse moments give an entire Mellin transform for the lower-probability kernel. -/
theorem differentiable_mellin_lowerProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P) :
    (∀ s : ℂ, MellinConvergent (lowerTailKernel (fun t => 1 - realUpperTail P Y hY t)) s) ∧
      Differentiable ℂ (mellin (lowerTailKernel (fun t => 1 - realUpperTail P Y hY t))) := by
  let T := fun t => 1 - realUpperTail P Y hY t
  have hT : Measurable T := measurable_const.sub (measurable_realUpperTail P Y hY)
  have hb := lowerProbability_bounds P Y hY
  have hglob := norm_lowerTailKernel_le T hb
  have hzero : ∀ t, 1 < t → lowerTailKernel T t = 0 := by
    intro t ht
    exact indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr ht) h.2) _
  have hlocal : ∀ s : ℂ, MellinConvergent (lowerTailKernel T) s ∧
      DifferentiableAt ℂ (mellin (lowerTailKernel T)) s := by
    intro s
    let q := max 1 (1 - s.re)
    have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hs : -q < s.re := by have := le_max_right (1 : ℝ) (1 - s.re); dsimp [q]; linarith
    have hint := hinv q hq
    let C := ∫ ω, Y ω ^ (-q) ∂P
    have hC : 0 ≤ C := integral_nonneg_of_ae (hpos.mono fun ω hω => (Real.rpow_pos_of_pos hω _).le)
    have hpower : lowerTailKernel T =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-q))) := by
      apply IsBigO.of_bound C
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [neg_neg, Real.norm_of_nonneg (Real.rpow_pos_of_pos ht q).le]
      by_cases h : t ∈ Ioc (0 : ℝ) 1
      · rw [lowerTailKernel, indicator_of_mem h, norm_real, Real.norm_of_nonneg (hb t).1]
        exact lowerProbability_le_inverseMoment P Y hY hpos q hq hint t ht
      · rw [lowerTailKernel, indicator_of_notMem h, norm_zero]
        exact mul_nonneg hC (Real.rpow_pos_of_pos ht q).le
    have hloc := locallyIntegrableOn_of_bound (lowerTailKernel T)
      (measurable_lowerTailKernel T hT).aestronglyMeasurable 1 zero_le_one hglob
    have htop := isBigO_at_top_of_eq_zero (lowerTailKernel T) hzero (s.re + 1)
    exact ⟨mellinConvergent_of_isBigO_rpow hloc htop (by linarith) hpower hs,
      mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hpower hs⟩
  exact ⟨fun s => (hlocal s).1, fun s => (hlocal s).2⟩

/-- Lower tail and lower probability sum to the elementary unit interval kernel. -/
theorem lowerTailKernel_add_complement (T : ℝ → ℝ) :
    (fun t => lowerTailKernel T t + lowerTailKernel (fun x => 1 - T x) t) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [lowerTailKernel, indicator_of_mem ht]
    push_cast
    ring
  · simp only [lowerTailKernel, indicator_of_notMem ht, add_zero]

/-- The positive-strip lower-tail representation agrees with its continuation through zero. -/
theorem lowerTail_mellin_complement (T : ℝ → ℝ) (hT : Measurable T)
    (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (s : ℂ) (hs : 0 < s.re) :
    s * (mellin (lowerTailKernel T) s + mellin (lowerTailKernel (fun t => 1 - T t)) s) = 1 := by
  have hq : ∀ t, 0 ≤ 1 - T t ∧ 1 - T t ≤ 1 := by
    intro t
    have h := hb t
    constructor <;> linarith
  have hsum := hasMellin_add ((mellin_lowerTailKernel T hT hb).1 s hs)
    ((mellin_lowerTailKernel (fun t => 1 - T t) (measurable_const.sub hT) hq).1 s hs)
  rw [lowerTailKernel_add_complement T] at hsum
  have hunit := hasMellin_one_Ioc hs
  have heq : mellin (lowerTailKernel T) s + mellin (lowerTailKernel (fun t => 1 - T t)) s = 1 / s :=
    hsum.2.symm.trans hunit.2
  have hne : s ≠ 0 := fun h => (ne_of_gt hs) (congrArg Complex.re h)
  rw [heq, mul_one_div_cancel hne]

/-- The lower-probability remainder extends the upper-error Mellin remainder through zero. -/
noncomputable def inverseTailRemainder (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) : ℂ :=
  1 - s * mellin (lowerTailKernel (fun t => 1 - T t)) s +
    s * mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s

/-- The two remainder formulas agree on positive real part. -/
theorem inverseTailRemainder_eq_twoTailRemainder (T : ℝ → ℝ) (hT : Measurable T)
    (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    inverseTailRemainder T c₁ c₂ β₁ β₂ s = twoTailRemainder T c₁ c₂ β₁ β₂ s := by
  have h := lowerTail_mellin_complement T hT hb s hs
  unfold inverseTailRemainder twoTailRemainder
  linear_combination -h

/-- A real-part half-plane is open. -/
theorem isOpen_realPart_lt (β : ℝ) : IsOpen {s : ℂ | s.re < β} :=
  isOpen_lt Complex.continuous_re continuous_const

/-- Scalar identity in a left half-plane from its positive real interval. -/
theorem eqOn_realPart_lt_of_positive_real (β : ℝ) (hβ : 0 < β) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < β})
    (hg : DifferentiableOn ℂ g {s : ℂ | s.re < β})
    (heq : ∀ p : ℝ, 0 < p → p < β → f (p : ℂ) = g (p : ℂ)) :
    EqOn f g {s : ℂ | s.re < β} := by
  have hconv : Convex ℝ {s : ℂ | s.re < β} := (convex_Iio β).linear_preimage Complex.reLm
  have ha : ((β / 2 : ℝ) : ℂ) ∈ {s : ℂ | s.re < β} := half_lt_self hβ
  apply (hf.analyticOnNhd (isOpen_realPart_lt β)).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd (isOpen_realPart_lt β)) hconv.isPreconnected ha
  apply frequently_eq_of_real_interval (β / 2) (β / 2) (half_pos hβ)
  intro p hp
  have h := abs_lt.mp hp
  apply heq p <;> linarith

/-- All inverse moments extend real power integrability throughout the ordinary left half-plane. -/
theorem integrable_real_power_of_two_tail_inverse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hβ₁₂ : β₁ ≤ β₂) (hβ₂₃ : β₂ ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃))
    (p : ℝ) (hp : p < β₁) : Integrable (fun ω => Y ω ^ p) P := by
  by_cases h : p < 0
  · simpa only [neg_neg] using hinv (-p) (neg_pos.mpr h)
  · by_cases hzero : p = 0
    · simp only [hzero, Real.rpow_zero]
      exact integrable_const 1
    · have hposp : 0 < p := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hzero)
      have htop := tail_le_first_power (realUpperTail P Y hY) c₁ c₂ c₃ β₁ β₂ β₃
        hc₁ hc₂ hc₃ hβ₁₂ hβ₂₃ htail
      exact (complexMoment_real_eq_mellin_tail P Y hY (hpos.mono fun _ h => h.le) p hposp
        (mellin_full_tail (realUpperTail P Y hY) (measurable_realUpperTail P Y hY)
          (realUpperTail_bounds P Y hY) (c₁ + c₂ + c₃) β₁ htop (p : ℂ) ⟨hposp, hp⟩)).1

/-- The inverse-tail remainder is holomorphic on the full continuation half-plane. -/
theorem differentiableOn_inverseTailRemainder {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ) (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    DifferentiableOn ℂ (inverseTailRemainder (realUpperTail P Y hY) c₁ c₂ β₁ β₂)
      {s : ℂ | s.re < β₃} := by
  have hl : DifferentiableOn ℂ (mellin (lowerTailKernel (fun t => 1 - realUpperTail P Y hY t)))
      {s : ℂ | s.re < β₃} := (differentiable_mellin_lowerProbability P Y hY hpos hinv).2.differentiableOn
  have hu := (mellin_upperTailErrorKernel (realUpperTail P Y hY) (measurable_realUpperTail P Y hY)
    c₁ c₂ c₃ β₁ β₂ β₃ hc₃ hβ₃ htail).2
  exact ((differentiableOn_const (1 : ℂ)).sub (differentiableOn_id.mul hl)).add
    (differentiableOn_id.mul hu)

/-- The lower-tail correction has its exact value at exponent zero. -/
theorem inverseTailRemainder_zero (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) :
    inverseTailRemainder T c₁ c₂ β₁ β₂ 0 = 1 := by
  simp only [inverseTailRemainder, zero_mul, sub_zero, add_zero]

/-- Proof of `DOZZ.complexMoment_two_tail_residues_of_inverse_moments`: the lower-tail extension,
with every inverse moment kept as a separate input. -/
theorem complexMoment_two_tail_residues_of_inverse_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ < β₂) (hβ₂₃ : β₂ < β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s : ℂ, s.re < β₁ → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      {s : ℂ | s.re < β₁} ∧
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r {s | s.re < β₃} ∧
      MeromorphicOn (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) {s | s.re < β₃} ∧
      (∀ s : ℂ, s.re < β₁ →
        (∫ ω, (Y ω : ℂ) ^ s ∂P) = twoTailRational c₁ c₂ β₁ β₂ s + r s) ∧
      r 0 = 1 ∧
      Tendsto (fun s => (s - (β₁ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₁ : ℂ)) (𝓝 (-(β₁ * c₁ : ℝ) : ℂ)) ∧
      Tendsto (fun s => (s - (β₂ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₂ : ℂ)) (𝓝 (-(β₂ * c₂ : ℝ) : ℂ)) := by
  let T := realUpperTail P Y hY
  have hT := measurable_realUpperTail P Y hY
  have hb := realUpperTail_bounds P Y hY
  have hβ₃ : 0 < β₃ := hβ₁.trans (hβ₁₂.trans hβ₂₃)
  have htop := tail_le_first_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₁.le hc₂.le hc₃.le hβ₁₂.le hβ₂₃.le htail
  have hmoment : ∀ p ∈ Iio β₁, Integrable (fun ω => Y ω ^ p) P :=
    integrable_real_power_of_two_tail_inverse P Y hY hpos hinv c₁ c₂ c₃ β₁ β₂ β₃
      hc₁.le hc₂.le hc₃.le hβ₁₂.le hβ₂₃.le htail
  have hord := complexMoments_of_positive_real_powers P Y hY hpos (Iio β₁) isOpen_Iio hmoment
  let r := inverseTailRemainder T c₁ c₂ β₁ β₂
  have hr : DifferentiableOn ℂ r {s : ℂ | s.re < β₃} :=
    differentiableOn_inverseTailRemainder P Y hY hpos hinv c₁ c₂ c₃ β₁ β₂ β₃ hc₃.le hβ₃.le htail
  have hsub : {s : ℂ | s.re < β₁} ⊆ {s : ℂ | s.re < β₃} :=
    fun _ hs => hs.trans (hβ₁₂.trans hβ₂₃)
  have hformula : EqOn (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) {s : ℂ | s.re < β₁} := by
    apply eqOn_realPart_lt_of_positive_real β₁ hβ₁ _ _ hord.2
      ((differentiableOn_twoTailRational_left c₁ c₂ β₁ β₂ hβ₁₂.le).add (hr.mono hsub))
    intro p hp hpβ
    have hre := inverseTailRemainder_eq_twoTailRemainder T hT hb c₁ c₂ β₁ β₂ (p : ℂ) hp
    change (∫ ω, (Y ω : ℂ) ^ (p : ℂ) ∂P) = twoTailRational c₁ c₂ β₁ β₂ (p : ℂ) +
      inverseTailRemainder T c₁ c₂ β₁ β₂ (p : ℂ)
    rw [hre, (complexMoment_real_eq_mellin_tail P Y hY (hpos.mono fun _ h => h.le) p hp
      (mellin_full_tail T hT hb (c₁ + c₂ + c₃) β₁ htop (p : ℂ) ⟨hp, hpβ⟩)).2]
    exact mellin_tail_decomposition T c₁ c₂ β₁ β₂ (p : ℂ) hpβ (hpβ.trans hβ₁₂)
      ((mellin_lowerTailKernel T hT hb).1 _ hp)
      ((mellin_upperTailErrorKernel T hT c₁ c₂ c₃ β₁ β₂ β₃ hc₃.le hβ₃.le htail).1 _
        (hpβ.trans (hβ₁₂.trans hβ₂₃)))
  refine ⟨hord.1, hord.2, r, hr,
    meromorphicOn_twoTailRational_add c₁ c₂ β₁ β₂ r _ (isOpen_realPart_lt β₃) hr,
    fun s hs => hformula hs, inverseTailRemainder_zero T c₁ c₂ β₁ β₂, ?_, ?_⟩
  · exact tendsto_twoTailRational_first c₁ c₂ β₁ β₂ hβ₁₂.ne r
      (hr.continuousOn.continuousAt ((isOpen_realPart_lt β₃).mem_nhds (hβ₁₂.trans hβ₂₃)))
  · exact tendsto_twoTailRational_second c₁ c₂ β₁ β₂ hβ₁₂.ne r
      (hr.continuousOn.continuousAt ((isOpen_realPart_lt β₃).mem_nhds hβ₂₃))

end DOZZ.Proofs
