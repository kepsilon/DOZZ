/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.Mass
public import DOZZ.GMC.Construction.RootedIdentity

/-! # Rooted bounds for the degenerate four-point mass

The equator Green kernel satisfies `G(u,x) ≥ -log 2` for all points, so the rooted measure
`e^{γ²G(u,·)} M` dominates `2^{-γ²} M`. Combined with the rooted identity this bounds
`E[I^{-q} ∫ f dM]` by `2^{γ²q} E[I^{-q}] ∫ f dσ` for every nonnegative `f`, where `σ` is the
reference measure. No fusion estimate is needed: rooting only increases the mass. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The equator Green kernel is bounded below by `-log 2`. -/
theorem gffKernel_ge_neg_log_two (u x : ℂ) : -Real.log 2 ≤ gffKernel u x := by
  unfold gffKernel
  have hu := bpz_one_le_normPlus u
  have hx := bpz_one_le_normPlus x
  have hu0 : 0 < normPlus u := bpz_normPlus_pos u
  have hx0 : 0 < normPlus x := bpz_normPlus_pos x
  rcases eq_or_ne u x with h | h
  · subst h
    simp only [sub_self, norm_zero, Real.log_zero, neg_zero, zero_add]
    have h1 := Real.log_nonneg hu
    have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  · have hpos : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    have hle : ‖u - x‖ ≤ 2 * (normPlus u * normPlus x) := by
      have h1 : ‖u‖ ≤ normPlus u := le_max_right _ _
      have h2 : ‖x‖ ≤ normPlus x := le_max_right _ _
      have h3 := norm_sub_le u x
      nlinarith
    have hlog := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hu0.ne' hx0.ne'] at hlog
    linarith

/-- The density of the rooted measure is measurable. -/
theorem measurable_gmcRootedDensity (u : ℂ) :
    Measurable fun x : ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) := by
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  refine Measurable.const_mul ?_ _
  unfold gffKernel
  exact (((measurable_const.sub measurable_id).norm.log.neg).add
    (measurable_const : Measurable fun _ : ℂ => Real.log (normPlus u))).add
    (Real.measurable_log.comp bpz_measurable_normPlus)

/-- The rooted measure dominates `2^{-γ²}` times the measure. -/
theorem lintegral_le_lintegral_gmcRootedMeasure (u : ℂ) (m : Measure ℂ) (g : ℂ → ℝ≥0∞)
    (hg : Measurable g) :
    ENNReal.ofReal ((2 : ℝ) ^ (-γ ^ 2)) * ∫⁻ x, g x ∂m ≤
      ∫⁻ x, g x ∂gmcRootedMeasure γ u m := by
  rw [gmcRootedMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gmcRootedDensity u) hg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  simp only [Pi.mul_apply]
  gcongr
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have := gffKernel_ge_neg_log_two u x
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- A lower bound by a positive multiple transfers to nonpositive powers, including the case of
an infinite lower bound. -/
theorem bpz_rpow_neg_le_of_le' {a b : ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (hab : ENNReal.ofReal c * b ≤ a) (q : ℝ) (hq : 0 ≤ q) :
    a ^ (-q) ≤ ENNReal.ofReal (c ^ (-q)) * b ^ (-q) := by
  rcases eq_or_ne b ⊤ with hb | hb
  · rcases hq.eq_or_lt with hq0 | hq0
    · subst hq0
      simp
    · have ha : a = ⊤ := by
        rw [hb, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at hab
        exact top_le_iff.mp hab
      rw [ha, ENNReal.top_rpow_of_neg (by linarith)]
      exact zero_le
  · exact bpz_rpow_neg_le_of_le hc hb hab q hq

/-- The rooted mass dominates `2^{-γ²}` times the mass. -/
theorem bpzMass_le_rooted (ε : ℝ) (u : ℂ) (m : Measure ℂ) (z : ℂ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-γ ^ 2)) * bpzMass γ χ α₁ α₂ α₃ ε m z ≤
      bpzMass γ χ α₁ α₂ α₃ ε (gmcRootedMeasure γ u m) z :=
  lintegral_le_lintegral_gmcRootedMeasure u m _
    (ENNReal.measurable_ofReal.comp (measurable_bpzSoftWeight ε z))

/-- The rooted bound: a negative power of the mass against a chaos integral is controlled by the
same reference-measure integral, with the constant `2^{γ²q} E[I^{-q}]`. -/
theorem bpz_rooted_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ε q : ℝ) (hq : 0 ≤ q) (z : ℂ) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-q) * ∫⁻ x, f x ∂M ω ∂P ≤
      ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q)) *
        (∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-q) ∂P) *
          ∫⁻ x, f x ∂gmcReferenceMeasure := by
  set F : Measure ℂ → ℝ≥0∞ := fun m => bpzMass γ χ α₁ α₂ α₃ ε m z ^ (-q) with hF
  have hFm : Measurable F :=
    (ENNReal.continuous_rpow_const.measurable).comp (measurable_bpzMass_measure ε z)
  have hH : Measurable (fun p : ℂ × ((TestFn → ℝ) × Measure ℂ) => f p.1 * F p.2.2) :=
    (hf.comp measurable_fst).mul (hFm.comp (measurable_snd.comp measurable_snd))
  have hid := equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM
    (fun u _ m => f u * F m) hH
  have hmeasI : AEMeasurable (fun ω => F (M ω)) P := by
    have := gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM
      (fun x => ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ ε z x))
      (ENNReal.measurable_ofReal.comp (measurable_bpzSoftWeight ε z))
    exact this.pow_const _
  have hlhs : ∫⁻ ω, F (M ω) * ∫⁻ x, f x ∂M ω ∂P =
      ∫⁻ ω, ∫⁻ u, f u * F (M ω) ∂M ω ∂P := by
    apply lintegral_congr
    intro ω
    rw [lintegral_mul_const _ hf, mul_comm]
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-γ ^ 2) := by positivity
  have hpt : ∀ u ω, F (gmcRootedMeasure γ u (M ω)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q)) * F (M ω) := by
    intro u ω
    have h := bpz_rpow_neg_le_of_le' hc (bpzMass_le_rooted (γ := γ) (χ := χ) (α₁ := α₁)
      (α₂ := α₂) (α₃ := α₃) ε u (M ω) z) q hq
    have hpow : ((2 : ℝ) ^ (-γ ^ 2)) ^ (-q) = (2 : ℝ) ^ (γ ^ 2 * q) := by
      rw [← Real.rpow_mul (by norm_num)]
      ring_nf
    rw [hpow] at h
    exact h
  change ∫⁻ ω, F (M ω) * ∫⁻ x, f x ∂M ω ∂P ≤ _
  rw [hlhs, hid]
  calc ∫⁻ u, ∫⁻ ω, f u * F (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure
      ≤ ∫⁻ u, ∫⁻ ω, f u * (ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q)) * F (M ω)) ∂P
          ∂gmcReferenceMeasure := by
        apply lintegral_mono
        intro u
        apply lintegral_mono
        intro ω
        exact mul_le_mul_right (hpt u ω) _
    _ = ∫⁻ u, f u * (ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q)) * ∫⁻ ω, F (M ω) ∂P)
          ∂gmcReferenceMeasure := by
        apply lintegral_congr
        intro u
        rw [lintegral_const_mul'' _ (hmeasI.const_mul _), lintegral_const_mul'' _ hmeasI]
    _ = _ := by
        rw [lintegral_mul_const _ hf, mul_comm]

end DOZZ.Proofs
