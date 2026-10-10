/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftMassDeriv
public import DOZZ.FourPoint.BPZ.Rooting
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Bounds uniform in the softening and in the root

This file collects the deterministic and measure-theoretic bounds that are uniform in the
softening `ε` and in the position `z` of the degenerate root.

* Pointwise bounds on the derivatives of the softened distance factor `(|x − z|² + ε²)^a` for
  `0 < a ≤ 1`: uniformly in `ε` by the unsoftened powers `|x − z|^{2a−1}` and `|x − z|^{2a−2}`,
  and away from the root by multiples of the softened weight itself. The softened weight is
  monotone in the softening.
* The planar integral `∫_{B(c,R)} |x − c|^p = 2π R^{p+2}/(p+2)` of a power with an integrable
  singularity (`p > −2`), computed in polar coordinates.
* The near-root rooted estimate: for every nonnegative measurable `f`, uniformly in `‖z‖ ≤ R`
  and `0 ≤ ε ≤ 1`, the quantity `E[I_ε(z)^{-q} ∫ f dM]` is bounded by a constant times the
  Lebesgue integral `∫ f dx`. It combines the rooted bound, the uniform negative moments of the
  mass, and `σ ≤ Leb` for the reference measure `σ`. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Uniform pointwise bounds -/

/-- The softened base `|x − z|² + ε²` dominates `‖x − z‖²`. -/
theorem bpzSoft_norm_sq_le_base (ε : ℝ) (x z : ℂ) :
    ‖x - z‖ ^ 2 ≤ Complex.normSq (x - z) + ε ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg ε)

/-- For `a ≤ 1` and `x ≠ z` the power `N^{a-1}` of the softened base is bounded, uniformly in the
softening, by the unsoftened power `‖x − z‖^{2a−2}`. -/
theorem bpzSoft_rpow_pred_le_norm_rpow {a ε : ℝ} (ha1 : a ≤ 1) {x z : ℂ} (hxz : x ≠ z) :
    (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) ≤ ‖x - z‖ ^ (2 * a - 2) := by
  have hu : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have h1 : (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) ≤ (‖x - z‖ ^ 2) ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (bpzSoft_norm_sq_le_base ε x z) (by linarith)
  have h2 : (‖x - z‖ ^ 2) ^ (a - 1) = ‖x - z‖ ^ (2 * a - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    congr 1
    push_cast
    ring
  rw [← h2]
  exact h1

/-- The first derivative of the softened factor is bounded, uniformly in the softening, by
`2a ‖x − z‖^{2a−1}`. -/
theorem norm_bpzSoftDeriv_le_uniform {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {x z : ℂ}
    (hxz : x ≠ z) :
    ‖bpzSoftDeriv a ε x z‖ ≤ 2 * a * ‖x - z‖ ^ (2 * a - 1) := by
  have hu : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  refine (norm_bpzSoftDeriv_le a ε x z).trans ?_
  rw [abs_of_pos ha]
  have h := bpzSoft_rpow_pred_le_norm_rpow (ε := ε) ha1 hxz
  have hpow : ‖x - z‖ ^ (2 * a - 2) * ‖x - z‖ = ‖x - z‖ ^ (2 * a - 1) := by
    rw [← Real.rpow_add_one hu.ne']
    congr 1
    ring
  calc 2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) * ‖x - z‖
      ≤ 2 * a * ‖x - z‖ ^ (2 * a - 2) * ‖x - z‖ := by gcongr
    _ = 2 * a * ‖x - z‖ ^ (2 * a - 1) := by rw [mul_assoc, hpow]

/-- The second derivative of the softened factor is bounded, uniformly in the softening, by
`(4a(1−a) + 2a) ‖x − z‖^{2a−2}`. -/
theorem norm_bpzSoftDeriv2_le_uniform {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {x z : ℂ}
    (hxz : x ≠ z) :
    ‖bpzSoftDeriv2 a ε x z‖ ≤ (4 * a * (1 - a) + 2 * a) * ‖x - z‖ ^ (2 * a - 2) := by
  have hu : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hN : 0 < Complex.normSq (x - z) + ε ^ 2 :=
    lt_of_lt_of_le (by positivity) (bpzSoft_norm_sq_le_base ε x z)
  refine (norm_bpzSoftDeriv2_le a ε x z hN).trans ?_
  have habs : |a * (a - 1)| = a * (1 - a) := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith))]
    ring
  rw [habs, abs_of_pos ha]
  have h := bpzSoft_rpow_pred_le_norm_rpow (ε := ε) ha1 hxz
  have hc : 0 ≤ 4 * (a * (1 - a)) + 2 * a := by
    have : 0 ≤ a * (1 - a) := mul_nonneg ha.le (by linarith)
    positivity
  calc (4 * (a * (1 - a)) + 2 * a) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)
      ≤ (4 * (a * (1 - a)) + 2 * a) * ‖x - z‖ ^ (2 * a - 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = (4 * a * (1 - a) + 2 * a) * ‖x - z‖ ^ (2 * a - 2) := by ring

/-- Away from the root the first derivative is bounded by the softened weight itself. -/
theorem norm_bpzSoftDeriv_le_far {a ε r : ℝ} (ha : 0 < a) (hr : 0 < r) {x z : ℂ}
    (hxz : r ≤ ‖x - z‖) :
    ‖bpzSoftDeriv a ε x z‖ ≤ 2 * a / r * (Complex.normSq (x - z) + ε ^ 2) ^ a := by
  have hu0 : 0 < ‖x - z‖ := lt_of_lt_of_le hr hxz
  have hNu : ‖x - z‖ ^ 2 ≤ Complex.normSq (x - z) + ε ^ 2 := bpzSoft_norm_sq_le_base ε x z
  have hN0 : 0 < Complex.normSq (x - z) + ε ^ 2 := lt_of_lt_of_le (by positivity) hNu
  refine (norm_bpzSoftDeriv_le a ε x z).trans ?_
  rw [abs_of_pos ha, Real.rpow_sub_one hN0.ne']
  have hNa : 0 ≤ (Complex.normSq (x - z) + ε ^ 2) ^ a := Real.rpow_nonneg hN0.le a
  have key : ‖x - z‖ / (Complex.normSq (x - z) + ε ^ 2) ≤ 1 / r := by
    rw [div_le_div_iff₀ hN0 hr]
    nlinarith [mul_le_mul_of_nonneg_left hxz hu0.le]
  calc 2 * a * ((Complex.normSq (x - z) + ε ^ 2) ^ a / (Complex.normSq (x - z) + ε ^ 2)) *
        ‖x - z‖
      = 2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ a *
          (‖x - z‖ / (Complex.normSq (x - z) + ε ^ 2)) := by ring
    _ ≤ 2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ a * (1 / r) := by gcongr
    _ = 2 * a / r * (Complex.normSq (x - z) + ε ^ 2) ^ a := by ring

/-- Away from the root the second derivative is bounded by the softened weight itself. -/
theorem norm_bpzSoftDeriv2_le_far {a ε r : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 < r) {x z : ℂ}
    (hxz : r ≤ ‖x - z‖) :
    ‖bpzSoftDeriv2 a ε x z‖ ≤
      (4 * a * (1 - a) + 2 * a) / r ^ 2 * (Complex.normSq (x - z) + ε ^ 2) ^ a := by
  have hu0 : 0 < ‖x - z‖ := lt_of_lt_of_le hr hxz
  have hNu : ‖x - z‖ ^ 2 ≤ Complex.normSq (x - z) + ε ^ 2 := bpzSoft_norm_sq_le_base ε x z
  have hN0 : 0 < Complex.normSq (x - z) + ε ^ 2 := lt_of_lt_of_le (by positivity) hNu
  refine (norm_bpzSoftDeriv2_le a ε x z hN0).trans ?_
  have habs : |a * (a - 1)| = a * (1 - a) := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith))]
    ring
  rw [habs, abs_of_pos ha, Real.rpow_sub_one hN0.ne']
  have hc : 0 ≤ 4 * (a * (1 - a)) + 2 * a := by
    have : 0 ≤ a * (1 - a) := mul_nonneg ha.le (by linarith)
    positivity
  have hNa : 0 ≤ (Complex.normSq (x - z) + ε ^ 2) ^ a := Real.rpow_nonneg hN0.le a
  have hr2 : r ^ 2 ≤ Complex.normSq (x - z) + ε ^ 2 :=
    le_trans (pow_le_pow_left₀ hr.le hxz 2) hNu
  have key : 1 / (Complex.normSq (x - z) + ε ^ 2) ≤ 1 / r ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hr2
  calc (4 * (a * (1 - a)) + 2 * a) *
        ((Complex.normSq (x - z) + ε ^ 2) ^ a / (Complex.normSq (x - z) + ε ^ 2))
      = (4 * (a * (1 - a)) + 2 * a) * (Complex.normSq (x - z) + ε ^ 2) ^ a *
          (1 / (Complex.normSq (x - z) + ε ^ 2)) := by ring
    _ ≤ (4 * (a * (1 - a)) + 2 * a) * (Complex.normSq (x - z) + ε ^ 2) ^ a * (1 / r ^ 2) := by
        gcongr
    _ = (4 * a * (1 - a) + 2 * a) / r ^ 2 * (Complex.normSq (x - z) + ε ^ 2) ^ a := by ring


/-! ### The planar integral of a power near its singularity -/

/-- The radial integral `∫₀^R r^{p+1} dr = R^{p+2}/(p+2)` for `p > −2`, as a lower integral. -/
theorem bpz_lintegral_Ioo_rpow {p R : ℝ} (hp : -2 < p) (hR : 0 < R) :
    ∫⁻ r in Ioo 0 R, ENNReal.ofReal (r ^ (p + 1)) = ENNReal.ofReal (R ^ (p + 2) / (p + 2)) := by
  have hp1 : -1 < p + 1 := by linarith
  have hint : IntegrableOn (fun r : ℝ => r ^ (p + 1)) (Ioc 0 R) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hp1)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 R)] fun r : ℝ => r ^ (p + 1) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => Real.rpow_nonneg hr.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ioo_subset_Ioc_self) hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl hp1), show p + 1 + 1 = p + 2 by ring,
    Real.zero_rpow (by linarith : p + 2 ≠ 0), sub_zero]

/-- The planar integral of `‖x‖^p` over the disk `B(0,R)`, computed in polar coordinates. -/
theorem bpz_lintegral_ball_zero_rpow {p R : ℝ} (hp : -2 < p) (hR : 0 < R) :
    ∫⁻ x, (Metric.ball (0 : ℂ) R).indicator (fun y => ENNReal.ofReal (‖y‖ ^ p)) x =
      ENNReal.ofReal (2 * Real.pi * R ^ (p + 2) / (p + 2)) := by
  set F : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) R).indicator (fun y => ENNReal.ofReal (‖y‖ ^ p))
    with hF
  set g : ℝ → ℝ≥0∞ := (Ioo 0 R).indicator (fun r => ENNReal.ofReal (r ^ (p + 1))) with hg
  have hgm : Measurable g :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator measurableSet_Ioo
  have hpt : ∀ q ∈ Complex.polarCoord.target,
      ENNReal.ofReal q.1 • F (Complex.polarCoord.symm q) = g q.1 := by
    intro q hq
    have hq1 : 0 < q.1 := hq.1
    have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
    by_cases hqR : q.1 < R
    · have hmem : Complex.polarCoord.symm q ∈ Metric.ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff, hnorm]
        exact hqR
      have hmemI : q.1 ∈ Ioo 0 R := ⟨hq1, hqR⟩
      rw [hF, indicator_of_mem hmem, hg, indicator_of_mem hmemI, hnorm, smul_eq_mul,
        ← ENNReal.ofReal_mul hq1.le, mul_comm, ← Real.rpow_add_one hq1.ne']
    · have hmem : Complex.polarCoord.symm q ∉ Metric.ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff, hnorm]
        exact hqR
      rw [hF, indicator_of_notMem hmem, hg,
        indicator_of_notMem (fun h : q.1 ∈ Ioo 0 R => hqR h.2)]
      simp
  have hrad : ∫⁻ r in Ioi (0 : ℝ), g r = ENNReal.ofReal (R ^ (p + 2) / (p + 2)) := by
    rw [setLIntegral_eq_of_support_subset, hg, lintegral_indicator measurableSet_Ioo,
      bpz_lintegral_Ioo_rpow hp hR]
    intro r hr
    by_contra hri
    exact hr (indicator_of_notMem (fun h : r ∈ Ioo 0 R => hri h.1) _)
  calc ∫⁻ x, F x
      = ∫⁻ q in Complex.polarCoord.target, ENNReal.ofReal q.1 • F (Complex.polarCoord.symm q) :=
        (Complex.lintegral_comp_polarCoord_symm F).symm
    _ = ∫⁻ q in Complex.polarCoord.target, g q.1 :=
        setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet hpt
    _ = ∫⁻ q, g q.1 ∂((volume.restrict (Ioi (0 : ℝ))).prod
          (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
        rw [Complex.polarCoord_target, Measure.volume_eq_prod, Measure.prod_restrict]
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ _θ in Ioo (-Real.pi) Real.pi, g r :=
        lintegral_prod _ (hgm.comp measurable_fst).aemeasurable
    _ = (∫⁻ r in Ioi (0 : ℝ), g r) * ENNReal.ofReal (2 * Real.pi) := by
        simp_rw [setLIntegral_const, Real.volume_Ioo]
        rw [lintegral_mul_const _ hgm]
        congr 2
        ring
    _ = ENNReal.ofReal (2 * Real.pi * R ^ (p + 2) / (p + 2)) := by
        rw [hrad, ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hR.le _) (by linarith))]
        congr 1
        ring

/-- For `p > −2`, the planar integral of `‖x − c‖^p` over the disk `B(c, R)` is
`2π R^{p+2}/(p+2)`. -/
theorem bpz_lintegral_ball_rpow_eq {p R : ℝ} (hp : -2 < p) (hR : 0 < R) (c : ℂ) :
    ∫⁻ x in Metric.ball c R, ENNReal.ofReal (‖x - c‖ ^ p) =
      ENNReal.ofReal (2 * Real.pi * R ^ (p + 2) / (p + 2)) := by
  set F : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) R).indicator (fun y => ENNReal.ofReal (‖y‖ ^ p))
    with hF
  have h : ∫⁻ x in Metric.ball c R, ENNReal.ofReal (‖x - c‖ ^ p) = ∫⁻ x, F (x - c) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Metric.ball c R
    · have hx' : x - c ∈ Metric.ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      rw [indicator_of_mem hx, hF, indicator_of_mem hx']
    · have hx' : x - c ∉ Metric.ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      rw [indicator_of_notMem hx, hF, indicator_of_notMem hx']
  rw [h, lintegral_sub_right_eq_self F c]
  exact bpz_lintegral_ball_zero_rpow hp hR

/-- For `p > −2`, `∫⁻_{B(c, R)} ‖x − c‖^p ≤ 2π R^{p+2}/(p+2)` (Lebesgue measure on `ℂ`). -/
theorem bpz_lintegral_ball_rpow_le {p R : ℝ} (hp : -2 < p) (hR : 0 < R) (c : ℂ) :
    ∫⁻ x in Metric.ball c R, ENNReal.ofReal (‖x - c‖ ^ p) ≤
      ENNReal.ofReal (2 * Real.pi * R ^ (p + 2) / (p + 2)) :=
  (bpz_lintegral_ball_rpow_eq hp hR c).le

/-! ### The near-root rooted estimate -/

/-- The reference measure `σ(dx) = |x|₊^{-4} d²x` is dominated by Lebesgue measure. -/
theorem bpz_gmcReferenceMeasure_le_volume : gmcReferenceMeasure ≤ (volume : Measure ℂ) := by
  have h : gmcReferenceMeasure ≤ (volume : Measure ℂ).withDensity (1 : ℂ → ℝ≥0∞) := by
    refine withDensity_mono (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 1 ≤ normPlus x := le_max_left _ _
    have h2 : normPlus x ^ (-4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    calc ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h2
      _ = 1 := ENNReal.ofReal_one
  rwa [withDensity_one] at h

/-- The near-root rooted estimate, uniform in the root `‖z‖ ≤ R` and the softening
`0 ≤ ε ≤ 1`: for every nonnegative measurable `f`, `E[I_ε(z)^{-q} ∫ f dM]` is bounded by a
constant times the Lebesgue integral of `f`. -/
theorem bpz_near_root_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) {γ χ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {R q : ℝ} (hR : 0 ≤ R) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ f : ℂ → ℝ≥0∞, Measurable f →
        ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-q) * ∫⁻ x, f x ∂M ω ∂P ≤
          ENNReal.ofReal C * ∫⁻ x, f x ∂volume := by
  obtain ⟨B, hB, hBz⟩ := bpzMass_negMoment_uniform (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
    P X hX hγ hγ2 M hM R hR q hq
  refine ⟨(2 : ℝ) ^ (γ ^ 2 * q) * B.toReal, by positivity, ?_⟩
  intro z hz ε hε0 hε1 f hf
  have h1 := bpz_rooted_bound (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM ε q
    hq z f hf
  have h2 : ∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-q) ∂P ≤ B := hBz z hz ε hε0 hε1
  have h3 : ∫⁻ x, f x ∂gmcReferenceMeasure ≤ ∫⁻ x, f x ∂volume :=
    lintegral_mono' bpz_gmcReferenceMeasure_le_volume le_rfl
  calc _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q)) *
          (∫⁻ ω, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ^ (-q) ∂P) * ∫⁻ x, f x ∂gmcReferenceMeasure :=
        h1
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q)) * B * ∫⁻ x, f x ∂volume := by gcongr
    _ = ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 * q) * B.toReal) * ∫⁻ x, f x ∂volume := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hB.ne]

end DOZZ.Proofs
