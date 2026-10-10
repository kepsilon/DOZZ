/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftCalculus
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Differentiating the softened mass under the integral

For `a ε : ℝ` with `ε > 0`, a nonnegative measurable weight `w` and a measure `m` on `ℂ`, the
softened mass
`z ↦ ∫ (|x − z|² + ε²)^a w(x) dm(x)`
is twice differentiable (as a function of `z ∈ ℂ ≅ ℝ²`) as soon as it is finite at one point
`z₀`, with derivatives obtained by differentiating under the integral sign.

The key point is the comparison `N(z') ≤ 2 (1 + |z − z'|²/ε²) N(z)` between the softened bases
`N(z) = |x − z|² + ε²`, which gives the same integrability at every `z` and a dominating
function for the derivatives on the unit ball about `z₀`. The derivative bounds
`‖D_z N^a‖ ≤ (2|a|/ε) N^a` and `‖D_z² N^a‖ ≤ ((4|a(a−1)| + 2|a|)/ε²) N^a` (from `N ≥ ε²` and
`|x − z| ≤ N^{1/2}`) then show that the derivatives are also bounded by multiples of the mass. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- The softened mass `∫ (|x − z|² + ε²)^a w(x) dm(x)`. -/
noncomputable def bpzSoftMassReal (a ε : ℝ) (w : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ x, (Complex.normSq (x - z) + ε ^ 2) ^ a * w x ∂m

/-- The first derivative `∫ w(x) D_z (|x − z|² + ε²)^a dm(x)` of the softened mass, as a
continuous linear functional on `ℂ`. -/
noncomputable def bpzSoftMassDeriv (a ε : ℝ) (w : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  ∫ x, w x • bpzSoftDeriv a ε x z ∂m

/-- The second derivative `∫ w(x) D_z² (|x − z|² + ε²)^a dm(x)` of the softened mass, as a
continuous bilinear form on `ℂ`. -/
noncomputable def bpzSoftMassDeriv2 (a ε : ℝ) (w : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ∫ x, w x • bpzSoftDeriv2 a ε x z ∂m

/-! ### Instance shortcuts

Instance search for the second-level space `ℂ →L[ℝ] ℂ →L[ℝ] ℝ` of bilinear forms does not find
`ContinuousENorm`, `PseudoMetrizableSpace` or `NormSMulClass`: the nested search for the inner
space `ℂ →L[ℝ] ℝ` exceeds the default `maxSynthPendingDepth`. The following low-priority local
shortcuts (definitionally the generic instances) repair this without changing the instances used
to elaborate norms, integrals and the statements below. Only the private lemma
`bpzSoftMassDeriv2_integrable_integrand`, which states `Integrable` for a bilinear-form-valued
function, has a type that mentions them. -/

noncomputable local instance (priority := low) bpzNormedAddCommGroupBilin :
    NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := inferInstance

noncomputable local instance (priority := low) bpzNormedSpaceBilin :
    NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := inferInstance

/-! ### Comparison of softened bases at two parameters -/

/-- The softened base `|x − z|² + ε²` is positive when `ε > 0`. -/
theorem bpzSoft_base_pos {ε : ℝ} (hε : 0 < ε) (x z : ℂ) :
    0 < Complex.normSq (x - z) + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (pow_pos hε 2)

/-- Comparison of the softened bases at two parameters `z, z'`. -/
theorem bpzSoft_comp_le {ε : ℝ} (hε : 0 < ε) (z z' x : ℂ) :
    Complex.normSq (x - z') + ε ^ 2 ≤
      2 * (1 + ‖z - z'‖ ^ 2 / ε ^ 2) * (Complex.normSq (x - z) + ε ^ 2) := by
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have htri : ‖x - z'‖ ≤ ‖x - z‖ + ‖z - z'‖ := by
    calc ‖x - z'‖ = ‖(x - z) + (z - z')‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - z‖ + ‖z - z'‖ := norm_add_le _ _
  have hsq : ‖x - z'‖ ^ 2 ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖z - z'‖ ^ 2 := by
    nlinarith [norm_nonneg (x - z'), norm_nonneg (x - z), norm_nonneg (z - z'),
      sq_nonneg (‖x - z‖ - ‖z - z'‖)]
  set q : ℝ := ‖z - z'‖ ^ 2 / ε ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hDq : ‖z - z'‖ ^ 2 = q * ε ^ 2 := by rw [hq]; field_simp
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [hDq] at hsq
  nlinarith [mul_nonneg hq0 (sq_nonneg ‖x - z‖)]

/-- For `‖z − z'‖ ≤ 1` the softened bases at `z` and `z'` are comparable with the constant
`2 (1 + 1/ε²)`. -/
theorem bpzSoft_ratio_le {ε : ℝ} (hε : 0 < ε) {z z' : ℂ} (hzz : ‖z - z'‖ ≤ 1) (x : ℂ) :
    Complex.normSq (x - z') + ε ^ 2 ≤
      2 * (1 + 1 / ε ^ 2) * (Complex.normSq (x - z) + ε ^ 2) := by
  refine (bpzSoft_comp_le hε z z' x).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (bpzSoft_base_pos hε x z).le
  have h1 : ‖z - z'‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hzz
  have h2 : ‖z - z'‖ ^ 2 / ε ^ 2 ≤ 1 / ε ^ 2 :=
    div_le_div_of_nonneg_right h1 (pow_pos hε 2).le
  linarith

/-- A two-sided multiplicative comparison of positive reals gives one for every real power. -/
theorem bpzSoft_rpow_le_aux {P Q C : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hC : 0 < C)
    (h1 : P ≤ C * Q) (h2 : Q ≤ C * P) (a : ℝ) : P ^ a ≤ C ^ |a| * Q ^ a := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    calc P ^ a ≤ (C * Q) ^ a := Real.rpow_le_rpow hP.le h1 ha
      _ = C ^ a * Q ^ a := Real.mul_rpow hC.le hQ.le
  · rw [abs_of_nonpos ha]
    have h3 : Q / C ≤ P := by
      rw [div_le_iff₀ hC]
      linarith [mul_comm C P]
    calc P ^ a ≤ (Q / C) ^ a := Real.rpow_le_rpow_of_nonpos (div_pos hQ hC) h3 ha
      _ = Q ^ a / C ^ a := Real.div_rpow hQ.le hC.le a
      _ = C ^ (-a) * Q ^ a := by rw [Real.rpow_neg hC.le]; ring

/-- Comparison of the `a`-th powers of the softened bases at two parameters `z, z'`. -/
theorem bpzSoft_rpow_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) (z z' x : ℂ) :
    (Complex.normSq (x - z') + ε ^ 2) ^ a ≤
      (2 * (1 + ‖z - z'‖ ^ 2 / ε ^ 2)) ^ |a| * (Complex.normSq (x - z) + ε ^ 2) ^ a := by
  refine bpzSoft_rpow_le_aux (bpzSoft_base_pos hε x z') (bpzSoft_base_pos hε x z)
    (by positivity) (bpzSoft_comp_le hε z z' x) ?_ a
  have h := bpzSoft_comp_le hε z' z x
  rwa [norm_sub_rev z' z] at h

/-- For `‖z − z'‖ ≤ 1`: `N(z')^a ≤ (2 (1 + 1/ε²))^|a| N(z)^a` for every real `a`. -/
theorem bpzSoft_rpow_le_of_norm_le_one {ε : ℝ} (hε : 0 < ε) (a : ℝ) {z z' : ℂ}
    (hzz : ‖z - z'‖ ≤ 1) (x : ℂ) :
    (Complex.normSq (x - z') + ε ^ 2) ^ a ≤
      (2 * (1 + 1 / ε ^ 2)) ^ |a| * (Complex.normSq (x - z) + ε ^ 2) ^ a := by
  refine bpzSoft_rpow_le_aux (bpzSoft_base_pos hε x z') (bpzSoft_base_pos hε x z)
    (by positivity) (bpzSoft_ratio_le hε hzz x) ?_ a
  have hzz' : ‖z' - z‖ ≤ 1 := by rwa [norm_sub_rev]
  exact bpzSoft_ratio_le hε hzz' x

/-! ### Pointwise bounds by `N^a` -/

/-- `N^{a-1} |u| ≤ N^a / ε` for `N = |u|² + ε²`. -/
theorem bpzSoft_rpow_pred_mul_norm_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) (u : ℂ) :
    (Complex.normSq u + ε ^ 2) ^ (a - 1) * ‖u‖ ≤ (Complex.normSq u + ε ^ 2) ^ a / ε := by
  have hN : 0 < Complex.normSq u + ε ^ 2 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
    (pow_pos hε 2)
  have hu : ‖u‖ * ε ≤ Complex.normSq u + ε ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖u‖ - ε), sq_nonneg ‖u‖, sq_nonneg ε]
  rw [Real.rpow_sub_one hN.ne', div_mul_eq_mul_div, div_le_div_iff₀ hN hε]
  calc (Complex.normSq u + ε ^ 2) ^ a * ‖u‖ * ε
      = (Complex.normSq u + ε ^ 2) ^ a * (‖u‖ * ε) := by ring
    _ ≤ (Complex.normSq u + ε ^ 2) ^ a * (Complex.normSq u + ε ^ 2) :=
      mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hN.le a)

/-- `N^{a-1} ≤ N^a / ε²` for `N = |u|² + ε²`. -/
theorem bpzSoft_rpow_pred_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) (u : ℂ) :
    (Complex.normSq u + ε ^ 2) ^ (a - 1) ≤ (Complex.normSq u + ε ^ 2) ^ a / ε ^ 2 := by
  have hN : 0 < Complex.normSq u + ε ^ 2 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
    (pow_pos hε 2)
  rw [Real.rpow_sub_one hN.ne']
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN.le a) (pow_pos hε 2)
    (le_add_of_nonneg_left (Complex.normSq_nonneg u))

/-- The first derivative is bounded by `(2|a|/ε) N^a`. -/
theorem bpzSoftDeriv_norm_le_rpow (a : ℝ) {ε : ℝ} (hε : 0 < ε) (x z : ℂ) :
    ‖bpzSoftDeriv a ε x z‖ ≤ 2 * |a| / ε * (Complex.normSq (x - z) + ε ^ 2) ^ a := by
  refine (norm_bpzSoftDeriv_le a ε x z).trans ?_
  have h := bpzSoft_rpow_pred_mul_norm_le hε a (x - z)
  calc 2 * |a| * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) * ‖x - z‖
      = 2 * |a| * ((Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) * ‖x - z‖) := by ring
    _ ≤ 2 * |a| * ((Complex.normSq (x - z) + ε ^ 2) ^ a / ε) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * |a| / ε * (Complex.normSq (x - z) + ε ^ 2) ^ a := by ring

/-- The second derivative is bounded by `((4|a(a−1)| + 2|a|)/ε²) N^a`. -/
theorem bpzSoftDeriv2_norm_le_rpow (a : ℝ) {ε : ℝ} (hε : 0 < ε) (x z : ℂ) :
    ‖bpzSoftDeriv2 a ε x z‖ ≤
      (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * (Complex.normSq (x - z) + ε ^ 2) ^ a := by
  refine (norm_bpzSoftDeriv2_le a ε x z (bpzSoft_base_pos hε x z)).trans ?_
  calc (4 * |a * (a - 1)| + 2 * |a|) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)
      ≤ (4 * |a * (a - 1)| + 2 * |a|) * ((Complex.normSq (x - z) + ε ^ 2) ^ a / ε ^ 2) :=
        mul_le_mul_of_nonneg_left (bpzSoft_rpow_pred_le hε a (x - z)) (by positivity)
    _ = (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * (Complex.normSq (x - z) + ε ^ 2) ^ a := by ring

/-! ### Measurability and continuity in `x` -/

/-- Measurability of the softened power in `x`. -/
theorem bpzSoft_measurable_rpow (a ε : ℝ) (z : ℂ) :
    Measurable (fun x : ℂ => (Complex.normSq (x - z) + ε ^ 2) ^ a) := by
  have h : Measurable (fun x : ℂ => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  exact h.pow_const a

/-- Continuity of the first derivative in the integration variable `x`. -/
theorem bpzSoftDeriv_continuous_left (a : ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Continuous (fun x : ℂ => bpzSoftDeriv a ε x z) := by
  have hbase : Continuous (fun x : ℂ => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  have hc : Continuous
      (fun x : ℂ => -2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)) :=
    continuous_const.mul (hbase.rpow_const fun x => Or.inl (bpzSoft_base_pos hε x z).ne')
  have hL : Continuous (fun x : ℂ => innerSL ℝ (x - z)) :=
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  exact hc.smul hL

/-- Continuity of the second derivative in the integration variable `x`. -/
theorem bpzSoftDeriv2_continuous_left (a : ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Continuous (fun x : ℂ => bpzSoftDeriv2 a ε x z) := by
  have hbase : Continuous (fun x : ℂ => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  have hc2 : Continuous
      (fun x : ℂ => 4 * a * (a - 1) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 2)) :=
    continuous_const.mul (hbase.rpow_const fun x => Or.inl (bpzSoft_base_pos hε x z).ne')
  have hc1 : Continuous
      (fun x : ℂ => 2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)) :=
    continuous_const.mul (hbase.rpow_const fun x => Or.inl (bpzSoft_base_pos hε x z).ne')
  have hL : Continuous (fun x : ℂ => innerSL ℝ (x - z)) :=
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  have hS : Continuous
      (fun x : ℂ => (innerSL ℝ (x - z)).smulRight (innerSL ℝ (x - z))) :=
    (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] ℝ)).continuous₂.comp₂ hL hL
  exact (hc2.smul hS).add (hc1.smul continuous_const)

/-! ### Integrability -/

/-- If the softened mass is finite at one point `z₀`, it is finite at every point. -/
theorem integrable_bpzSoftMass_of {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    ∀ z, Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m := by
  intro z
  refine Integrable.mono' (hint.const_mul ((2 * (1 + ‖z₀ - z‖ ^ 2 / ε ^ 2)) ^ |a|)) ?_ ?_
  · exact ((bpzSoft_measurable_rpow a ε z).mul hw).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hnn : 0 ≤ (Complex.normSq (x - z) + ε ^ 2) ^ a * w x :=
      mul_nonneg (Real.rpow_nonneg (bpzSoft_base_pos hε x z).le a) (hw0 x)
    rw [Real.norm_of_nonneg hnn, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (bpzSoft_rpow_le hε a z₀ z x) (hw0 x)

/-- Pointwise bound for the first-derivative integrand at the same point. -/
theorem bpzSoftDeriv_norm_smul_le_self {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (x z : ℂ) :
    ‖w x • bpzSoftDeriv a ε x z‖ ≤
      2 * |a| / ε * ((Complex.normSq (x - z) + ε ^ 2) ^ a * w x) := by
  rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  calc w x * ‖bpzSoftDeriv a ε x z‖
      ≤ w x * (2 * |a| / ε * (Complex.normSq (x - z) + ε ^ 2) ^ a) :=
        mul_le_mul_of_nonneg_left (bpzSoftDeriv_norm_le_rpow a hε x z) (hw0 x)
    _ = 2 * |a| / ε * ((Complex.normSq (x - z) + ε ^ 2) ^ a * w x) := by ring

/-- Pointwise bound for the second-derivative integrand at the same point. -/
theorem bpzSoftDeriv2_norm_smul_le_self {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (x z : ℂ) :
    ‖w x • bpzSoftDeriv2 a ε x z‖ ≤
      (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 *
        ((Complex.normSq (x - z) + ε ^ 2) ^ a * w x) := by
  rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  calc w x * ‖bpzSoftDeriv2 a ε x z‖
      ≤ w x * ((4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 *
          (Complex.normSq (x - z) + ε ^ 2) ^ a) :=
        mul_le_mul_of_nonneg_left (bpzSoftDeriv2_norm_le_rpow a hε x z) (hw0 x)
    _ = (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 *
        ((Complex.normSq (x - z) + ε ^ 2) ^ a * w x) := by ring

/-- Domination of the first-derivative integrand for `‖z₀ − z‖ ≤ 1`. -/
theorem bpzSoftDeriv_norm_smul_le {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) {z₀ z : ℂ} (hz : ‖z₀ - z‖ ≤ 1) (x : ℂ) :
    ‖w x • bpzSoftDeriv a ε x z‖ ≤
      2 * |a| / ε * (2 * (1 + 1 / ε ^ 2)) ^ |a| *
        ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) := by
  refine (bpzSoftDeriv_norm_smul_le_self hε hw0 x z).trans ?_
  have h := mul_le_mul_of_nonneg_right (bpzSoft_rpow_le_of_norm_le_one hε a hz x) (hw0 x)
  calc 2 * |a| / ε * ((Complex.normSq (x - z) + ε ^ 2) ^ a * w x)
      ≤ 2 * |a| / ε * ((2 * (1 + 1 / ε ^ 2)) ^ |a| *
          (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * |a| / ε * (2 * (1 + 1 / ε ^ 2)) ^ |a| *
        ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) := by ring

/-- Domination of the second-derivative integrand for `‖z₀ − z‖ ≤ 1`. -/
theorem bpzSoftDeriv2_norm_smul_le {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) {z₀ z : ℂ} (hz : ‖z₀ - z‖ ≤ 1) (x : ℂ) :
    ‖w x • bpzSoftDeriv2 a ε x z‖ ≤
      (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * (2 * (1 + 1 / ε ^ 2)) ^ |a| *
        ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) := by
  refine (bpzSoftDeriv2_norm_smul_le_self hε hw0 x z).trans ?_
  have h := mul_le_mul_of_nonneg_right (bpzSoft_rpow_le_of_norm_le_one hε a hz x) (hw0 x)
  calc (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 *
        ((Complex.normSq (x - z) + ε ^ 2) ^ a * w x)
      ≤ (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * ((2 * (1 + 1 / ε ^ 2)) ^ |a| *
          (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * (2 * (1 + 1 / ε ^ 2)) ^ |a| *
        ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) := by ring

/-- The first-derivative integrand is integrable. -/
theorem bpzSoftMassDeriv_integrable_integrand {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    Integrable (fun x => w x • bpzSoftDeriv a ε x z₀) m := by
  refine Integrable.mono' (hint.const_mul (2 * |a| / ε)) ?_
    (Eventually.of_forall fun x => bpzSoftDeriv_norm_smul_le_self hε hw0 x z₀)
  exact hw.aestronglyMeasurable.smul (bpzSoftDeriv_continuous_left a hε z₀).aestronglyMeasurable

/-- The second-derivative integrand is integrable. (Private: its statement involves the local
instance shortcuts above.) -/
private theorem bpzSoftMassDeriv2_integrable_integrand {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    Integrable (fun x => w x • bpzSoftDeriv2 a ε x z₀) m := by
  refine Integrable.mono' (hint.const_mul ((4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2)) ?_
    (Eventually.of_forall fun x => bpzSoftDeriv2_norm_smul_le_self hε hw0 x z₀)
  exact hw.aestronglyMeasurable.smul (bpzSoftDeriv2_continuous_left a hε z₀).aestronglyMeasurable

/-! ### Differentiation under the integral sign -/

/-- The softened mass is differentiable, with derivative `bpzSoftMassDeriv`. -/
theorem hasFDerivAt_bpzSoftMassReal {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    HasFDerivAt (bpzSoftMassReal a ε w m) (bpzSoftMassDeriv a ε w m z₀) z₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := m)
    (F := fun z x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x)
    (F' := fun z x => w x • bpzSoftDeriv a ε x z)
    (bound := fun x => 2 * |a| / ε * (2 * (1 + 1 / ε ^ 2)) ^ |a| *
      ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x))
    (Metric.ball_mem_nhds z₀ one_pos) ?_ hint ?_ ?_ (hint.const_mul _) ?_
  · exact Eventually.of_forall fun z =>
      ((bpzSoft_measurable_rpow a ε z).mul hw).aestronglyMeasurable
  · exact hw.aestronglyMeasurable.smul (bpzSoftDeriv_continuous_left a hε z₀).aestronglyMeasurable
  · refine Eventually.of_forall fun x z hz => ?_
    rw [Metric.mem_ball', dist_eq_norm] at hz
    exact bpzSoftDeriv_norm_smul_le hε hw0 hz.le x
  · refine Eventually.of_forall fun x z _ => ?_
    exact (hasFDerivAt_bpzSoft a ε x z (bpzSoft_base_pos hε x z)).mul_const (w x)

/-- The first derivative of the softened mass is differentiable, with derivative
`bpzSoftMassDeriv2`. -/
theorem hasFDerivAt_bpzSoftMassDeriv {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    HasFDerivAt (bpzSoftMassDeriv a ε w m) (bpzSoftMassDeriv2 a ε w m z₀) z₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := m)
    (F := fun z x => w x • bpzSoftDeriv a ε x z)
    (F' := fun z x => w x • bpzSoftDeriv2 a ε x z)
    (bound := fun x => (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * (2 * (1 + 1 / ε ^ 2)) ^ |a| *
      ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x))
    (Metric.ball_mem_nhds z₀ one_pos) ?_ ?_ ?_ ?_ (hint.const_mul _) ?_
  · exact Eventually.of_forall fun z =>
      hw.aestronglyMeasurable.smul (bpzSoftDeriv_continuous_left a hε z).aestronglyMeasurable
  · exact bpzSoftMassDeriv_integrable_integrand hε hw hw0 hint
  · exact hw.aestronglyMeasurable.smul (bpzSoftDeriv2_continuous_left a hε z₀).aestronglyMeasurable
  · refine Eventually.of_forall fun x z hz => ?_
    rw [Metric.mem_ball', dist_eq_norm] at hz
    exact bpzSoftDeriv2_norm_smul_le hε hw0 hz.le x
  · refine Eventually.of_forall fun x z _ => ?_
    exact (hasFDerivAt_bpzSoftDeriv a ε x z (bpzSoft_base_pos hε x z)).const_smul (w x)

/-! ### Bounds on the derivatives of the mass -/

/-- The first derivative of the softened mass is bounded by `(2|a|/ε)` times the mass. -/
theorem norm_bpzSoftMassDeriv_le {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    ‖bpzSoftMassDeriv a ε w m z₀‖ ≤ 2 * |a| / ε * bpzSoftMassReal a ε w m z₀ := by
  have hI := bpzSoftMassDeriv_integrable_integrand hε hw hw0 hint
  have hg := hint.const_mul (2 * |a| / ε)
  calc ‖bpzSoftMassDeriv a ε w m z₀‖
      = ‖∫ x, w x • bpzSoftDeriv a ε x z₀ ∂m‖ := rfl
    _ ≤ ∫ x, ‖w x • bpzSoftDeriv a ε x z₀‖ ∂m := norm_integral_le_integral_norm _
    _ ≤ ∫ x, 2 * |a| / ε * ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) ∂m :=
        integral_mono hI.norm hg fun x => bpzSoftDeriv_norm_smul_le_self hε hw0 x z₀
    _ = 2 * |a| / ε * bpzSoftMassReal a ε w m z₀ := integral_const_mul _ _

/-- The second derivative of the softened mass is bounded by `(4|a(a−1)| + 2|a|)/ε²` times the
mass. -/
theorem norm_bpzSoftMassDeriv2_le {a ε : ℝ} (hε : 0 < ε) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) m) :
    ‖bpzSoftMassDeriv2 a ε w m z₀‖ ≤
      (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * bpzSoftMassReal a ε w m z₀ := by
  have hI := bpzSoftMassDeriv2_integrable_integrand hε hw hw0 hint
  have hg := hint.const_mul ((4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2)
  calc ‖bpzSoftMassDeriv2 a ε w m z₀‖
      = ‖∫ x, w x • bpzSoftDeriv2 a ε x z₀ ∂m‖ := rfl
    _ ≤ ∫ x, ‖w x • bpzSoftDeriv2 a ε x z₀‖ ∂m := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 *
          ((Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) ∂m :=
        integral_mono hI.norm hg fun x => bpzSoftDeriv2_norm_smul_le_self hε hw0 x z₀
    _ = (4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2 * bpzSoftMassReal a ε w m z₀ :=
        integral_const_mul _ _

/-! ### The derivatives in coordinates -/



end DOZZ.Proofs
