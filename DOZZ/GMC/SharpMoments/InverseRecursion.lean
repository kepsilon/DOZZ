/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.LaplaceScaling
public import DOZZ.GMC.SharpMoments.GaussianSplit
public import DOZZ.GMC.GaussianTailBound

/-! # The two-branch small-deviation recursion at finite cutoff

The reference disk `D = B(0, 1/8)` contains the two separated subdisks `D₁ = B(-1/16, 1/32)` and
`D₂ = B(1/16, 1/32)`. A Kahane comparison with two independent copies of the field on the two
subdisks and a common Gaussian scalar bounds the Laplace transform of the reference mass by a
Gaussian average of the product of the two subdisk Laplace transforms (the *two-branch
inequality*). Exact scaling turns each subdisk transform into a Gaussian average of the reference
transform at the cutoff `r - log 4`, and splitting off Gaussian lower tails gives the quadratic
recursion
`L_r(x) ≤ A e^{-c x²} + (1 + ε) L_{r - log 4}(3x/4 + a)²`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Center of the left subdisk. -/
noncomputable def invSubCenterLeft : ℂ := ((-(1 / 16) : ℝ) : ℂ)

/-- Center of the right subdisk. -/
noncomputable def invSubCenterRight : ℂ := (((1 / 16) : ℝ) : ℂ)

theorem norm_invSubCenterLeft : ‖invSubCenterLeft‖ = 1 / 16 := by
  rw [invSubCenterLeft, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem norm_invSubCenterRight : ‖invSubCenterRight‖ = 1 / 16 := by
  rw [invSubCenterRight, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- The Gaussian lower tail of a scaled centered Gaussian, in real form. -/
theorem gaussianReal_scaled_lower_tail_toReal (v : ℝ≥0) (hv : 0 < v) (γ u : ℝ)
    (hγ : 0 < γ) (hu : 0 ≤ u) :
    (gaussianReal 0 v {ξ | γ * ξ < -u}).toReal ≤ Real.exp (-u ^ 2 / (2 * γ ^ 2 * v)) := by
  have hset : {ξ : ℝ | γ * ξ < -u} = Set.Iio (-u / γ) := by
    ext ξ
    change γ * ξ < -u ↔ ξ < -u / γ
    rw [lt_div_iff₀ hγ]
    constructor <;> intro h <;> linarith
  rw [hset]
  have hb : -u / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
  have h := gaussianReal_lower_tail_bound v (-u / γ) hv hb
  have heq : -(-u / γ) ^ 2 / (2 * (v : ℝ)) = -u ^ 2 / (2 * γ ^ 2 * v) := by
    field_simp
  rw [heq] at h
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le h

/-- The subdisk Laplace transform is a Gaussian average of the reference transform at the
coarser cutoff `r - log 4`. -/
theorem cutoffLaplace_invSubdisk_scaling
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (a : ℂ) (ha : ‖a‖ = 1 / 16) (r : ℝ) (hr : Real.log 4 + 1 ≤ r) (y : ℝ) :
    cutoffLaplace P Xc γ r (Metric.ball a (1 / 4 * (1 / 8))) y =
      ∫ w, cutoffLaplace P Xc γ (r - Real.log 4) (Metric.ball 0 (1 / 8))
        (y + 2 * Real.log (1 / 4) + γ ^ 2 / 2 * Real.log (1 / 4) + γ * w)
        ∂gaussianReal 0 ⟨-Real.log (1 / 4),
          neg_nonneg.mpr (Real.log_nonpos (by norm_num) (by norm_num))⟩ := by
  have hlog : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  have hr' : 1 ≤ r - Real.log 4 := by linarith
  have hexp : Real.exp (-(r - Real.log 4)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(r - Real.log 4)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  have hexp2 : Real.exp (-r) ≤ 1 / 2 := by
    have : Real.exp (-r) ≤ Real.exp (-(r - Real.log 4)) :=
      Real.exp_le_exp.mpr (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)])
    linarith
  have hsource : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) (1 / 8)},
      ‖x.1‖ + Real.exp (-(r - Real.log 4)) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ 1 / 8 := by simpa using x.2
    linarith
  have htarget : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) (1 / 8)},
      ‖a + (1 / 4 : ℝ) • x.1‖ + Real.exp (-(r - Real.log 4 - Real.log (1 / 4))) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ 1 / 8 := by simpa using x.2
    have hcut : r - Real.log 4 - Real.log (1 / 4) = r := by rw [hlog]; ring
    rw [hcut]
    have hnorm : ‖a + (1 / 4 : ℝ) • x.1‖ ≤ 1 / 16 + 1 / 4 * (1 / 8) := by
      calc ‖a + (1 / 4 : ℝ) • x.1‖ ≤ ‖a‖ + ‖(1 / 4 : ℝ) • x.1‖ := norm_add_le _ _
        _ = ‖a‖ + 1 / 4 * ‖x.1‖ := by rw [norm_smul, Real.norm_eq_abs]; norm_num
        _ ≤ 1 / 16 + 1 / 4 * (1 / 8) := by rw [ha]; linarith
    linarith
  have h := cutoffLaplace_affine_ball_scaling P X hX γ Xc hXc (a := a) (c := 1 / 4)
    (R := 1 / 8) (r := r - Real.log 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [ha]; norm_num) hsource htarget y
  have hcut : r - Real.log 4 - Real.log (1 / 4) = r := by rw [hlog]; ring
  rw [hcut] at h
  exact h

/-- The quadratic recursion step: the two-branch inequality at cutoff `r` bounds the reference
Laplace transform by a Gaussian error and the square of the transform at cutoff `r - log 4`. -/
theorem cutoffLaplace_recursion_step
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (C : ℝ≥0) (hC : 0 < C)
    (r : ℝ) (hr : Real.log 4 + 1 ≤ r)
    (h2B : ∀ x : ℝ, cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤
      ∫ ξ, cutoffLaplace P Xc γ r (Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
          (x + γ * ξ - γ ^ 2 * C / 2) *
        cutoffLaplace P Xc γ r (Metric.ball invSubCenterRight (1 / 4 * (1 / 8)))
          (x + γ * ξ - γ ^ 2 * C / 2) ∂gaussianReal 0 C)
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : 0 ≤ x) :
    cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤
      Real.exp (-x ^ 2 / (128 * γ ^ 2 * C)) +
        (1 + 1 / ε) * Real.exp (-x ^ 2 / (64 * γ ^ 2 * Real.log 4)) +
        (1 + ε) * cutoffLaplace P Xc γ (r - Real.log 4) (Metric.ball 0 (1 / 8))
          (3 / 4 * x + (2 * Real.log (1 / 4) + γ ^ 2 / 2 * Real.log (1 / 4) -
            γ ^ 2 * C / 2)) ^ 2 := by
  set L' : ℝ → ℝ := cutoffLaplace P Xc γ (r - Real.log 4) (Metric.ball 0 (1 / 8)) with hL'
  set v₂ : ℝ≥0 := ⟨-Real.log (1 / 4), neg_nonneg.mpr (Real.log_nonpos (by norm_num)
    (by norm_num))⟩ with hv₂
  set c₁ : ℝ := 2 * Real.log (1 / 4) + γ ^ 2 / 2 * Real.log (1 / 4) with hc₁
  set a : ℝ := c₁ - γ ^ 2 * C / 2 with ha
  have hball : MeasurableSet (Metric.ball (0 : ℂ) (1 / 8)) := Metric.isOpen_ball.measurableSet
  have hanti : Antitone L' := cutoffLaplace_antitone P X hX Xc hXc γ _ _ hball
  have hnn : ∀ y, 0 ≤ L' y := fun y => cutoffLaplace_nonneg P Xc γ _ _ y
  have hle1 : ∀ y, L' y ≤ 1 := fun y => cutoffLaplace_le_one P X hX Xc γ _ _ y
  -- both subdisk transforms are the same Gaussian average
  have hsub : ∀ (b : ℂ), ‖b‖ = 1 / 16 → ∀ y,
      cutoffLaplace P Xc γ r (Metric.ball b (1 / 4 * (1 / 8))) y =
        ∫ w, L' (y + c₁ + γ * w) ∂gaussianReal 0 v₂ := by
    intro b hb y
    rw [cutoffLaplace_invSubdisk_scaling P X hX γ Xc hXc b hb r hr y]
    apply integral_congr_ae
    filter_upwards [] with w
    congr 1
    rw [hc₁]
    ring
  have hprod : ∀ ξ : ℝ,
      cutoffLaplace P Xc γ r (Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
          (x + γ * ξ - γ ^ 2 * C / 2) *
        cutoffLaplace P Xc γ r (Metric.ball invSubCenterRight (1 / 4 * (1 / 8)))
          (x + γ * ξ - γ ^ 2 * C / 2) =
      (∫ w, L' (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 := by
    intro ξ
    have harg : ∀ w : ℝ, x + γ * ξ - γ ^ 2 * C / 2 + c₁ + γ * w = x + a + γ * ξ + γ * w := by
      intro w
      rw [ha]
      ring
    have hint : (∫ w, L' (x + γ * ξ - γ ^ 2 * C / 2 + c₁ + γ * w) ∂gaussianReal 0 v₂) =
        ∫ w, L' (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂ :=
      integral_congr_ae (ae_of_all _ fun w => congrArg L' (harg w))
    rw [hsub _ norm_invSubCenterLeft, hsub _ norm_invSubCenterRight, hint, sq]
  have hmain : cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤
      ∫ ξ, (∫ w, L' (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ∂gaussianReal 0 C :=
    (h2B x).trans_eq (integral_congr_ae (ae_of_all _ hprod))
  have hsplit := gaussianSplit_two_branch L' hanti hnn hle1 γ C v₂ x a (x / 8) ε hε
  have htail₁ := gaussianReal_scaled_lower_tail_toReal C hC γ (x / 8) hγ (by positivity)
  have hv₂val : ((v₂ : ℝ≥0) : ℝ) = Real.log 4 := by
    rw [hv₂]
    change -Real.log (1 / 4) = Real.log 4
    rw [one_div, Real.log_inv, neg_neg]
  have hv₂pos : 0 < v₂ := by
    rw [← NNReal.coe_pos, hv₂val]
    exact Real.log_pos (by norm_num)
  have htail₂ := gaussianReal_scaled_lower_tail_toReal v₂ hv₂pos γ (x / 8) hγ (by positivity)
  rw [hv₂val] at htail₂
  have hT₁ : Real.exp (-(x / 8) ^ 2 / (2 * γ ^ 2 * C)) = Real.exp (-x ^ 2 / (128 * γ ^ 2 * C)) := by
    congr 1
    ring
  have hT₂ : Real.exp (-(x / 8) ^ 2 / (2 * γ ^ 2 * Real.log 4)) ^ 2 =
      Real.exp (-x ^ 2 / (64 * γ ^ 2 * Real.log 4)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hP₂nn : 0 ≤ (gaussianReal 0 v₂ {w | γ * w < -(x / 8)}).toReal := ENNReal.toReal_nonneg
  have hsq₂ : (gaussianReal 0 v₂ {w | γ * w < -(x / 8)}).toReal ^ 2 ≤
      Real.exp (-x ^ 2 / (64 * γ ^ 2 * Real.log 4)) := by
    rw [← hT₂]
    exact pow_le_pow_left₀ hP₂nn htail₂ 2
  have harg' : x + a - 2 * (x / 8) =
      3 / 4 * x + (2 * Real.log (1 / 4) + γ ^ 2 / 2 * Real.log (1 / 4) - γ ^ 2 * C / 2) := by
    rw [ha, hc₁]
    ring
  rw [harg'] at hsplit
  have hcoef : 0 ≤ 1 + 1 / ε := by positivity
  calc cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x
      ≤ _ := hmain
    _ ≤ _ := hsplit
    _ ≤ _ := by
        rw [hT₁] at htail₁
        have := mul_le_mul_of_nonneg_left hsq₂ hcoef
        linarith

end DOZZ.Proofs
