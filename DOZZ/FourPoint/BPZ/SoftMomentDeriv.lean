/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftMassDeriv

/-! # Differentiating a negative moment of the random softened mass

Let `m : Ω → Measure ℂ` be a random measure, and write `I(ω, z) = bpzSoftMassReal a ε w (m ω) z`
for the softened mass of `m ω` at `z`, with `DI(ω, z) = bpzSoftMassDeriv a ε w (m ω) z` and
`D²I(ω, z) = bpzSoftMassDeriv2 a ε w (m ω) z` its first and second derivatives in `z`. Suppose
that almost surely `I(ω, z) ≥ Y(ω) > 0` for `z` in the unit ball about `z₀`, with `Y^{-s}`
integrable. Then the negative moment `z ↦ ∫ I(ω, z)^{-s} dP(ω)` is differentiable at `z₀`
(`hasFDerivAt_bpzSoftMoment`), with derivative `∫ (−s I^{-s-1}) • DI dP`, and this derivative
is itself differentiable at `z₀` (`hasFDerivAt_bpzSoftMomentDeriv`), with derivative
`∫ (s (s+1) I^{-s-2}) • (DI ⊗ DI) + (−s I^{-s-1}) • D²I dP`, where `(DI ⊗ DI) h = (DI h) • DI` is
written `DI.smulRight DI`. The scalar evaluations of the two integrals on test vectors are
`bpzSoftMoment_deriv_apply` and `bpzSoftMoment_deriv2_apply`.

The proofs differentiate under the integral sign (`hasFDerivAt_integral_of_dominated_of_fderiv_le`)
on the unit ball about `z₀`. The dominating function is a multiple of `Y^{-s}`: by
`‖DI‖ ≤ (2|a|/ε) I` and `‖D²I‖ ≤ ((4|a(a−1)| + 2|a|)/ε²) I`, the derivatives of `I^{-s}` and of
`I^{-s-1} DI` are bounded by constants times `I^{-s} ≤ Y^{-s}`.

The file is organised as follows: real-power algebra and pointwise calculus for a positive
differentiable function `J` on `ℂ`; their specialization to the softened mass of a fixed measure
(derivative formulas and norm bounds); measurability and integrability for the random mass; the
two differentiation theorems; and the evaluations on vectors. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-! ### Instance shortcuts

As in `SoftMassDeriv`, instance search for norms, `Integrable` and scalar multiplication on the
space `ℂ →L[ℝ] ℂ →L[ℝ] ℝ` of bilinear forms needs the low-priority shortcuts defined there
(`bpzNormedAddCommGroupBilin`, `bpzNormedSpaceBilin`, definitionally the generic instances). We
re-activate them locally. They are used in proofs, and in the statement of the private lemma
`integrable_bpzSoftMomentField2`; no public statement below mentions them. -/

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

/-! ### Real-power algebra -/

/-- `J^(r-1) * J = J^r` for `J > 0`. -/
theorem bpzRpow_pred_mul {J : ℝ} (hJ : 0 < J) (r : ℝ) : J ^ (r - 1) * J = J ^ r := by
  rw [Real.rpow_sub_one hJ.ne', div_mul_cancel₀ _ hJ.ne']

/-- `J^(r-2) * (J * J) = J^r` for `J > 0`. -/
theorem bpzRpow_sub_two_mul_mul {J : ℝ} (hJ : 0 < J) (r : ℝ) : J ^ (r - 2) * (J * J) = J ^ r := by
  have h1 := bpzRpow_pred_mul hJ (r - 1)
  rw [show r - 1 - 1 = r - 2 by ring] at h1
  rw [← mul_assoc, h1, bpzRpow_pred_mul hJ r]

/-- The negative power is antitone: `J^(-s) ≤ Y^(-s)` for `0 < Y ≤ J` and `0 ≤ s`. -/
theorem bpzRpow_neg_le {s J Y : ℝ} (hs : 0 ≤ s) (hY : 0 < Y) (hYJ : Y ≤ J) :
    J ^ (-s) ≤ Y ^ (-s) :=
  Real.rpow_le_rpow_of_nonpos hY hYJ (by linarith)

/-! ### Pointwise calculus -/

/-- Chain rule for the negative power of a positive differentiable function. -/
theorem hasFDerivAt_bpzRpow_neg {J : ℂ → ℝ} {J' : ℂ →L[ℝ] ℝ} {z : ℂ} (s : ℝ)
    (hJ : HasFDerivAt J J' z) (hpos : 0 < J z) :
    HasFDerivAt (fun y => J y ^ (-s)) ((-s * J z ^ (-s - 1)) • J') z :=
  hJ.rpow_const (Or.inl hpos.ne')

/-- The derivative of the vector field `y ↦ (−s J(y)^(−s−1)) • DJ(y)`, where `J` is a positive
differentiable function with derivative `DJ`, and `DJ` is differentiable with derivative `DDJ`. -/
theorem hasFDerivAt_bpzMomentField {J : ℂ → ℝ} {DJ : ℂ → ℂ →L[ℝ] ℝ}
    {DDJ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ} {z : ℂ} (s : ℝ)
    (hJ : HasFDerivAt J (DJ z) z) (hDJ : HasFDerivAt DJ DDJ z) (hpos : 0 < J z) :
    HasFDerivAt (fun y => (-s * J y ^ (-s - 1)) • DJ y)
      ((s * (s + 1) * J z ^ (-s - 2)) • (DJ z).smulRight (DJ z) +
        (-s * J z ^ (-s - 1)) • DDJ) z := by
  have h1 : HasFDerivAt (fun y => J y ^ (-s - 1)) (((-s - 1) * J z ^ (-s - 2)) • DJ z) z := by
    have h := hJ.rpow_const (p := -s - 1) (Or.inl hpos.ne')
    rwa [show -s - 1 - 1 = -s - 2 by ring] at h
  have h3 := (h1.const_mul (-s)).fun_smul hDJ
  have e : ((-s) • (((-s - 1) * J z ^ (-s - 2)) • DJ z)).smulRight (DJ z) =
      (s * (s + 1) * J z ^ (-s - 2)) • (DJ z).smulRight (DJ z) := by
    ext h
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, smul_smul]
    congr 1
    ring
  rw [e, add_comm] at h3
  exact h3

/-- Norm bound for the first-moment vector field `(−s J^(−s−1)) • D`: if `‖D‖ ≤ A J` and
`0 < Y ≤ J`, the norm is at most `s A Y^(−s)`. -/
theorem norm_bpzMomentField_le {s J Y A : ℝ} {D : ℂ →L[ℝ] ℝ} (hs : 0 ≤ s) (hY : 0 < Y)
    (hYJ : Y ≤ J) (hA : 0 ≤ A) (hD : ‖D‖ ≤ A * J) :
    ‖(-s * J ^ (-s - 1)) • D‖ ≤ s * A * Y ^ (-s) := by
  have hJ : 0 < J := hY.trans_le hYJ
  have h1 : 0 ≤ J ^ (-s - 1) := Real.rpow_nonneg hJ.le _
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg h1]
  calc s * J ^ (-s - 1) * ‖D‖ ≤ s * J ^ (-s - 1) * (A * J) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg hs h1)
    _ = s * A * J ^ (-s) := by rw [← bpzRpow_pred_mul hJ (-s)]; ring
    _ ≤ s * A * Y ^ (-s) :=
        mul_le_mul_of_nonneg_left (bpzRpow_neg_le hs hY hYJ) (mul_nonneg hs hA)

/-- Norm bound for the derivative of the first-moment vector field: if `‖D‖ ≤ A J`, `‖DD‖ ≤ B J`
and `0 < Y ≤ J`, the norm is at most `(s (s+1) A² + s B) Y^(−s)`. -/
theorem norm_bpzMomentField2_le {s J Y A B : ℝ} {D : ℂ →L[ℝ] ℝ} {DD : ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
    (hs : 0 ≤ s) (hY : 0 < Y) (hYJ : Y ≤ J) (hA : 0 ≤ A)
    (hD : ‖D‖ ≤ A * J) (hDD : ‖DD‖ ≤ B * J) :
    ‖(s * (s + 1) * J ^ (-s - 2)) • D.smulRight D + (-s * J ^ (-s - 1)) • DD‖ ≤
      (s * (s + 1) * A ^ 2 + s * B) * Y ^ (-s) := by
  have hJ : 0 < J := hY.trans_le hYJ
  have h1 : 0 ≤ J ^ (-s - 1) := Real.rpow_nonneg hJ.le _
  have h2 : 0 ≤ J ^ (-s - 2) := Real.rpow_nonneg hJ.le _
  have hk : 0 ≤ s * (s + 1) * J ^ (-s - 2) := mul_nonneg (mul_nonneg hs (by linarith)) h2
  have hT1 : ‖(s * (s + 1) * J ^ (-s - 2)) • D.smulRight D‖ ≤ s * (s + 1) * A ^ 2 * J ^ (-s) := by
    rw [norm_smul, Real.norm_of_nonneg hk, ContinuousLinearMap.norm_smulRight_apply]
    have hDD2 : ‖D‖ * ‖D‖ ≤ (A * J) * (A * J) :=
      mul_le_mul hD hD (norm_nonneg _) (mul_nonneg hA hJ.le)
    calc s * (s + 1) * J ^ (-s - 2) * (‖D‖ * ‖D‖)
        ≤ s * (s + 1) * J ^ (-s - 2) * ((A * J) * (A * J)) := mul_le_mul_of_nonneg_left hDD2 hk
      _ = s * (s + 1) * A ^ 2 * (J ^ (-s - 2) * (J * J)) := by ring
      _ = s * (s + 1) * A ^ 2 * J ^ (-s) := by rw [bpzRpow_sub_two_mul_mul hJ]
  have hT2 : ‖(-s * J ^ (-s - 1)) • DD‖ ≤ s * B * J ^ (-s) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg h1]
    calc s * J ^ (-s - 1) * ‖DD‖ ≤ s * J ^ (-s - 1) * (B * J) :=
          mul_le_mul_of_nonneg_left hDD (mul_nonneg hs h1)
      _ = s * B * J ^ (-s) := by rw [← bpzRpow_pred_mul hJ (-s)]; ring
  have hsum : (s * (s + 1) * A ^ 2 + s * B) * J ^ (-s) ≤
      (s * (s + 1) * A ^ 2 + s * B) * Y ^ (-s) := by
    refine mul_le_mul_of_nonneg_left (bpzRpow_neg_le hs hY hYJ) ?_
    have hB : 0 ≤ B := by
      have := (norm_nonneg DD).trans hDD
      exact nonneg_of_mul_nonneg_left this hJ
    exact add_nonneg (mul_nonneg (mul_nonneg hs (by linarith)) (sq_nonneg A)) (mul_nonneg hs hB)
  calc ‖(s * (s + 1) * J ^ (-s - 2)) • D.smulRight D + (-s * J ^ (-s - 1)) • DD‖
      ≤ ‖(s * (s + 1) * J ^ (-s - 2)) • D.smulRight D‖ + ‖(-s * J ^ (-s - 1)) • DD‖ :=
        norm_add_le _ _
    _ ≤ s * (s + 1) * A ^ 2 * J ^ (-s) + s * B * J ^ (-s) := add_le_add hT1 hT2
    _ = (s * (s + 1) * A ^ 2 + s * B) * J ^ (-s) := by ring
    _ ≤ (s * (s + 1) * A ^ 2 + s * B) * Y ^ (-s) := hsum

/-! ### Fixed measure

For a single measure `μ` on `ℂ` with finite softened mass at `z`, the negative power of the mass
and the first-moment vector field are differentiable at `z` wherever the mass is positive, with the
derivatives obtained from `bpzSoftMassDeriv` and `bpzSoftMassDeriv2`; their norms are bounded by
constants times `Y^(−s)` for every lower bound `0 < Y ≤ I(z)`. -/

/-- The negative power of the softened mass is differentiable where the mass is positive. -/
theorem hasFDerivAt_bpzSoftMassPow {a ε : ℝ} (s : ℝ) (hε : 0 < ε) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {μ : Measure ℂ} {z : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) μ)
    (hpos : 0 < bpzSoftMassReal a ε w μ z) :
    HasFDerivAt (fun y => bpzSoftMassReal a ε w μ y ^ (-s))
      ((-s * bpzSoftMassReal a ε w μ z ^ (-s - 1)) • bpzSoftMassDeriv a ε w μ z) z :=
  hasFDerivAt_bpzRpow_neg s (hasFDerivAt_bpzSoftMassReal hε hw hw0 hint) hpos

/-- The first-moment vector field `y ↦ (−s I(y)^(−s−1)) • DI(y)` of the softened mass is
differentiable where the mass is positive. -/
theorem hasFDerivAt_bpzSoftMassField {a ε : ℝ} (s : ℝ) (hε : 0 < ε) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {μ : Measure ℂ} {z : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) μ)
    (hpos : 0 < bpzSoftMassReal a ε w μ z) :
    HasFDerivAt
      (fun y => (-s * bpzSoftMassReal a ε w μ y ^ (-s - 1)) • bpzSoftMassDeriv a ε w μ y)
      ((s * (s + 1) * bpzSoftMassReal a ε w μ z ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w μ z).smulRight (bpzSoftMassDeriv a ε w μ z) +
        (-s * bpzSoftMassReal a ε w μ z ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w μ z) z :=
  hasFDerivAt_bpzMomentField s (hasFDerivAt_bpzSoftMassReal hε hw hw0 hint)
    (hasFDerivAt_bpzSoftMassDeriv hε hw hw0 hint) hpos

/-- Domination of the first-moment vector field by `s (2|a|/ε) Y^(−s)`. -/
theorem norm_bpzSoftMassField_le {a ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {μ : Measure ℂ} {z : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) μ)
    {Y : ℝ} (hY : 0 < Y) (hYI : Y ≤ bpzSoftMassReal a ε w μ z) :
    ‖(-s * bpzSoftMassReal a ε w μ z ^ (-s - 1)) • bpzSoftMassDeriv a ε w μ z‖ ≤
      s * (2 * |a| / ε) * Y ^ (-s) :=
  norm_bpzMomentField_le hs hY hYI (by positivity) (norm_bpzSoftMassDeriv_le hε hw hw0 hint)

/-- Domination of the derivative of the first-moment vector field by
`(s (s+1) (2|a|/ε)² + s (4|a(a−1)| + 2|a|)/ε²) Y^(−s)`. -/
theorem norm_bpzSoftMassField2_le {a ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {μ : Measure ℂ} {z : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) μ)
    {Y : ℝ} (hY : 0 < Y) (hYI : Y ≤ bpzSoftMassReal a ε w μ z) :
    ‖(s * (s + 1) * bpzSoftMassReal a ε w μ z ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w μ z).smulRight (bpzSoftMassDeriv a ε w μ z) +
        (-s * bpzSoftMassReal a ε w μ z ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w μ z‖ ≤
      (s * (s + 1) * (2 * |a| / ε) ^ 2 + s * ((4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2)) *
        Y ^ (-s) :=
  norm_bpzMomentField2_le hs hY hYI (by positivity) (norm_bpzSoftMassDeriv_le hε hw hw0 hint)
    (norm_bpzSoftMassDeriv2_le hε hw hw0 hint)

/-! ### Random mass: measurability and integrability -/

/-- The negative power of the random mass is integrable, being dominated by `Y^(−s)`. -/
theorem integrable_bpzSoftMassPow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hs : 0 < s) {w : ℂ → ℝ} {z₀ : ℂ}
    (hmeasI : AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z₀) P)
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) :
    Integrable (fun ω => bpzSoftMassReal a ε w (m ω) z₀ ^ (-s)) P := by
  refine Integrable.mono' hYint (hmeasI.aemeasurable.pow_const (-s)).aestronglyMeasurable ?_
  filter_upwards [hYpos, hlow] with ω hY hl
  have h1 := hl z₀ (Metric.mem_ball_self one_pos)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hY.trans_le h1).le _)]
  exact bpzRpow_neg_le hs.le hY h1

/-- The first-moment vector field of the random mass is integrable, being dominated by
`s (2|a|/ε) Y^(−s)`. -/
theorem integrable_bpzSoftMomentField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    (hmeasI : AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z₀) P)
    (hmeasD : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z₀) P)
    (hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) (m ω))
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) :
    Integrable (fun ω => (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) •
      bpzSoftMassDeriv a ε w (m ω) z₀) P := by
  refine Integrable.mono' (hYint.const_mul (s * (2 * |a| / ε))) ?_ ?_
  · exact (((hmeasI.aemeasurable.pow_const (-s - 1)).const_mul (-s)).aestronglyMeasurable).smul
      hmeasD
  · filter_upwards [hint, hYpos, hlow] with ω hω hY hl
    exact norm_bpzSoftMassField_le hε hs.le hw hw0 hω hY (hl z₀ (Metric.mem_ball_self one_pos))

/-- Measurability of the integrand of the derivative of the first-moment vector field. -/
theorem aestronglyMeasurable_bpzSoftMomentField2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} {w : ℂ → ℝ} {z₀ : ℂ}
    (hmeasI : AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z₀) P)
    (hmeasD : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z₀) P)
    (hmeasD2 : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv2 a ε w (m ω) z₀) P) :
    AEStronglyMeasurable (fun ω =>
      (s * (s + 1) * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w (m ω) z₀).smulRight (bpzSoftMassDeriv a ε w (m ω) z₀) +
        (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w (m ω) z₀) P := by
  have hS : AEStronglyMeasurable (fun ω =>
      (bpzSoftMassDeriv a ε w (m ω) z₀).smulRight (bpzSoftMassDeriv a ε w (m ω) z₀)) P :=
    (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ hmeasD hmeasD
  have h2 : AEStronglyMeasurable (fun ω => s * (s + 1) * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 2))
      P := ((hmeasI.aemeasurable.pow_const (-s - 2)).const_mul (s * (s + 1))).aestronglyMeasurable
  have h1 : AEStronglyMeasurable (fun ω => -s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) P :=
    ((hmeasI.aemeasurable.pow_const (-s - 1)).const_mul (-s)).aestronglyMeasurable
  exact (h2.smul hS).add (h1.smul hmeasD2)

/-- The integrand of the derivative of the first-moment vector field is integrable, being
dominated by `C Y^(−s)`. (Private: its statement involves the local instance shortcuts.) -/
private theorem integrable_bpzSoftMomentField2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    (hmeasI : AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z₀) P)
    (hmeasD : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z₀) P)
    (hmeasD2 : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv2 a ε w (m ω) z₀) P)
    (hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) (m ω))
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) :
    Integrable (fun ω =>
      (s * (s + 1) * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w (m ω) z₀).smulRight (bpzSoftMassDeriv a ε w (m ω) z₀) +
        (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w (m ω) z₀)
      P := by
  refine Integrable.mono'
    (hYint.const_mul (s * (s + 1) * (2 * |a| / ε) ^ 2 +
      s * ((4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2)))
    (aestronglyMeasurable_bpzSoftMomentField2 m hmeasI hmeasD hmeasD2) ?_
  filter_upwards [hint, hYpos, hlow] with ω hω hY hl
  exact norm_bpzSoftMassField2_le hε hs.le hw hw0 hω hY (hl z₀ (Metric.mem_ball_self one_pos))

/-! ### Differentiation under the integral sign -/

/-- **Differentiation of the negative moment of the random softened mass.** If almost surely
`I(ω, z) ≥ Y(ω) > 0` for `z` in the unit ball about `z₀`, with `Y^(−s)` integrable, then
`z ↦ ∫ I(ω, z)^(−s) dP(ω)` is differentiable at `z₀`, with derivative
`∫ (−s I(ω, z₀)^(−s−1)) • DI(ω, z₀) dP(ω)`. -/
theorem hasFDerivAt_bpzSoftMoment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    (hmeasI : ∀ z, AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z) P)
    (hmeasD : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z₀) P)
    (hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) (m ω))
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) :
    HasFDerivAt (fun z => ∫ ω, bpzSoftMassReal a ε w (m ω) z ^ (-s) ∂P)
      (∫ ω, (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) •
        bpzSoftMassDeriv a ε w (m ω) z₀ ∂P) z₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P)
    (F := fun z ω => bpzSoftMassReal a ε w (m ω) z ^ (-s))
    (F' := fun z ω => (-s * bpzSoftMassReal a ε w (m ω) z ^ (-s - 1)) •
      bpzSoftMassDeriv a ε w (m ω) z)
    (bound := fun ω => s * (2 * |a| / ε) * Y ω ^ (-s))
    (Metric.ball_mem_nhds z₀ one_pos) ?_ ?_ ?_ ?_ (hYint.const_mul _) ?_
  · exact Eventually.of_forall fun z =>
      ((hmeasI z).aemeasurable.pow_const (-s)).aestronglyMeasurable
  · exact integrable_bpzSoftMassPow m hs (hmeasI z₀) hYpos hlow hYint
  · exact (((hmeasI z₀).aemeasurable.pow_const (-s - 1)).const_mul (-s)).aestronglyMeasurable.smul
      hmeasD
  · filter_upwards [hint, hYpos, hlow] with ω hω hY hl z hz
    exact norm_bpzSoftMassField_le hε hs.le hw hw0 (integrable_bpzSoftMass_of hε hw hw0 hω z) hY
      (hl z hz)
  · filter_upwards [hint, hYpos, hlow] with ω hω hY hl z hz
    exact hasFDerivAt_bpzSoftMassPow s hε hw hw0 (integrable_bpzSoftMass_of hε hw hw0 hω z)
      (hY.trans_le (hl z hz))

/-- **Differentiation of the derivative of the negative moment.** Under the hypotheses of
`hasFDerivAt_bpzSoftMoment`, with measurability of `DI(·, z)` on the unit ball about `z₀` and of
`D²I(·, z₀)`, the map `z ↦ ∫ (−s I(ω, z)^(−s−1)) • DI(ω, z) dP(ω)` is differentiable at `z₀`, with
derivative
`∫ (s (s+1) I(ω, z₀)^(−s−2)) • (DI(ω, z₀) ⊗ DI(ω, z₀)) + (−s I(ω, z₀)^(−s−1)) • D²I(ω, z₀) dP(ω)`
where `(DI.smulRight DI) h = (DI h) • DI`. -/
theorem hasFDerivAt_bpzSoftMomentDeriv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    (hmeasI : ∀ z, AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z) P)
    (hmeasD : ∀ z ∈ Metric.ball z₀ 1,
      AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z) P)
    (hmeasD2 : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv2 a ε w (m ω) z₀) P)
    (hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) (m ω))
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) :
    HasFDerivAt
      (fun z => ∫ ω, (-s * bpzSoftMassReal a ε w (m ω) z ^ (-s - 1)) •
        bpzSoftMassDeriv a ε w (m ω) z ∂P)
      (∫ ω, ((s * (s + 1) * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w (m ω) z₀).smulRight (bpzSoftMassDeriv a ε w (m ω) z₀) +
        (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w (m ω) z₀)
        ∂P) z₀ := by
  have hz₀ : z₀ ∈ Metric.ball z₀ 1 := Metric.mem_ball_self one_pos
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P)
    (F := fun z ω => (-s * bpzSoftMassReal a ε w (m ω) z ^ (-s - 1)) •
      bpzSoftMassDeriv a ε w (m ω) z)
    (F' := fun z ω => (s * (s + 1) * bpzSoftMassReal a ε w (m ω) z ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w (m ω) z).smulRight (bpzSoftMassDeriv a ε w (m ω) z) +
        (-s * bpzSoftMassReal a ε w (m ω) z ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w (m ω) z)
    (bound := fun ω => (s * (s + 1) * (2 * |a| / ε) ^ 2 +
      s * ((4 * |a * (a - 1)| + 2 * |a|) / ε ^ 2)) * Y ω ^ (-s))
    (Metric.ball_mem_nhds z₀ one_pos) ?_ ?_ ?_ ?_ (hYint.const_mul _) ?_
  · exact eventually_of_mem (Metric.ball_mem_nhds z₀ one_pos) fun z hz =>
      (((hmeasI z).aemeasurable.pow_const (-s - 1)).const_mul (-s)).aestronglyMeasurable.smul
        (hmeasD z hz)
  · exact integrable_bpzSoftMomentField m hε hs hw hw0 (hmeasI z₀) (hmeasD z₀ hz₀) hint hYpos hlow
      hYint
  · exact aestronglyMeasurable_bpzSoftMomentField2 m (hmeasI z₀) (hmeasD z₀ hz₀) hmeasD2
  · filter_upwards [hint, hYpos, hlow] with ω hω hY hl z hz
    exact norm_bpzSoftMassField2_le hε hs.le hw hw0 (integrable_bpzSoftMass_of hε hw hw0 hω z) hY
      (hl z hz)
  · filter_upwards [hint, hYpos, hlow] with ω hω hY hl z hz
    exact hasFDerivAt_bpzSoftMassField s hε hw hw0 (integrable_bpzSoftMass_of hε hw hw0 hω z)
      (hY.trans_le (hl z hz))

/-! ### The derivatives evaluated on vectors -/



/-- The first derivative of the negative moment evaluated at a vector `h`. -/
theorem bpzSoftMoment_deriv_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    (hmeasI : ∀ z, AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z) P)
    (hmeasD : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z₀) P)
    (hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) (m ω))
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) (h : ℂ) :
    (∫ ω, (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) •
        bpzSoftMassDeriv a ε w (m ω) z₀ ∂P) h =
      ∫ ω, (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) *
        bpzSoftMassDeriv a ε w (m ω) z₀ h ∂P := by
  have hI := integrable_bpzSoftMomentField m hε hs hw hw0 (hmeasI z₀) hmeasD hint hYpos hlow hYint
  rw [ContinuousLinearMap.integral_apply hI h]
  simp only [smul_apply, smul_eq_mul]

/-- The second derivative of the negative moment evaluated at two vectors `h, k`. -/
theorem bpzSoftMoment_deriv2_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : Ω → Measure ℂ) {a ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    (hmeasI : ∀ z, AEStronglyMeasurable (fun ω => bpzSoftMassReal a ε w (m ω) z) P)
    (hmeasD : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv a ε w (m ω) z₀) P)
    (hmeasD2 : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv2 a ε w (m ω) z₀) P)
    (hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ a * w x) (m ω))
    {Y : Ω → ℝ} (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal a ε w (m ω) z)
    (hYint : Integrable (fun ω => Y ω ^ (-s)) P) (h k : ℂ) :
    (∫ ω, ((s * (s + 1) * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 2)) •
          (bpzSoftMassDeriv a ε w (m ω) z₀).smulRight (bpzSoftMassDeriv a ε w (m ω) z₀) +
        (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) • bpzSoftMassDeriv2 a ε w (m ω) z₀)
        ∂P) h k =
      ∫ ω, (s * (s + 1) * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 2) *
          (bpzSoftMassDeriv a ε w (m ω) z₀ h * bpzSoftMassDeriv a ε w (m ω) z₀ k) +
        (-s * bpzSoftMassReal a ε w (m ω) z₀ ^ (-s - 1)) *
          bpzSoftMassDeriv2 a ε w (m ω) z₀ h k) ∂P := by
  have hI := integrable_bpzSoftMomentField2 m hε hs hw hw0 (hmeasI z₀) hmeasD hmeasD2 hint hYpos
    hlow hYint
  rw [ContinuousLinearMap.integral_apply hI h,
    ContinuousLinearMap.integral_apply (hI.apply_continuousLinearMap h) k]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

end DOZZ.Proofs
