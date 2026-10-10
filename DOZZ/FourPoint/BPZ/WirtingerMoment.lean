/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardDefs
public import DOZZ.FourPoint.BPZ.WirtingerMass
public import DOZZ.FourPoint.BPZ.MomentLimitB

/-! # Wirtinger combinations of the moment fields

Let `a = γχ/2`, let `w` be the base weight, `k = bpzSoftWeight … 0 z = |x − z|^{2a} w` the
degenerate four-point weight and `I = ∫ k dM` the four-point mass. Almost surely the chaos measure
has no atom at `z`, the singular weight `(1 + |x − z|^{-2}) k` is integrable and `I > 0`. Then the
two moment fields `−s I^{−s−1} DI` and `s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I` of the softened
mass at `ε = 0` are bounded by multiples of `I^{−(s+1)} ∫ (1 + |x − z|^{-2}) k dM`, which is
integrable. Their Wirtinger combinations are the meromorphic moments `E₁`, `D₁`, `D₂` of
`bpzMomE1`, `bpzMomD1`, `bpzMomD2`:

* `bpz_wirtL_momField1_zero`: `∂ E[−s I^{−s−1} DI] = −s a E₁`;
* `bpz_wirt2L_momField2_zero`: `∂² E[s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I]
  = s(s+1) a² D₂ − s a (a − 1) D₁`.

The pathwise estimates use `|∫ k/(z − x)| ≤ ∫ w |x − z|^{2a−1}` together with the Cauchy–Schwarz
inequality `(∫ w t^{2a−1})² ≤ (∫ w t^{2a}) (∫ w t^{2a−2})`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

variable {γ χ α₁ α₂ α₃ : ℝ}

/-! ### Pointwise comparisons off the root -/

/-- Elementary inequality behind `t^{-1} ≤ 1 + t^{-2}`. -/
theorem bpzWM_aux_ineq {u v : ℝ} (hu : 0 ≤ u) : u * v ≤ (1 + v ^ 2) * u := by
  have h := mul_nonneg hu (sq_nonneg (v - 1 / 2))
  linarith

/-- Off the root, `w |x − z|^{2a−1} ≤ (1 + |x − z|^{-2}) k` for `k = |x − z|^{2a} w`. -/
theorem bpzWM_w1_le {a : ℝ} {w k : ℂ → ℝ} {z : ℂ} (hw0 : ∀ x, 0 ≤ w x)
    (hk : ∀ x, k x = ‖x - z‖ ^ (2 * a) * w x) {x : ℂ} (hx : x ≠ z) :
    w x * ‖x - z‖ ^ (2 * a - 1) ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x := by
  have ht : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have h1 : ‖x - z‖ ^ (2 * a - 1) = ‖x - z‖ ^ (2 * a) * ‖x - z‖⁻¹ := by
    rw [Real.rpow_sub_one ht.ne', div_eq_mul_inv]
  have h2 : ‖x - z‖ ^ (-2 : ℝ) = (‖x - z‖⁻¹) ^ 2 := by
    rw [Real.rpow_neg ht.le, Real.rpow_two, inv_pow]
  have hu : 0 ≤ ‖x - z‖ ^ (2 * a) * w x := mul_nonneg (Real.rpow_nonneg ht.le _) (hw0 x)
  rw [hk x, h1, h2]
  calc w x * (‖x - z‖ ^ (2 * a) * ‖x - z‖⁻¹)
      = (‖x - z‖ ^ (2 * a) * w x) * ‖x - z‖⁻¹ := by ring
    _ ≤ _ := bpzWM_aux_ineq hu

/-- Off the root, `w |x − z|^{2a−2} = |x − z|^{-2} k` for `k = |x − z|^{2a} w`. -/
theorem bpzWM_w2_eq {a : ℝ} {w k : ℂ → ℝ} {z : ℂ} (hk : ∀ x, k x = ‖x - z‖ ^ (2 * a) * w x)
    {x : ℂ} (hx : x ≠ z) : w x * ‖x - z‖ ^ (2 * a - 2) = ‖x - z‖ ^ (-2 : ℝ) * k x := by
  have ht : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [hk x, show 2 * a - 2 = 2 * a + (-2 : ℝ) by ring, Real.rpow_add ht]
  ring

/-- The root weight `k = |x − z|^{2a} w` is nonnegative. -/
theorem bpzWM_k_nonneg {a : ℝ} {w k : ℂ → ℝ} {z : ℂ} (hw0 : ∀ x, 0 ≤ w x)
    (hk : ∀ x, k x = ‖x - z‖ ^ (2 * a) * w x) (x : ℂ) : 0 ≤ k x := by
  rw [hk x]
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hw0 x)

/-- The hypotheses of the pathwise estimates: `a ∈ (0, 1]`, a nonnegative measurable weight `w`,
the root weight `k = |x − z|^{2a} w`, and a measure `m` without atom at `z` for which the singular
weight `(1 + |x − z|^{-2}) k` is integrable. -/
structure BPZWMData (a : ℝ) (w k : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) : Prop where
  ha : 0 < a
  ha1 : a ≤ 1
  hw : Measurable w
  hw0 : ∀ x, 0 ≤ w x
  hk : ∀ x, k x = ‖x - z‖ ^ (2 * a) * w x
  hz : m {z} = 0
  hg : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m

/-! ### Integrability of the near-root integrands -/

variable {a : ℝ} {w k : ℂ → ℝ} {m : Measure ℂ} {z : ℂ}

/-- `w |x − z|^{2a−1}` is integrable. -/
theorem bpzWM_integrable_w1 (H : BPZWMData a w k m z) :
    Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 1)) m := by
  refine H.hg.mono' (H.hw.mul
    ((measurable_id.sub measurable_const).norm.pow_const _)).aestronglyMeasurable ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (H.hw0 x) (Real.rpow_nonneg (norm_nonneg _) _))]
  exact bpzWM_w1_le H.hw0 H.hk hx

/-- `w |x − z|^{2a−2}` is integrable. -/
theorem bpzWM_integrable_w2 (H : BPZWMData a w k m z) :
    Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 2)) m := by
  refine H.hg.mono' (H.hw.mul
    ((measurable_id.sub measurable_const).norm.pow_const _)).aestronglyMeasurable ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (H.hw0 x) (Real.rpow_nonneg (norm_nonneg _) _)),
    bpzWM_w2_eq H.hk hx]
  have hk0 := bpzWM_k_nonneg H.hw0 H.hk x
  calc ‖x - z‖ ^ (-2 : ℝ) * k x ≤ k x + ‖x - z‖ ^ (-2 : ℝ) * k x := le_add_of_nonneg_left hk0
    _ = (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x := by ring

/-- The root weight `k = |x − z|^{2a} w` is measurable. -/
theorem bpzWM_measurable_k (H : BPZWMData a w k m z) : Measurable k := by
  have h : k = fun x => ‖x - z‖ ^ (2 * a) * w x := funext H.hk
  rw [h]
  exact ((measurable_id.sub measurable_const).norm.pow_const _).mul H.hw

/-- `k = w |x − z|^{2a}` is integrable. -/
theorem bpzWM_integrable_k (H : BPZWMData a w k m z) : Integrable k m := by
  refine H.hg.mono' (bpzWM_measurable_k H).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hk0 := bpzWM_k_nonneg H.hw0 H.hk x
  rw [Real.norm_of_nonneg hk0]
  calc k x ≤ k x + ‖x - z‖ ^ (-2 : ℝ) * k x :=
        le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hk0)
    _ = (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x := by ring

/-- `w |x − z|^{2a} = k`. -/
theorem bpzWM_w0_eq (H : BPZWMData a w k m z) (x : ℂ) : w x * ‖x - z‖ ^ (2 * a) = k x := by
  rw [H.hk x, mul_comm]

/-- `w |x − z|^{2a}` is integrable. -/
theorem bpzWM_integrable_w0 (H : BPZWMData a w k m z) :
    Integrable (fun x => w x * ‖x - z‖ ^ (2 * a)) m :=
  (bpzWM_integrable_k H).congr (Eventually.of_forall fun x => (bpzWM_w0_eq H x).symm)

/-! ### Comparison of the near-root integrals with the singular mass -/

/-- `∫ w |x − z|^{2a−1} ≤ ∫ (1 + |x − z|^{-2}) k`. -/
theorem bpzWM_n1_le (H : BPZWMData a w k m z) :
    ∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m ≤ ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  refine integral_mono_ae (bpzWM_integrable_w1 H) H.hg ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  exact bpzWM_w1_le H.hw0 H.hk hx

/-- `∫ w |x − z|^{2a−2} ≤ ∫ (1 + |x − z|^{-2}) k`. -/
theorem bpzWM_n2_le (H : BPZWMData a w k m z) :
    ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m ≤ ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  refine integral_mono_ae (bpzWM_integrable_w2 H) H.hg ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  rw [bpzWM_w2_eq H.hk hx]
  have hk0 := bpzWM_k_nonneg H.hw0 H.hk x
  calc ‖x - z‖ ^ (-2 : ℝ) * k x ≤ k x + ‖x - z‖ ^ (-2 : ℝ) * k x := le_add_of_nonneg_left hk0
    _ = (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x := by ring

/-- The mass `∫ k` is nonnegative. -/
theorem bpzWM_mass_nonneg (H : BPZWMData a w k m z) : 0 ≤ ∫ x, k x ∂m :=
  integral_nonneg (bpzWM_k_nonneg H.hw0 H.hk)

/-- The softened mass at `ε = 0` is `∫ k`. -/
theorem bpzWM_softMassReal_eq (H : BPZWMData a w k m z) :
    bpzSoftMassReal a 0 w m z = ∫ x, k x ∂m := by
  unfold bpzSoftMassReal
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (Complex.normSq (x - z) + (0 : ℝ) ^ 2) ^ a * w x = k x
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, add_zero, bpz_normSq_rpow_eq, H.hk x]

/-- Cauchy–Schwarz: `(∫ w t^{2a−1})² ≤ I ∫ w t^{2a−2}`, with `I = ∫ k`. -/
theorem bpzWM_cauchySchwarz (H : BPZWMData a w k m z) :
    (∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m) ^ 2 ≤
      (∫ x, k x ∂m) * ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := by
  have h := bpz_near_cauchySchwarz H.hw H.hw0 H.hz (bpzWM_integrable_w0 H)
    (bpzWM_integrable_w2 H)
  rwa [integral_congr_ae (Eventually.of_forall (bpzWM_w0_eq H))] at h

/-! ### Pathwise bounds on the derivative masses -/

/-- The first derivative mass is bounded by `2a ∫ w t^{2a−1}`. -/
theorem bpzWM_norm_deriv_le (H : BPZWMData a w k m z) :
    ‖bpzSoftMassDeriv a 0 w m z‖ ≤ 2 * a * ∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m :=
  norm_bpzSoftMassDeriv_le_near H.ha H.ha1 H.hw0 H.hz (bpzWM_integrable_w1 H)

/-- The square of the first derivative mass is bounded by `4a² I ∫ (1 + t^{-2}) k`. -/
theorem bpzWM_norm_deriv_sq_le (H : BPZWMData a w k m z) :
    ‖bpzSoftMassDeriv a 0 w m z‖ ^ 2 ≤
      4 * a ^ 2 * ((∫ x, k x ∂m) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) := by
  have h1 := bpzWM_norm_deriv_le H
  have hcs := bpzWM_cauchySchwarz H
  have hn2 := bpzWM_n2_le H
  have hI := bpzWM_mass_nonneg H
  calc ‖bpzSoftMassDeriv a 0 w m z‖ ^ 2
      ≤ (2 * a * ∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = 4 * a ^ 2 * (∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m) ^ 2 := by ring
    _ ≤ 4 * a ^ 2 * ((∫ x, k x ∂m) * ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m) := by gcongr
    _ ≤ 4 * a ^ 2 * ((∫ x, k x ∂m) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) := by gcongr

/-- The second derivative mass is bounded by `(4a(1 − a) + 2a) ∫ (1 + t^{-2}) k`. -/
theorem bpzWM_norm_deriv2_le (H : BPZWMData a w k m z) :
    ‖bpzSoftMassDeriv2 a 0 w m z‖ ≤
      (4 * a * (1 - a) + 2 * a) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  have h := norm_bpzSoftMassDeriv2_le_near (ε := 0) H.ha H.ha1 H.hw0 H.hz
    (bpzWM_integrable_w2 H)
  have hK : 0 ≤ 4 * a * (1 - a) + 2 * a := by
    have := sub_nonneg.mpr H.ha1
    have := H.ha
    positivity
  exact h.trans (mul_le_mul_of_nonneg_left (bpzWM_n2_le H) hK)

/-! ### Pathwise bounds on the moment fields -/

/-- The first moment field is bounded by `2as · I^{-(s+1)} ∫ (1 + t^{-2}) k`. -/
theorem bpzWM_norm_momField1_le (H : BPZWMData a w k m z) {s : ℝ} (hs : 0 ≤ s)
    (hI : 0 < ∫ x, k x ∂m) :
    ‖bpzMomField1 a s 0 w w m z‖ ≤ 2 * a * s *
      ((∫ x, k x ∂m) ^ (-(s + 1)) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) := by
  unfold bpzMomField1
  rw [bpzWM_softMassReal_eq H, show -(s + 1) = -s - 1 by ring, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg (Real.rpow_nonneg hI.le _)]
  have ha := H.ha
  have hD := (bpzWM_norm_deriv_le H).trans
    (mul_le_mul_of_nonneg_left (bpzWM_n1_le H) (by positivity))
  have h1 : 0 ≤ (∫ x, k x ∂m) ^ (-s - 1) := Real.rpow_nonneg hI.le _
  calc s * (∫ x, k x ∂m) ^ (-s - 1) * ‖bpzSoftMassDeriv a 0 w m z‖
      ≤ s * (∫ x, k x ∂m) ^ (-s - 1) * (2 * a * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg hs h1)
    _ = _ := by ring

/-- The second moment field is bounded by `C · I^{-(s+1)} ∫ (1 + t^{-2}) k`. -/
theorem bpzWM_norm_momField2_le (H : BPZWMData a w k m z) {s : ℝ} (hs : 0 ≤ s)
    (hI : 0 < ∫ x, k x ∂m) :
    ‖bpzMomField2 a s 0 w w m z‖ ≤
      (4 * a ^ 2 * s * (s + 1) + s * (4 * a * (1 - a) + 2 * a)) *
        ((∫ x, k x ∂m) ^ (-(s + 1)) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) := by
  unfold bpzMomField2
  rw [bpzWM_softMassReal_eq H]
  have hDD := bpzWM_norm_deriv_sq_le H
  have hD2 := bpzWM_norm_deriv2_le H
  set I : ℝ := ∫ x, k x ∂m with hIdef
  set G : ℝ := ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m with hGdef
  set D : ℂ →L[ℝ] ℝ := bpzSoftMassDeriv a 0 w m z with hD
  set D2 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := bpzSoftMassDeriv2 a 0 w m z with hD2def
  have hpow : I ^ (-s - 2) * I = I ^ (-s - 1) := by
    have := bpzRpow_pred_mul hI (-s - 1)
    rwa [show -s - 1 - 1 = -s - 2 by ring] at this
  have h1 : 0 ≤ I ^ (-s - 1) := Real.rpow_nonneg hI.le _
  have h2 : 0 ≤ I ^ (-s - 2) := Real.rpow_nonneg hI.le _
  have hc : 0 ≤ s * (s + 1) * I ^ (-s - 2) := mul_nonneg (mul_nonneg hs (by linarith)) h2
  have hDD' : ‖D‖ * ‖D‖ ≤ 4 * a ^ 2 * (I * G) := by rw [← sq]; exact hDD
  rw [show -(s + 1) = -s - 1 by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hc, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg hs, abs_of_nonneg h1, ContinuousLinearMap.norm_smulRight_apply]
  calc s * (s + 1) * I ^ (-s - 2) * (‖D‖ * ‖D‖) + s * I ^ (-s - 1) * ‖D2‖
      ≤ s * (s + 1) * I ^ (-s - 2) * (4 * a ^ 2 * (I * G)) +
        s * I ^ (-s - 1) * ((4 * a * (1 - a) + 2 * a) * G) :=
        add_le_add (mul_le_mul_of_nonneg_left hDD' hc)
          (mul_le_mul_of_nonneg_left hD2 (mul_nonneg hs h1))
    _ = _ := by rw [← hpow]; ring

/-! ### Pathwise Wirtinger identities -/

/-- `|x − z|^{2a} w = k`, in the form produced by the Wirtinger computations. -/
theorem bpzWM_normSq_eq (H : BPZWMData a w k m z) (x : ℂ) :
    Complex.normSq (x - z) ^ a * w x = k x := by
  rw [H.hk x, bpz_normSq_rpow_eq]

/-- The Wirtinger combination of the first derivative mass is `a ∫ k/(z − x)`. -/
theorem bpzWM_wirtL_deriv (H : BPZWMData a w k m z) :
    bpzWirtL (bpzSoftMassDeriv a 0 w m z) = (a : ℂ) * ∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m := by
  rw [bpzWirtL_softMassDeriv_zero H.ha H.ha1 H.hw H.hw0 H.hz (bpzWM_integrable_w1 H)]
  simp only [bpzWM_normSq_eq H]

/-- The second Wirtinger combination of the second derivative mass is `a (a − 1) ∫ k/(z − x)²`. -/
theorem bpzWM_wirt2L_deriv2 (H : BPZWMData a w k m z) :
    bpzWirt2L (bpzSoftMassDeriv2 a 0 w m z) =
      ((a * (a - 1) : ℝ) : ℂ) * ∫ x, ((k x : ℝ) : ℂ) / (z - x) ^ 2 ∂m := by
  rw [bpzWirt2L_softMassDeriv2_zero H.ha H.ha1 H.hw H.hw0 H.hz (bpzWM_integrable_w2 H)]
  simp only [bpzWM_normSq_eq H]

/-- The Wirtinger combination of the first moment field. -/
theorem bpzWM_wirtL_momField1 (H : BPZWMData a w k m z) (s : ℝ) :
    bpzWirtL (bpzMomField1 a s 0 w w m z) = -((s * a : ℝ) : ℂ) *
      ((((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) * ∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m) := by
  unfold bpzMomField1
  rw [map_smul, Complex.real_smul, bpzWM_wirtL_deriv H, bpzWM_softMassReal_eq H]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The second Wirtinger combination of the second moment field. -/
theorem bpzWM_wirt2L_momField2 (H : BPZWMData a w k m z) (s : ℝ) :
    bpzWirt2L (bpzMomField2 a s 0 w w m z) =
      ((s * (s + 1) * a ^ 2 : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 2) : ℝ) : ℂ) *
        (∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m) ^ 2) -
      ((s * a * (a - 1) : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
        ∫ x, ((k x : ℝ) : ℂ) / (z - x) ^ 2 ∂m) := by
  unfold bpzMomField2
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul, bpzWirt2L_smulRight,
    bpzWM_wirtL_deriv H, bpzWM_wirt2L_deriv2 H, bpzWM_softMassReal_eq H]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_pow]
  ring

/-! ### Pathwise bounds on the meromorphic moments -/

/-- `|∫ k/(z − x)| ≤ ∫ w |x − z|^{2a−1}`. -/
theorem bpzWM_norm_J1_le (H : BPZWMData a w k m z) :
    ‖∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m‖ ≤ ∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m := by
  refine norm_integral_le_of_norm_le (bpzWM_integrable_w1 H) ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  have h := bpz_norm_div_root_pow a 1 (H.hw0 x) hx
  rw [bpzWM_normSq_eq H x] at h
  simpa using h.le

/-- `|∫ k/(z − x)²| ≤ ∫ w |x − z|^{2a−2}`. -/
theorem bpzWM_norm_J2_le (H : BPZWMData a w k m z) :
    ‖∫ x, ((k x : ℝ) : ℂ) / (z - x) ^ 2 ∂m‖ ≤ ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := by
  refine norm_integral_le_of_norm_le (bpzWM_integrable_w2 H) ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  have h := bpz_norm_div_root_pow a 2 (H.hw0 x) hx
  rw [bpzWM_normSq_eq H x] at h
  simpa using h.le

/-- The pathwise bound `|I^{-s-2} (∫ k/(z − x))²| ≤ I^{-(s+1)} ∫ (1 + t^{-2}) k`. -/
theorem bpzWM_norm_T2_le (H : BPZWMData a w k m z) (s : ℝ) (hI : 0 < ∫ x, k x ∂m) :
    ‖(((∫ x, k x ∂m) ^ (-s - 2) : ℝ) : ℂ) * (∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m) ^ 2‖ ≤
      (∫ x, k x ∂m) ^ (-(s + 1)) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  have hJ : ‖∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m‖ ^ 2 ≤
      (∫ x, k x ∂m) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m :=
    calc ‖∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m‖ ^ 2
        ≤ (∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (bpzWM_norm_J1_le H) 2
      _ ≤ (∫ x, k x ∂m) * ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := bpzWM_cauchySchwarz H
      _ ≤ _ := mul_le_mul_of_nonneg_left (bpzWM_n2_le H) hI.le
  set I : ℝ := ∫ x, k x ∂m with hIdef
  set G : ℝ := ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m with hGdef
  have hpow : I ^ (-s - 2) * I = I ^ (-s - 1) := by
    have := bpzRpow_pred_mul hI (-s - 1)
    rwa [show -s - 1 - 1 = -s - 2 by ring] at this
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hI.le _),
    show -(s + 1) = -s - 1 by ring]
  calc I ^ (-s - 2) * ‖∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m‖ ^ 2 ≤ I ^ (-s - 2) * (I * G) :=
        mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hI.le _)
    _ = I ^ (-s - 1) * G := by rw [← hpow]; ring

/-- The pathwise bound `|I^{-s-1} ∫ k/(z − x)²| ≤ I^{-(s+1)} ∫ (1 + t^{-2}) k`. -/
theorem bpzWM_norm_T1_le (H : BPZWMData a w k m z) (s : ℝ) (hI : 0 < ∫ x, k x ∂m) :
    ‖(((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) * ∫ x, ((k x : ℝ) : ℂ) / (z - x) ^ 2 ∂m‖ ≤
      (∫ x, k x ∂m) ^ (-(s + 1)) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hI.le _),
    show -(s + 1) = -s - 1 by ring]
  exact mul_le_mul_of_nonneg_left ((bpzWM_norm_J2_le H).trans (bpzWM_n2_le H))
    (Real.rpow_nonneg hI.le _)

/-! ### The four-point setting -/

/-- Almost surely the pathwise hypotheses hold for the four-point weight, and the four-point
mass is positive. -/
theorem bpzWM_good_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∀ᵐ ω ∂P, BPZWMData (γ * χ / 2) (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) (M ω) z ∧
      0 < ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω := by
  have ha : 0 < γ * χ / 2 := by positivity
  filter_upwards [gmc_noAtoms_ae P X hX γ hγ hγ2 M hM hMm,
    bpz_singular_integrable_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM hχ hα₁ hα₂
      hα₃ (le_refl 1) hz0 hz1] with ω hat ⟨hgi, hpos, hfin⟩
  refine ⟨⟨ha, ha1, measurable_bpzBaseWeight, bpzBaseWeight_nonneg, fun x => ?_, hat z, hgi⟩, ?_⟩
  · rw [bpzSoftWeight_zero_norm, show 2 * (γ * χ / 2) = γ * χ by ring]
  · have h := bpzSoftI_eq_toReal (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 (M ω) z
    rw [bpzSoftI_eq_integral] at h
    rw [h]
    exact ENNReal.toReal_pos hpos.ne' hfin.ne

/-! ### Integrability of the moment fields -/

/-- The first moment field of the four-point mass is integrable. -/
theorem bpzWM_integrable_momField1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω => bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P := by
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ (q := s + 1) (by linarith) hz0 hz1
  refine Integrable.mono' (hdom.const_mul (2 * (γ * χ / 2) * s))
    (bpz_stronglyMeasurable_momField1 hMm (γ * χ / 2) s 0 measurable_bpzBaseWeight
      measurable_bpzBaseWeight z).aestronglyMeasurable ?_
  filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
    with ω ⟨H, hI⟩
  exact bpzWM_norm_momField1_le H hs hI

/-- The second moment field of the four-point mass is integrable. -/
theorem bpzWM_integrable_momField2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω => bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P := by
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ (q := s + 1) (by linarith) hz0 hz1
  refine Integrable.mono'
    (hdom.const_mul (4 * (γ * χ / 2) ^ 2 * s * (s + 1) +
      s * (4 * (γ * χ / 2) * (1 - γ * χ / 2) + 2 * (γ * χ / 2))))
    (bpz_stronglyMeasurable_momField2 hMm (γ * χ / 2) s 0 measurable_bpzBaseWeight
      measurable_bpzBaseWeight z).aestronglyMeasurable ?_
  filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
    with ω ⟨H, hI⟩
  exact bpzWM_norm_momField2_le H hs hI

/-! ### Integrability of the meromorphic moments -/

/-- The meromorphic integral `∫ k/(z − x) dM` is a measurable function of the chaos. -/
theorem bpzWM_measurable_J1 {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) {k : ℂ → ℝ} (hk : Measurable k) (z : ℂ) :
    Measurable (fun ω => ∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂M ω) :=
  (bpz_stronglyMeasurable_integral_measure (f := fun x : ℂ => ((k x : ℝ) : ℂ) / (z - x))
    ((Complex.measurable_ofReal.comp hk).div
      (measurable_const.sub measurable_id)).stronglyMeasurable).measurable.comp hMm

/-- The meromorphic integral `∫ k/(z − x)² dM` is a measurable function of the chaos. -/
theorem bpzWM_measurable_J2 {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) {k : ℂ → ℝ} (hk : Measurable k) (z : ℂ) :
    Measurable (fun ω => ∫ x, ((k x : ℝ) : ℂ) / (z - x) ^ 2 ∂M ω) :=
  (bpz_stronglyMeasurable_integral_measure (f := fun x : ℂ => ((k x : ℝ) : ℂ) / (z - x) ^ 2)
    ((Complex.measurable_ofReal.comp hk).div
      ((measurable_const.sub measurable_id).pow_const 2)).stronglyMeasurable).measurable.comp hMm

/-- `I^{-s-2} (∫ k/(z − x))²` is integrable. -/
theorem bpzWM_integrable_T2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) *
        (∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂M ω) ^ 2) P := by
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ (q := s + 1) (by linarith) hz0 hz1
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hIm : Measurable fun ω => ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω :=
    (measurable_integral_measure hkm).comp hMm
  refine Integrable.mono' hdom ?_ ?_
  · exact ((Complex.measurable_ofReal.comp (hIm.pow_const _)).mul
      ((bpzWM_measurable_J1 hMm hkm z).pow_const 2)).aestronglyMeasurable
  · filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
      with ω ⟨H, hI⟩
    exact bpzWM_norm_T2_le H s hI

/-- `I^{-s-1} ∫ k/(z − x)²` is integrable. -/
theorem bpzWM_integrable_T1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
        ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ^ 2 ∂M ω) P := by
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ (q := s + 1) (by linarith) hz0 hz1
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hIm : Measurable fun ω => ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω :=
    (measurable_integral_measure hkm).comp hMm
  refine Integrable.mono' hdom ?_ ?_
  · exact ((Complex.measurable_ofReal.comp (hIm.pow_const _)).mul
      (bpzWM_measurable_J2 hMm hkm z)).aestronglyMeasurable
  · filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
      with ω ⟨H, hI⟩
    exact bpzWM_norm_T1_le H s hI

/-! ### The Wirtinger combinations of the expected moment fields -/

/-- **The Wirtinger combination of the expected first moment field.** The first moment field
`−s I^{−s−1} DI` of the four-point mass is integrable, and the Wirtinger combination of its
expectation is `−s a E₁`. -/
theorem bpz_wirtL_momField1_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω => bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P ∧
    bpzWirtL (∫ ω, bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) =
      -((s * (γ * χ / 2) : ℝ) : ℂ) * bpzMomE1 P M γ χ α₁ α₂ α₃ s z := by
  have hint := bpzWM_integrable_momField1 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  refine ⟨hint, ?_⟩
  rw [← ContinuousLinearMap.integral_comp_comm bpzWirtL hint]
  have hae : ∀ᵐ ω ∂P, bpzWirtL (bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) =
      -((s * (γ * χ / 2) : ℝ) : ℂ) *
        ((((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
          ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂M ω) := by
    filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
      with ω hω
    exact bpzWM_wirtL_momField1 hω.1 s
  rw [integral_congr_ae hae, integral_const_mul]
  rfl

/-- **The Wirtinger combination of the expected second moment field.** The second moment field
`s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I` of the four-point mass is integrable, and the second
Wirtinger combination of its expectation is `s(s+1) a² D₂ − s a (a − 1) D₁`. -/
theorem bpz_wirt2L_momField2_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω => bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P ∧
    bpzWirt2L (∫ ω, bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) =
      ((s * (s + 1) * (γ * χ / 2) ^ 2 : ℝ) : ℂ) * bpzMomD2 P M γ χ α₁ α₂ α₃ s z -
        ((s * (γ * χ / 2) * (γ * χ / 2 - 1) : ℝ) : ℂ) * bpzMomD1 P M γ χ α₁ α₂ α₃ s z := by
  have hint := bpzWM_integrable_momField2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  have hT2 := bpzWM_integrable_T2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  have hT1 := bpzWM_integrable_T1 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  refine ⟨hint, ?_⟩
  rw [← ContinuousLinearMap.integral_comp_comm bpzWirt2L hint]
  have hae : ∀ᵐ ω ∂P, bpzWirt2L (bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) =
      ((s * (s + 1) * (γ * χ / 2) ^ 2 : ℝ) : ℂ) *
        ((((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) *
          (∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂M ω) ^ 2) -
      ((s * (γ * χ / 2) * (γ * χ / 2 - 1) : ℝ) : ℂ) *
        ((((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
          ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ^ 2 ∂M ω) := by
    filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
      with ω hω
    exact bpzWM_wirt2L_momField2 hω.1 s
  rw [integral_congr_ae hae, integral_sub (hT2.const_mul _) (hT1.const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

end DOZZ.Proofs
