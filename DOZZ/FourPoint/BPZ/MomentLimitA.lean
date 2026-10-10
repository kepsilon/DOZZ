/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentMeas
public import DOZZ.FourPoint.BPZ.SoftFarCont

/-! # Near/far decomposition of the derivative masses

For a weight `w` and a base point `z₀`, the derivative masses at a root `z` within `r / 2` of `z₀`
split into the contributions of the near weight `1_{|x − z₀| < r} w` and of the far weight
`1_{|x − z₀| ≥ r} w`. The near contributions are controlled by the integrals of
`|x − z|^{2a−1}` and `|x − z|^{2a−2}` against the near weight; the far contributions by the
softened mass. We record the resulting bounds for the differences between the moment fields and
their far parts. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

private noncomputable local instance bpzMLAAddMonoidBilin :
    AddMonoid (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := inferInstance

private noncomputable local instance bpzMLAAddCommMonoidBilin :
    AddCommMonoid (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := inferInstance

private noncomputable local instance bpzMLAAddCommGroupBilin :
    AddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := inferInstance

private noncomputable local instance bpzMLAModuleBilin :
    Module ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := inferInstance

private noncomputable local instance bpzMLANormedAddCommGroupDual :
    NormedAddCommGroup (ℂ →L[ℝ] ℝ) := inferInstance

private noncomputable local instance bpzMLANormedSpaceDual :
    NormedSpace ℝ (ℂ →L[ℝ] ℝ) := inferInstance

/-- Almost every point differs from a root that is not an atom. -/
theorem bpz_ae_ne_of_atom {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0) : ∀ᵐ x ∂m, x ≠ z := by
  rw [ae_iff]; simpa using hz

/-- The near weight `1_{|x − z₀| < r} w`. -/
theorem bpz_measurable_nearPart {w : ℂ → ℝ} (hw : Measurable w) (z₀ : ℂ) (r : ℝ) :
    Measurable (fun x : ℂ => if ‖x - z₀‖ < r then w x else 0) :=
  Measurable.ite (measurableSet_lt (measurable_id.sub measurable_const).norm measurable_const) hw
    measurable_const

/-- The far weight `1_{|x − z₀| ≥ r} w`. -/
theorem bpz_measurable_farPart {w : ℂ → ℝ} (hw : Measurable w) (z₀ : ℂ) (r : ℝ) :
    Measurable (fun x : ℂ => if r ≤ ‖x - z₀‖ then w x else 0) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_id.sub measurable_const).norm) hw
    measurable_const

theorem bpz_nearPart_nonneg {w : ℂ → ℝ} (hw0 : ∀ x, 0 ≤ w x) (z₀ : ℂ) (r : ℝ) (x : ℂ) :
    0 ≤ (if ‖x - z₀‖ < r then w x else 0) := by
  split_ifs
  · exact hw0 x
  · exact le_rfl


/-! ### Integrability of the integrands -/

/-- Integrability of `v • D_z (|x − z|² + ε²)^a` from that of `v |x − z|^{2a−1}`. -/
theorem bpz_integrable_smul_softDeriv {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {v : ℂ → ℝ}
    (hv : Measurable v) (hv0 : ∀ x, 0 ≤ v x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => v x * ‖x - z‖ ^ (2 * a - 1)) m) :
    Integrable (fun x => v x • bpzSoftDeriv a ε x z) m := by
  refine Integrable.mono' (hint.const_mul (2 * a))
    (bpz_stronglyMeasurable_softDeriv a ε z hv).aestronglyMeasurable ?_
  filter_upwards [bpz_ae_ne_of_atom hz] with x hx
  rw [norm_smul, Real.norm_of_nonneg (hv0 x)]
  calc v x * ‖bpzSoftDeriv a ε x z‖ ≤ v x * (2 * a * ‖x - z‖ ^ (2 * a - 1)) :=
        mul_le_mul_of_nonneg_left (norm_bpzSoftDeriv_le_uniform ha ha1 hx) (hv0 x)
    _ = 2 * a * (v x * ‖x - z‖ ^ (2 * a - 1)) := by ring

/-- Integrability of `v • D_z² (|x − z|² + ε²)^a` from that of `v |x − z|^{2a−2}`. -/
theorem bpz_integrable_smul_softDeriv2 {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {v : ℂ → ℝ}
    (hv : Measurable v) (hv0 : ∀ x, 0 ≤ v x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => v x * ‖x - z‖ ^ (2 * a - 2)) m) :
    Integrable (fun x => v x • bpzSoftDeriv2 a ε x z) m := by
  refine Integrable.mono' (hint.const_mul (4 * a * (1 - a) + 2 * a))
    (bpz_stronglyMeasurable_softDeriv2 a ε z hv).aestronglyMeasurable ?_
  filter_upwards [bpz_ae_ne_of_atom hz] with x hx
  rw [norm_smul, Real.norm_of_nonneg (hv0 x)]
  calc v x * ‖bpzSoftDeriv2 a ε x z‖ ≤
        v x * ((4 * a * (1 - a) + 2 * a) * ‖x - z‖ ^ (2 * a - 2)) :=
        mul_le_mul_of_nonneg_left (norm_bpzSoftDeriv2_le_uniform ha ha1 hx) (hv0 x)
    _ = (4 * a * (1 - a) + 2 * a) * (v x * ‖x - z‖ ^ (2 * a - 2)) := by ring

/-- Integrability of the far part of the first derivative integrand. -/
theorem bpz_integrable_far_smul_softDeriv {a ε : ℝ} (ha : 0 < a) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m) :
    Integrable (fun x => (if r ≤ ‖x - z₀‖ then w x else 0) • bpzSoftDeriv a ε x z) m := by
  refine Integrable.mono' (hintz.const_mul (4 * a / r))
    (bpz_stronglyMeasurable_softDeriv a ε z (bpz_measurable_farPart hw z₀ r)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  refine bpz_norm_ite_smul_le (E := ℂ →L[ℝ] ℝ) hw0 (by positivity)
    (Real.rpow_nonneg (bpzSoft_normSq_add_nonneg _ _) a) fun hx => ?_
  have h := norm_bpzSoftDeriv_le_far (ε := ε) ha (half_pos hr) (bpzSoft_half_le_norm_sub hx hz)
  have e : 2 * a / (r / 2) = 4 * a / r := by field_simp; ring
  rwa [e] at h

/-- Integrability of the far part of the second derivative integrand. -/
theorem bpz_integrable_far_smul_softDeriv2 {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m) :
    Integrable (fun x => (if r ≤ ‖x - z₀‖ then w x else 0) • bpzSoftDeriv2 a ε x z) m := by
  have hc : 0 ≤ 4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by
    have : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    positivity
  refine Integrable.mono' (hintz.const_mul (4 * (4 * a * (1 - a) + 2 * a) / r ^ 2))
    (bpz_stronglyMeasurable_softDeriv2 a ε z
      (bpz_measurable_farPart hw z₀ r)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  refine bpz_norm_ite_smul_le (E := ℂ →L[ℝ] ℂ →L[ℝ] ℝ) hw0 hc
    (Real.rpow_nonneg (bpzSoft_normSq_add_nonneg _ _) a) fun hx => ?_
  have h := norm_bpzSoftDeriv2_le_far (ε := ε) ha ha1 (half_pos hr)
    (bpzSoft_half_le_norm_sub hx hz)
  have e : (4 * a * (1 - a) + 2 * a) / (r / 2) ^ 2 =
      4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by field_simp; ring
  rwa [e] at h

/-! ### The decomposition -/

/-- The first derivative mass is the sum of its near and far parts. -/
theorem bpzSoftMassDeriv_eq_near_add_far {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2) (hzm : m {z} = 0)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m)
    (hn : Integrable (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1)) m) :
    bpzSoftMassDeriv a ε w m z =
      bpzSoftMassDeriv a ε (fun x => if ‖x - z₀‖ < r then w x else 0) m z +
        bpzSoftMassDeriv a ε (fun x => if r ≤ ‖x - z₀‖ then w x else 0) m z := by
  have h1 := bpz_integrable_smul_softDeriv (ε := ε) ha ha1 (bpz_measurable_nearPart hw z₀ r)
    (bpz_nearPart_nonneg hw0 z₀ r) hzm hn
  have h2 := bpz_integrable_far_smul_softDeriv (ε := ε) ha hw hw0 hr hz hintz
  unfold bpzSoftMassDeriv
  rw [← integral_add h1 h2]
  congr 1
  funext x
  rw [← add_smul]
  congr 1
  by_cases hx : ‖x - z₀‖ < r
  · rw [ite_eq_left hx, ite_eq_right (not_le.mpr hx), add_zero]
  · rw [ite_eq_right hx, ite_eq_left (not_lt.mp hx), zero_add]

/-- The second derivative mass is the sum of its near and far parts. -/
theorem bpzSoftMassDeriv2_eq_near_add_far {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2) (hzm : m {z} = 0)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m)
    (hn : Integrable (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 2)) m) :
    bpzSoftMassDeriv2 a ε w m z =
      bpzSoftMassDeriv2 a ε (fun x => if ‖x - z₀‖ < r then w x else 0) m z +
        bpzSoftMassDeriv2 a ε (fun x => if r ≤ ‖x - z₀‖ then w x else 0) m z := by
  have h1 := bpz_integrable_smul_softDeriv2 (ε := ε) ha ha1 (bpz_measurable_nearPart hw z₀ r)
    (bpz_nearPart_nonneg hw0 z₀ r) hzm hn
  have h2 := bpz_integrable_far_smul_softDeriv2 (ε := ε) ha ha1 hw hw0 hr hz hintz
  unfold bpzSoftMassDeriv2
  rw [← integral_add h1 h2]
  congr 1
  funext x
  rw [← add_smul]
  congr 1
  by_cases hx : ‖x - z₀‖ < r
  · rw [ite_eq_left hx, ite_eq_right (not_le.mpr hx), add_zero]
  · rw [ite_eq_right hx, ite_eq_left (not_lt.mp hx), zero_add]

/-- The near integral of `|x − z|^{2a}` is at most the softened mass. -/
theorem bpz_integral_near_le_softMass {a ε : ℝ} (ha : 0 ≤ a) {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ}
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m) :
    Integrable (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a)) m ∧
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a) ∂m ≤
        bpzSoftMassReal a ε w m z := by
  have hpt : ∀ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a) ≤
      (Complex.normSq (x - z) + ε ^ 2) ^ a * w x := by
    intro x
    have h1 : ‖x - z‖ ^ (2 * a) ≤ (Complex.normSq (x - z) + ε ^ 2) ^ a := by
      rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
      exact Real.rpow_le_rpow (sq_nonneg _) (bpzSoft_norm_sq_le_base ε x z) ha
    have h2 : (if ‖x - z₀‖ < r then w x else 0) ≤ w x := by
      split_ifs
      · exact le_rfl
      · exact hw0 x
    calc (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a)
        ≤ w x * (Complex.normSq (x - z) + ε ^ 2) ^ a :=
          mul_le_mul h2 h1 (Real.rpow_nonneg (norm_nonneg _) _) (hw0 x)
      _ = (Complex.normSq (x - z) + ε ^ 2) ^ a * w x := mul_comm _ _
  have hnn : ∀ x, 0 ≤ (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a) := fun x =>
    mul_nonneg (bpz_nearPart_nonneg hw0 z₀ r x) (Real.rpow_nonneg (norm_nonneg _) _)
  have hint : Integrable (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a)) m :=
    Integrable.mono' hintz
      ((bpz_measurable_nearPart hw z₀ r).mul
        ((measurable_id.sub measurable_const).norm.pow_const _)).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hnn x)]; exact hpt x)
  exact ⟨hint, integral_mono hint hintz hpt⟩

/-! ### Differences between the moment fields and their far parts -/

/-- The first moment field differs from its far part by the near part. -/
theorem bpz_mom1_sub_le {s J u : ℝ} (hs : 0 ≤ s) (hJ : 0 < J) {L Ln Lf : ℂ →L[ℝ] ℝ}
    (hL : L = Ln + Lf) (hu : ‖Ln‖ ≤ u) :
    ‖(-s * J ^ (-s - 1)) • L - (-s * J ^ (-s - 1)) • Lf‖ ≤ s * (J ^ (-s - 1) * u) := by
  have hJs : 0 ≤ J ^ (-s - 1) := Real.rpow_nonneg hJ.le _
  rw [hL, smul_add, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg hs, abs_of_nonneg hJs]
  calc s * J ^ (-s - 1) * ‖Ln‖ ≤ s * J ^ (-s - 1) * u :=
        mul_le_mul_of_nonneg_left hu (mul_nonneg hs hJs)
    _ = s * (J ^ (-s - 1) * u) := by ring

/-- The rank-one bilinear forms of two functionals differ by at most
`‖L − L'‖ (‖L‖ + ‖L'‖)`. -/
theorem bpz_norm_smulRight_sub_le (L L' : ℂ →L[ℝ] ℝ) :
    ‖L.smulRight L - L'.smulRight L'‖ ≤ ‖L - L'‖ * (‖L‖ + ‖L'‖) := by
  have e : L.smulRight L - L'.smulRight L' = (L - L').smulRight L + L'.smulRight (L - L') := by
    ext h k
    simp only [sub_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
      add_apply]
    ring
  rw [e]
  calc ‖(L - L').smulRight L + L'.smulRight (L - L')‖
      ≤ ‖(L - L').smulRight L‖ + ‖L'.smulRight (L - L')‖ := norm_add_le _ _
    _ = ‖L - L'‖ * ‖L‖ + ‖L'‖ * ‖L - L'‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply]
    _ = ‖L - L'‖ * (‖L‖ + ‖L'‖) := by ring

/-- The second moment field differs from its far part by terms controlled by the near part. -/
theorem bpz_mom2_sub_le {s J u t v A : ℝ} (hs : 0 ≤ s) (hJ : 0 < J)
    {L Ln Lf : ℂ →L[ℝ] ℝ} {B Bn Bf : ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
    (hL : L = Ln + Lf) (hB : B = Bn + Bf) (hu : ‖Ln‖ ≤ u) (hLf : ‖Lf‖ ≤ A * J)
    (hut : u ^ 2 ≤ J * t) (hv : ‖Bn‖ ≤ v) :
    ‖((s * (s + 1) * J ^ (-s - 2)) • L.smulRight L + (-s * J ^ (-s - 1)) • B) -
      ((s * (s + 1) * J ^ (-s - 2)) • Lf.smulRight Lf + (-s * J ^ (-s - 1)) • Bf)‖ ≤
      s * (s + 1) * (J ^ (-s - 1) * t) + 2 * s * (s + 1) * A * (J ^ (-s - 1) * u) +
        s * (J ^ (-s - 1) * v) := by
  have hu0 : 0 ≤ u := (norm_nonneg _).trans hu
  have hJ2 : 0 ≤ J ^ (-s - 2) := Real.rpow_nonneg hJ.le _
  have hJ1 : 0 ≤ J ^ (-s - 1) := Real.rpow_nonneg hJ.le _
  have hc2 : 0 ≤ s * (s + 1) * J ^ (-s - 2) := by
    have : 0 ≤ s + 1 := by linarith
    positivity
  have hJJ : J ^ (-s - 2) * J = J ^ (-s - 1) := by
    rw [show -s - 2 = (-s - 1) - 1 by ring]
    exact bpzRpow_pred_mul hJ _
  have e : ((s * (s + 1) * J ^ (-s - 2)) • L.smulRight L + (-s * J ^ (-s - 1)) • B) -
      ((s * (s + 1) * J ^ (-s - 2)) • Lf.smulRight Lf + (-s * J ^ (-s - 1)) • Bf) =
      (s * (s + 1) * J ^ (-s - 2)) • (L.smulRight L - Lf.smulRight Lf) +
        (-s * J ^ (-s - 1)) • Bn := by
    rw [hB, smul_sub, smul_add]
    abel
  have hLL : ‖L.smulRight L - Lf.smulRight Lf‖ ≤ u * (u + 2 * (A * J)) := by
    refine (bpz_norm_smulRight_sub_le L Lf).trans ?_
    have hsub : L - Lf = Ln := by rw [hL, add_sub_cancel_right]
    have hLn : ‖L‖ ≤ u + A * J := by
      rw [hL]; exact (norm_add_le _ _).trans (add_le_add hu hLf)
    rw [hsub]
    calc ‖Ln‖ * (‖L‖ + ‖Lf‖) ≤ u * ((u + A * J) + A * J) :=
          mul_le_mul hu (add_le_add hLn hLf) (by positivity) hu0
      _ = u * (u + 2 * (A * J)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hc2, Real.norm_eq_abs (-s * _), abs_mul,
    abs_neg, abs_of_nonneg hs, abs_of_nonneg hJ1]
  have h1 : s * (s + 1) * J ^ (-s - 2) * ‖L.smulRight L - Lf.smulRight Lf‖ ≤
      s * (s + 1) * (J ^ (-s - 1) * t) + 2 * s * (s + 1) * A * (J ^ (-s - 1) * u) := by
    calc s * (s + 1) * J ^ (-s - 2) * ‖L.smulRight L - Lf.smulRight Lf‖
        ≤ s * (s + 1) * J ^ (-s - 2) * (u * (u + 2 * (A * J))) :=
          mul_le_mul_of_nonneg_left hLL hc2
      _ = s * (s + 1) * J ^ (-s - 2) * u ^ 2 +
          2 * s * (s + 1) * A * (J ^ (-s - 2) * J * u) := by ring
      _ ≤ s * (s + 1) * J ^ (-s - 2) * (J * t) +
          2 * s * (s + 1) * A * (J ^ (-s - 2) * J * u) := by
          gcongr
      _ = s * (s + 1) * (J ^ (-s - 2) * J * t) +
          2 * s * (s + 1) * A * (J ^ (-s - 2) * J * u) := by ring
      _ = s * (s + 1) * (J ^ (-s - 1) * t) + 2 * s * (s + 1) * A * (J ^ (-s - 1) * u) := by
          rw [hJJ]
  have h2 : s * J ^ (-s - 1) * ‖Bn‖ ≤ s * (J ^ (-s - 1) * v) := by
    calc s * J ^ (-s - 1) * ‖Bn‖ ≤ s * J ^ (-s - 1) * v :=
          mul_le_mul_of_nonneg_left hv (mul_nonneg hs hJ1)
      _ = s * (J ^ (-s - 1) * v) := by ring
  linarith

end DOZZ.Proofs
