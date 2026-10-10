/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftUniform

/-! # Continuity of the softened masses at `ε = 0`, jointly in the root

For `0 < a ≤ 1`, a nonnegative measurable weight `w` and a measure `m` on `ℂ` for which both
`|x − z₀|^{2a} w(x)` and `w(x)` are integrable, we prove by dominated convergence that, along
sequences `εₙ → 0` (with `0 ≤ εₙ ≤ 1`) and `zₙ → z₀`,

* the softened mass `∫ (|x − zₙ|² + εₙ²)^a w(x) dm(x)` converges to the unsoftened mass at `z₀`;
* the derivative masses `∫ w(x) 1_{|x − z₀| ≥ r} D_z^k (|x − zₙ|² + εₙ²)^a dm(x)` of the far part
  of the weight converge to their values at `(0, z₀)`, for `k = 1, 2` and every `r > 0`.

The dominating function comes from the comparison
`(|x − z|² + ε²)^a ≤ 4 (|x − z₀|^{2a} + 1)` for `|z − z₀| ≤ 1` and `0 ≤ ε ≤ 1`, together with the
bound by the softened weight itself of the derivatives away from the root. We also record the
uniform far bounds of the derivative masses by multiples of the softened mass, for roots within
`r / 2` of `z₀`. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-! ### Domination near the base point -/

/-- Domination of the softened weight near the base point. -/
theorem bpzSoft_rpow_le_near {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x z z₀ : ℂ} (hz : ‖z - z₀‖ ≤ 1) :
    (Complex.normSq (x - z) + ε ^ 2) ^ a ≤ 4 * ((Complex.normSq (x - z₀)) ^ a + 1) := by
  have ht0 : 0 ≤ Complex.normSq (x - z₀) := Complex.normSq_nonneg _
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0 hε1
  have hz2 : ‖z - z₀‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have htri : ‖x - z‖ ≤ ‖x - z₀‖ + ‖z - z₀‖ := by
    calc ‖x - z‖ = ‖(x - z₀) - (z - z₀)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖x - z₀‖ + ‖z - z₀‖ := norm_sub_le _ _
  have hsq : ‖x - z‖ ^ 2 ≤ 2 * ‖x - z₀‖ ^ 2 + 2 * ‖z - z₀‖ ^ 2 := by
    nlinarith [norm_nonneg (x - z), norm_nonneg (x - z₀), norm_nonneg (z - z₀),
      sq_nonneg (‖x - z₀‖ - ‖z - z₀‖)]
  have hbase : Complex.normSq (x - z) + ε ^ 2 ≤ 3 * (Complex.normSq (x - z₀) + 1) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    linarith [sq_nonneg ‖x - z₀‖]
  have hN0 : 0 ≤ Complex.normSq (x - z) + ε ^ 2 := bpzSoft_normSq_add_nonneg ε _
  have h3 : (3 : ℝ) ^ a ≤ 3 := by
    calc (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 3 := Real.rpow_one 3
  have h1 : (Complex.normSq (x - z₀) + 1) ^ a ≤ Complex.normSq (x - z₀) ^ a + 1 := by
    have h := Real.rpow_add_le_add_rpow ht0 zero_le_one ha.le ha1
    rwa [Real.one_rpow] at h
  have hP : 0 ≤ Complex.normSq (x - z₀) ^ a + 1 := by positivity
  calc (Complex.normSq (x - z) + ε ^ 2) ^ a
      ≤ (3 * (Complex.normSq (x - z₀) + 1)) ^ a := Real.rpow_le_rpow hN0 hbase ha.le
    _ = 3 ^ a * (Complex.normSq (x - z₀) + 1) ^ a := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 3 * (Complex.normSq (x - z₀) ^ a + 1) := by
        gcongr
    _ ≤ 4 * (Complex.normSq (x - z₀) ^ a + 1) := by linarith

/-- Domination of the softened weight times `w` near the base point. -/
theorem bpzSoft_rpow_mul_le_near {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {w : ℂ → ℝ} (hw0 : ∀ x, 0 ≤ w x) {x z z₀ : ℂ} (hz : ‖z - z₀‖ ≤ 1) :
    (Complex.normSq (x - z) + ε ^ 2) ^ a * w x ≤
      4 * ((Complex.normSq (x - z₀)) ^ a * w x) + 4 * w x :=
  calc (Complex.normSq (x - z) + ε ^ 2) ^ a * w x
      ≤ (4 * ((Complex.normSq (x - z₀)) ^ a + 1)) * w x :=
        mul_le_mul_of_nonneg_right (bpzSoft_rpow_le_near ha ha1 hε0 hε1 hz) (hw0 x)
    _ = 4 * ((Complex.normSq (x - z₀)) ^ a * w x) + 4 * w x := by ring

/-- The softened mass is finite at every root within distance `1` of `z₀`, uniformly in the
softening `0 ≤ ε ≤ 1`. -/
theorem bpzSoft_integrable_near {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ}
    {z₀ : ℂ} (hint : Integrable (fun x => (Complex.normSq (x - z₀)) ^ a * w x) m)
    (hintw : Integrable w m) {z : ℂ} (hz : ‖z - z₀‖ ≤ 1) :
    Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m := by
  refine Integrable.mono' ((hint.const_mul 4).add (hintw.const_mul 4))
    ((bpzSoft_measurable_rpow a ε z).mul hw).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hnn : 0 ≤ (Complex.normSq (x - z) + ε ^ 2) ^ a * w x :=
    mul_nonneg (Real.rpow_nonneg (bpzSoft_normSq_add_nonneg _ _) a) (hw0 x)
  rw [Real.norm_of_nonneg hnn]
  exact bpzSoft_rpow_mul_le_near ha ha1 hε0 hε1 hw0 hz

/-- If `x` is at distance at least `r` from `z₀` and the root `z` is within `r / 2` of `z₀`, then
`x` is at distance at least `r / 2` from `z`. -/
theorem bpzSoft_half_le_norm_sub {r : ℝ} {x z z₀ : ℂ} (hx : r ≤ ‖x - z₀‖)
    (hz : ‖z - z₀‖ ≤ r / 2) : r / 2 ≤ ‖x - z‖ := by
  have h : ‖x - z₀‖ ≤ ‖x - z‖ + ‖z - z₀‖ := by
    calc ‖x - z₀‖ = ‖(x - z) + (z - z₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - z‖ + ‖z - z₀‖ := norm_add_le _ _
  linarith

/-- The softened base `|x − z₀|² + ε²` is positive at points `x` at distance at least `r > 0`
from `z₀`. -/
theorem bpzSoft_base_pos_of_le_norm {r ε : ℝ} (hr : 0 < r) {x z₀ : ℂ} (hx : r ≤ ‖x - z₀‖) :
    0 < Complex.normSq (x - z₀) + ε ^ 2 :=
  lt_of_lt_of_le (pow_pos (lt_of_lt_of_le hr hx) 2) (bpzSoft_norm_sq_le_base ε x z₀)

/-! ### Measurability in the integration variable -/

/-- The first derivative of the softened factor is a.e. strongly measurable in `x` (for every
`ε`, including `ε = 0`). -/
theorem bpzSoftDeriv_aestronglyMeasurable (a ε : ℝ) (z : ℂ) (m : Measure ℂ) :
    AEStronglyMeasurable (fun x : ℂ => bpzSoftDeriv a ε x z) m := by
  have hbase : Measurable (fun x : ℂ => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  have hc : Measurable
      (fun x : ℂ => -2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)) :=
    (hbase.pow_const (a - 1)).const_mul _
  have hL : Continuous (fun x : ℂ => innerSL ℝ (x - z)) :=
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  exact hc.aestronglyMeasurable.smul hL.aestronglyMeasurable

/-- The second derivative of the softened factor is a.e. strongly measurable in `x` (for every
`ε`, including `ε = 0`). -/
theorem bpzSoftDeriv2_aestronglyMeasurable (a ε : ℝ) (z : ℂ) (m : Measure ℂ) :
    AEStronglyMeasurable (fun x : ℂ => bpzSoftDeriv2 a ε x z) m := by
  have hbase : Measurable (fun x : ℂ => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  have hc2 : Measurable
      (fun x : ℂ => 4 * a * (a - 1) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 2)) :=
    (hbase.pow_const (a - 2)).const_mul _
  have hc1 : Measurable
      (fun x : ℂ => 2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)) :=
    (hbase.pow_const (a - 1)).const_mul _
  have hL : Continuous (fun x : ℂ => innerSL ℝ (x - z)) :=
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  have hS : Continuous
      (fun x : ℂ => (innerSL ℝ (x - z)).smulRight (innerSL ℝ (x - z))) :=
    (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] ℝ)).continuous₂.comp₂ hL hL
  exact (hc2.aestronglyMeasurable.smul hS.aestronglyMeasurable).add
    (hc1.aestronglyMeasurable.smul aestronglyMeasurable_const)

/-! ### The mass is continuous at `ε = 0` -/

/-- The softened mass is continuous at `ε = 0` jointly in the root. -/
theorem bpz_tendsto_softMassReal {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀)) ^ a * w x) m)
    (hintw : Integrable w m) {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => bpzSoftMassReal a (εs n) w m (zs n)) atTop
      (𝓝 (bpzSoftMassReal a 0 w m z₀)) := by
  have hnear : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually (ge_mem_nhds one_pos)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => 4 * ((Complex.normSq (x - z₀)) ^ a * w x) + 4 * w x) ?_ ?_
    ((hint.const_mul 4).add (hintw.const_mul 4)) ?_
  · exact Eventually.of_forall fun n =>
      ((bpzSoft_measurable_rpow a (εs n) (zs n)).mul hw).aestronglyMeasurable
  · filter_upwards [hnear] with n hn
    refine Eventually.of_forall fun x => ?_
    have hnn : 0 ≤ (Complex.normSq (x - zs n) + εs n ^ 2) ^ a * w x :=
      mul_nonneg (Real.rpow_nonneg (bpzSoft_normSq_add_nonneg _ _) a) (hw0 x)
    rw [Real.norm_of_nonneg hnn]
    exact bpzSoft_rpow_mul_le_near ha ha1 (hε0 n) (hε1 n) hw0 hn
  · refine Eventually.of_forall fun x => ?_
    have hbase : ContinuousAt
        (fun p : ℝ × ℂ => Complex.normSq (x - p.2) + p.1 ^ 2) (0, z₀) := by fun_prop
    have hc : ContinuousAt
        (fun p : ℝ × ℂ => (Complex.normSq (x - p.2) + p.1 ^ 2) ^ a) (0, z₀) :=
      hbase.rpow_const (Or.inr ha.le)
    exact (hc.tendsto.comp (hε.prodMk_nhds hz)).mul_const (w x)

/-! ### The far parts of the derivative masses -/

/-- Pointwise bound of the far part of a weighted integrand: if `d` is bounded by `K P` whenever
`‖x − z₀‖ ≥ r`, then `1_{‖x − z₀‖ ≥ r} w(x) • d` is bounded by `K P w(x)`. -/
theorem bpz_norm_ite_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) {r K P : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P) {x z₀ : ℂ} {d : E}
    (hd : r ≤ ‖x - z₀‖ → ‖d‖ ≤ K * P) :
    ‖(if r ≤ ‖x - z₀‖ then w x else 0) • d‖ ≤ K * (P * w x) := by
  have hwx := hw0 x
  by_cases hx : r ≤ ‖x - z₀‖
  · rw [ite_eq_left hx, norm_smul, Real.norm_of_nonneg hwx]
    calc w x * ‖d‖ ≤ w x * (K * P) := mul_le_mul_of_nonneg_left (hd hx) hwx
      _ = K * (P * w x) := by ring
  · rw [ite_eq_right hx, zero_smul, norm_zero]
    positivity

/-- Dominated convergence for the far part of a kernel `D ε x z` which is jointly continuous in
`(ε, z)` at `(0, z₀)` for `‖x − z₀‖ ≥ r`, and bounded there by `K` times the softened weight. -/
theorem bpz_tendsto_integral_far {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a r K : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 < r) (hK : 0 ≤ K) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀)) ^ a * w x) m)
    (hintw : Integrable w m) (D : ℝ → ℂ → ℂ → E)
    (hmeas : ∀ ε z, AEStronglyMeasurable (fun x => D ε x z) m)
    (hcont : ∀ x, r ≤ ‖x - z₀‖ → ContinuousAt (fun p : ℝ × ℂ => D p.1 x p.2) (0, z₀))
    (hbd : ∀ ε x z, r ≤ ‖x - z₀‖ → ‖z - z₀‖ ≤ r / 2 →
      ‖D ε x z‖ ≤ K * (Complex.normSq (x - z) + ε ^ 2) ^ a)
    {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1) (hε : Tendsto εs atTop (𝓝 0))
    {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ x, (if r ≤ ‖x - z₀‖ then w x else 0) • D (εs n) x (zs n) ∂m) atTop
      (𝓝 (∫ x, (if r ≤ ‖x - z₀‖ then w x else 0) • D 0 x z₀ ∂m)) := by
  have hnear : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ min 1 (r / 2) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually
      (ge_mem_nhds (lt_min one_pos (half_pos hr)))
  have hmw : Measurable (fun x : ℂ => if r ≤ ‖x - z₀‖ then w x else 0) := by
    refine Measurable.ite ?_ hw measurable_const
    exact measurableSet_le measurable_const (by fun_prop)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => 4 * K * ((Complex.normSq (x - z₀)) ^ a * w x) + 4 * K * w x) ?_ ?_
    ((hint.const_mul (4 * K)).add (hintw.const_mul (4 * K))) ?_
  · exact Eventually.of_forall fun n => hmw.aestronglyMeasurable.smul (hmeas _ _)
  · filter_upwards [hnear] with n hn
    refine Eventually.of_forall fun x => ?_
    have hN0 : 0 ≤ (Complex.normSq (x - zs n) + εs n ^ 2) ^ a :=
      Real.rpow_nonneg (bpzSoft_normSq_add_nonneg _ _) a
    have h1 := bpz_norm_ite_smul_le (E := E) hw0 (r := r) hK hN0 (x := x) (z₀ := z₀)
      (d := D (εs n) x (zs n))
      (fun hx => hbd (εs n) x (zs n) hx (hn.trans (min_le_right _ _)))
    have h2 := bpzSoft_rpow_mul_le_near ha ha1 (hε0 n) (hε1 n) hw0 (x := x)
      (hn.trans (min_le_left _ _))
    calc ‖(if r ≤ ‖x - z₀‖ then w x else 0) • D (εs n) x (zs n)‖
        ≤ K * ((Complex.normSq (x - zs n) + εs n ^ 2) ^ a * w x) := h1
      _ ≤ K * (4 * ((Complex.normSq (x - z₀)) ^ a * w x) + 4 * w x) :=
          mul_le_mul_of_nonneg_left h2 hK
      _ = 4 * K * ((Complex.normSq (x - z₀)) ^ a * w x) + 4 * K * w x := by ring
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : r ≤ ‖x - z₀‖
    · rw [ite_eq_left hx]
      exact ((hcont x hx).tendsto.comp (hε.prodMk_nhds hz)).const_smul (w x)
    · simp only [ite_eq_right hx, zero_smul]
      exact tendsto_const_nhds

/-- The far part of the first derivative of the softened mass is continuous at `ε = 0` jointly in
the root. -/
theorem bpz_tendsto_softMassDeriv_far {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀)) ^ a * w x) m)
    (hintw : Integrable w m) {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun n => bpzSoftMassDeriv a (εs n)
        ((fun x => if r ≤ ‖x - z₀‖ then w x else 0)) m (zs n)) atTop
      (𝓝 (bpzSoftMassDeriv a 0 (fun x => if r ≤ ‖x - z₀‖ then w x else 0) m z₀)) := by
  refine bpz_tendsto_integral_far (K := 4 * a / r) ha ha1 hr (by positivity) hw hw0 hint hintw
    (fun ε x z => bpzSoftDeriv a ε x z)
    (fun ε z => bpzSoftDeriv_aestronglyMeasurable a ε z m) ?_ ?_ hε0 hε1 hε hz
  · intro x hx
    exact continuousAt_bpzSoftDeriv a x (bpzSoft_base_pos_of_le_norm hr hx)
  · intro ε x z hx hz
    have h := norm_bpzSoftDeriv_le_far (ε := ε) ha (half_pos hr) (bpzSoft_half_le_norm_sub hx hz)
    have e : 2 * a / (r / 2) = 4 * a / r := by field_simp; ring
    rwa [e] at h

/-- The far part of the second derivative of the softened mass is continuous at `ε = 0` jointly in
the root. -/
theorem bpz_tendsto_softMassDeriv2_far {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z₀ : ℂ}
    (hint : Integrable (fun x => (Complex.normSq (x - z₀)) ^ a * w x) m)
    (hintw : Integrable w m) {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun n => bpzSoftMassDeriv2 a (εs n)
        ((fun x => if r ≤ ‖x - z₀‖ then w x else 0)) m (zs n)) atTop
      (𝓝 (bpzSoftMassDeriv2 a 0 (fun x => if r ≤ ‖x - z₀‖ then w x else 0) m z₀)) := by
  have hc : 0 ≤ 4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by
    have : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    positivity
  refine bpz_tendsto_integral_far (K := 4 * (4 * a * (1 - a) + 2 * a) / r ^ 2) ha ha1 hr hc hw hw0
    hint hintw (fun ε x z => bpzSoftDeriv2 a ε x z)
    (fun ε z => bpzSoftDeriv2_aestronglyMeasurable a ε z m) ?_ ?_ hε0 hε1 hε hz
  · intro x hx
    exact continuousAt_bpzSoftDeriv2 a x (bpzSoft_base_pos_of_le_norm hr hx)
  · intro ε x z hx hz
    have h := norm_bpzSoftDeriv2_le_far (ε := ε) ha ha1 (half_pos hr)
      (bpzSoft_half_le_norm_sub hx hz)
    have e : (4 * a * (1 - a) + 2 * a) / (r / 2) ^ 2 =
        4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by field_simp; ring
    rwa [e] at h

/-! ### Uniform far bounds for the derivative masses -/

/-- The norm of the far integral of a kernel bounded by `K` times the softened weight is at most
`K` times the softened mass. -/
theorem bpz_norm_integral_far_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a ε r K : ℝ} (hK : 0 ≤ K) {w : ℂ → ℝ} (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ}
    (D : ℂ → E)
    (hbd : ∀ x, r ≤ ‖x - z₀‖ → ‖D x‖ ≤ K * (Complex.normSq (x - z) + ε ^ 2) ^ a)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m) :
    ‖∫ x, (if r ≤ ‖x - z₀‖ then w x else 0) • D x ∂m‖ ≤
      K * ∫ x, (Complex.normSq (x - z) + ε ^ 2) ^ a * w x ∂m := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hintz.const_mul K) (Eventually.of_forall fun x => ?_)
  exact bpz_norm_ite_smul_le hw0 hK (Real.rpow_nonneg (bpzSoft_normSq_add_nonneg _ _) a)
    (fun hx => hbd x hx)

/-- Uniform far bound for the first derivative mass, for roots within `r / 2` of `z₀`.

The integrability of the softened weight at `z` cannot be dropped: without it `bpzSoftMassReal`
is the junk value `0`, while the derivative mass of the far part may be nonzero. For
`‖z − z₀‖ ≤ 1` and `0 ≤ ε ≤ 1` it follows from `bpzSoft_integrable_near`. -/
theorem norm_bpzSoftMassDeriv_far_le {a ε : ℝ} (ha : 0 < a) {w : ℂ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z - z₀‖ ≤ r / 2)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m) :
    ‖bpzSoftMassDeriv a ε (fun x => if r ≤ ‖x - z₀‖ then w x else 0) m z‖ ≤
      4 * a / r * bpzSoftMassReal a ε w m z := by
  refine bpz_norm_integral_far_le (by positivity) hw0 (fun x => bpzSoftDeriv a ε x z)
    (fun x hx => ?_) hintz
  have h := norm_bpzSoftDeriv_le_far (ε := ε) ha (half_pos hr) (bpzSoft_half_le_norm_sub hx hz)
  have e : 2 * a / (r / 2) = 4 * a / r := by field_simp; ring
  rwa [e] at h

/-- Uniform far bound for the second derivative mass, for roots within `r / 2` of `z₀`.

The integrability of the softened weight at `z` cannot be dropped: without it `bpzSoftMassReal`
is the junk value `0`, while the derivative mass of the far part may be nonzero. For
`‖z − z₀‖ ≤ 1` and `0 ≤ ε ≤ 1` it follows from `bpzSoft_integrable_near`. -/
theorem norm_bpzSoftMassDeriv2_far_le {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2)
    (hintz : Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) m) :
    ‖bpzSoftMassDeriv2 a ε (fun x => if r ≤ ‖x - z₀‖ then w x else 0) m z‖ ≤
      4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 * bpzSoftMassReal a ε w m z := by
  have hc : 0 ≤ 4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by
    have : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    positivity
  refine bpz_norm_integral_far_le hc hw0 (fun x => bpzSoftDeriv2 a ε x z) (fun x hx => ?_) hintz
  have h := norm_bpzSoftDeriv2_le_far (ε := ε) ha ha1 (half_pos hr)
    (bpzSoft_half_le_norm_sub hx hz)
  have e : (4 * a * (1 - a) + 2 * a) / (r / 2) ^ 2 =
      4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by field_simp; ring
  rwa [e] at h

end DOZZ.Proofs
