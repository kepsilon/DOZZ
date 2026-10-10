/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentLimitA

/-! # Moment fields and their near/far bounds in expectation

The moment fields `−s I^{−s−1} DI` and `s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I` of a random
measure, with `I` the softened mass of a weight `w` and the derivatives `DI`, `D²I` of the softened
mass of a weight `v`. For `v = w` these are the derivatives of the moment `E[I^{−s}]`; for `v` the
far part of `w` they are the far parts. Given an integrable lower bound `Y` of the mass, the far
parts are dominated by `Y^{−s}`, and the differences between the fields and their far parts are
bounded in expectation by the near-root moments `E[I^{−s−1} ∫ near |x − z|^{2a−1}]` and
`E[I^{−s−1} ∫ near |x − z|^{2a−2}]`. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

/-- The first moment field `−s I^{−s−1} DI`, with `I` the softened mass of `w` and `DI` the first
derivative mass of `v`. -/
noncomputable def bpzMomField1 (a s ε : ℝ) (w v : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) :
    ℂ →L[ℝ] ℝ :=
  (-s * bpzSoftMassReal a ε w m z ^ (-s - 1)) • bpzSoftMassDeriv a ε v m z

/-- The second moment field `s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I`. -/
noncomputable def bpzMomField2 (a s ε : ℝ) (w v : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (s * (s + 1) * bpzSoftMassReal a ε w m z ^ (-s - 2)) •
      (bpzSoftMassDeriv a ε v m z).smulRight (bpzSoftMassDeriv a ε v m z) +
    (-s * bpzSoftMassReal a ε w m z ^ (-s - 1)) • bpzSoftMassDeriv2 a ε v m z

theorem bpz_stronglyMeasurable_momField1 {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) (a s ε : ℝ) {w v : ℂ → ℝ} (hw : Measurable w) (hv : Measurable v)
    (z : ℂ) : StronglyMeasurable (fun ω => bpzMomField1 a s ε w v (M ω) z) := by
  unfold bpzMomField1
  have hI := (bpz_measurable_softMassReal a ε hw z).comp hMm
  have hD := (bpz_stronglyMeasurable_softMassDeriv a ε hv z).comp_measurable hMm
  exact ((hI.pow_const _).const_mul _).stronglyMeasurable.smul hD

theorem bpz_stronglyMeasurable_momField2 {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) (a s ε : ℝ) {w v : ℂ → ℝ} (hw : Measurable w) (hv : Measurable v)
    (z : ℂ) : StronglyMeasurable (fun ω => bpzMomField2 a s ε w v (M ω) z) := by
  unfold bpzMomField2
  have hI := (bpz_measurable_softMassReal a ε hw z).comp hMm
  have hD := (bpz_stronglyMeasurable_softMassDeriv a ε hv z).comp_measurable hMm
  have hD2 := (bpz_stronglyMeasurable_softMassDeriv2 a ε hv z).comp_measurable hMm
  have hc : Continuous (fun L : ℂ →L[ℝ] ℝ => L.smulRight L) :=
    (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] ℝ)).continuous₂.comp
      (continuous_id.prodMk continuous_id)
  have hS : StronglyMeasurable (fun ω =>
      (bpzSoftMassDeriv a ε v (M ω) z).smulRight (bpzSoftMassDeriv a ε v (M ω) z)) :=
    hc.comp_stronglyMeasurable hD
  exact (((hI.pow_const _).const_mul _).stronglyMeasurable.smul hS).add
    (((hI.pow_const _).const_mul _).stronglyMeasurable.smul hD2)

/-- Expectation bounds for the first moment field and its far part. -/
theorem bpz_momField1_near {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℂ} (hMm : Measurable M) {a s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s)
    {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {z₀ z : ℂ} {r ε : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2) {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hgood : ∀ᵐ ω ∂P, M ω {z} = 0 ∧ 0 < Y ω ∧ Y ω ≤ bpzSoftMassReal a ε w (M ω) z ∧
      Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) (M ω))
    (hnear : ∀ᵐ ω ∂P, Integrable
      (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1)) (M ω))
    {B : ℝ} (hBint : Integrable (fun ω => bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω) P)
    (hB : ∫ ω, bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω ∂P ≤ B) :
    Integrable (fun ω => bpzMomField1 a s ε w w (M ω) z) P ∧
      Integrable (fun ω => bpzMomField1 a s ε w
        (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z) P ∧
      ∫ ω, ‖bpzMomField1 a s ε w w (M ω) z - bpzMomField1 a s ε w
        (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z‖ ∂P ≤ s * (2 * a) * B ∧
      ∀ᵐ ω ∂P, ‖bpzMomField1 a s ε w (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z‖ ≤
        s * (4 * a / r) * Y ω ^ (-s) := by
  set far : ℂ → ℝ := fun x => if r ≤ ‖x - z₀‖ then w x else 0 with hfar
  set N : Ω → ℝ := fun ω => bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
    ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω with hN
  have hF := bpz_stronglyMeasurable_momField1 hMm a s ε hw hw z
  have hG := bpz_stronglyMeasurable_momField1 hMm a s ε hw (bpz_measurable_farPart hw z₀ r) z
  have hpath : ∀ᵐ ω ∂P, ‖bpzMomField1 a s ε w far (M ω) z‖ ≤ s * (4 * a / r) * Y ω ^ (-s) ∧
      ‖bpzMomField1 a s ε w w (M ω) z - bpzMomField1 a s ε w far (M ω) z‖ ≤
        s * (2 * a) * N ω := by
    filter_upwards [hgood, hnear] with ω hω hn
    obtain ⟨hzm, hY, hYI, hintz⟩ := hω
    have hJ : 0 < bpzSoftMassReal a ε w (M ω) z := hY.trans_le hYI
    have hDf : ‖bpzSoftMassDeriv a ε far (M ω) z‖ ≤ 4 * a / r * bpzSoftMassReal a ε w (M ω) z :=
      norm_bpzSoftMassDeriv_far_le ha hw0 hr hz hintz
    refine ⟨norm_bpzMomentField_le hs hY hYI (by positivity) hDf, ?_⟩
    have hdec := bpzSoftMassDeriv_eq_near_add_far (ε := ε) ha ha1 hw hw0 hr hz hzm hintz hn
    have hDn := norm_bpzSoftMassDeriv_le_near (ε := ε) ha ha1 (bpz_nearPart_nonneg hw0 z₀ r)
      hzm hn
    have h := bpz_mom1_sub_le hs hJ hdec hDn
    unfold bpzMomField1
    refine h.trans (le_of_eq ?_)
    simp only [hN]
    rw [show -(s + 1) = -s - 1 by ring]
    ring
  have hGint : Integrable (fun ω => bpzMomField1 a s ε w far (M ω) z) P :=
    Integrable.mono' (hYint.const_mul _) hG.aestronglyMeasurable
      (hpath.mono fun ω h => h.1)
  have hDint : Integrable (fun ω => bpzMomField1 a s ε w w (M ω) z -
      bpzMomField1 a s ε w far (M ω) z) P :=
    Integrable.mono' (hBint.const_mul _) (hF.sub hG).aestronglyMeasurable
      (hpath.mono fun ω h => h.2)
  have hFint : Integrable (fun ω => bpzMomField1 a s ε w w (M ω) z) P := by
    refine Integrable.mono' ((hBint.const_mul (s * (2 * a))).add
      (hYint.const_mul (s * (4 * a / r)))) hF.aestronglyMeasurable ?_
    filter_upwards [hpath] with ω h
    calc ‖bpzMomField1 a s ε w w (M ω) z‖ = ‖(bpzMomField1 a s ε w w (M ω) z -
          bpzMomField1 a s ε w far (M ω) z) + bpzMomField1 a s ε w far (M ω) z‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ s * (2 * a) * N ω + s * (4 * a / r) * Y ω ^ (-s) := add_le_add h.2 h.1
  refine ⟨hFint, hGint, ?_, hpath.mono fun ω h => h.1⟩
  calc ∫ ω, ‖bpzMomField1 a s ε w w (M ω) z - bpzMomField1 a s ε w far (M ω) z‖ ∂P
      ≤ ∫ ω, s * (2 * a) * N ω ∂P :=
        integral_mono_ae hDint.norm (hBint.const_mul _) (hpath.mono fun ω h => h.2)
    _ = s * (2 * a) * ∫ ω, N ω ∂P := integral_const_mul _ _
    _ ≤ s * (2 * a) * B := mul_le_mul_of_nonneg_left hB (by positivity)

/-- Expectation bounds for the second moment field and its far part. -/
theorem bpz_momField2_near {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℂ} (hMm : Measurable M) {a s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s)
    {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {z₀ z : ℂ} {r ε : ℝ} (hr : 0 < r)
    (hz : ‖z - z₀‖ ≤ r / 2) {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hgood : ∀ᵐ ω ∂P, M ω {z} = 0 ∧ 0 < Y ω ∧ Y ω ≤ bpzSoftMassReal a ε w (M ω) z ∧
      Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ a * w x) (M ω))
    (hnear1 : ∀ᵐ ω ∂P, Integrable
      (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1)) (M ω))
    (hnear2 : ∀ᵐ ω ∂P, Integrable
      (fun x => (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 2)) (M ω))
    {B₁ B₂ : ℝ} (hB1int : Integrable (fun ω => bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω) P)
    (hB1 : ∫ ω, bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω ∂P ≤ B₁)
    (hB2int : Integrable (fun ω => bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 2) ∂M ω) P)
    (hB2 : ∫ ω, bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
      ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 2) ∂M ω ∂P ≤ B₂) :
    Integrable (fun ω => bpzMomField2 a s ε w w (M ω) z) P ∧
      Integrable (fun ω => bpzMomField2 a s ε w
        (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z) P ∧
      ∫ ω, ‖bpzMomField2 a s ε w w (M ω) z - bpzMomField2 a s ε w
        (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z‖ ∂P ≤
        (4 * a ^ 2 * s * (s + 1) + s * (4 * a * (1 - a) + 2 * a)) * B₂ +
          16 * a ^ 2 * s * (s + 1) / r * B₁ ∧
      ∀ᵐ ω ∂P, ‖bpzMomField2 a s ε w (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z‖ ≤
        (s * (s + 1) * (4 * a / r) ^ 2 + s * (4 * (4 * a * (1 - a) + 2 * a) / r ^ 2)) *
          Y ω ^ (-s) := by
  set far : ℂ → ℝ := fun x => if r ≤ ‖x - z₀‖ then w x else 0 with hfar
  set K₂ : ℝ := 4 * a * (1 - a) + 2 * a with hK₂
  have hK₂0 : 0 ≤ K₂ := by
    have : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    positivity
  set N₁ : Ω → ℝ := fun ω => bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
    ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω with hN₁
  set N₂ : Ω → ℝ := fun ω => bpzSoftMassReal a ε w (M ω) z ^ (-(s + 1)) *
    ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 2) ∂M ω with hN₂
  have hF := bpz_stronglyMeasurable_momField2 hMm a s ε hw hw z
  have hG := bpz_stronglyMeasurable_momField2 hMm a s ε hw (bpz_measurable_farPart hw z₀ r) z
  have hpath : ∀ᵐ ω ∂P, ‖bpzMomField2 a s ε w far (M ω) z‖ ≤
        (s * (s + 1) * (4 * a / r) ^ 2 + s * (4 * K₂ / r ^ 2)) * Y ω ^ (-s) ∧
      ‖bpzMomField2 a s ε w w (M ω) z - bpzMomField2 a s ε w far (M ω) z‖ ≤
        (4 * a ^ 2 * s * (s + 1) + s * K₂) * N₂ ω + 16 * a ^ 2 * s * (s + 1) / r * N₁ ω := by
    filter_upwards [hgood, hnear1, hnear2] with ω hω hn1 hn2
    obtain ⟨hzm, hY, hYI, hintz⟩ := hω
    have hJ : 0 < bpzSoftMassReal a ε w (M ω) z := hY.trans_le hYI
    have hDf : ‖bpzSoftMassDeriv a ε far (M ω) z‖ ≤ 4 * a / r * bpzSoftMassReal a ε w (M ω) z :=
      norm_bpzSoftMassDeriv_far_le ha hw0 hr hz hintz
    have hD2f : ‖bpzSoftMassDeriv2 a ε far (M ω) z‖ ≤
        4 * K₂ / r ^ 2 * bpzSoftMassReal a ε w (M ω) z :=
      norm_bpzSoftMassDeriv2_far_le ha ha1 hw0 hr hz hintz
    refine ⟨norm_bpzMomentField2_le hs hY hYI (by positivity) hDf hD2f, ?_⟩
    have hdec := bpzSoftMassDeriv_eq_near_add_far (ε := ε) ha ha1 hw hw0 hr hz hzm hintz hn1
    have hdec2 := bpzSoftMassDeriv2_eq_near_add_far (ε := ε) ha ha1 hw hw0 hr hz hzm hintz hn2
    have hDn := norm_bpzSoftMassDeriv_le_near (ε := ε) ha ha1 (bpz_nearPart_nonneg hw0 z₀ r)
      hzm hn1
    have hD2n := norm_bpzSoftMassDeriv2_le_near (ε := ε) ha ha1 (bpz_nearPart_nonneg hw0 z₀ r)
      hzm hn2
    obtain ⟨h0int, h0le⟩ := bpz_integral_near_le_softMass (ε := ε) (z₀ := z₀) (r := r) ha.le hw
      hw0 hintz
    have hCS := bpz_near_cauchySchwarz (bpz_measurable_nearPart hw z₀ r)
      (bpz_nearPart_nonneg hw0 z₀ r) hzm h0int hn2
    set n₁ := ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 1) ∂M ω with hn₁
    set n₂ := ∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a - 2) ∂M ω with hn₂
    have hn₂0 : 0 ≤ n₂ := integral_nonneg fun x =>
      mul_nonneg (bpz_nearPart_nonneg hw0 z₀ r x) (Real.rpow_nonneg (norm_nonneg _) _)
    have hut : (2 * a * n₁) ^ 2 ≤ bpzSoftMassReal a ε w (M ω) z * (4 * a ^ 2 * n₂) := by
      calc (2 * a * n₁) ^ 2 = 4 * a ^ 2 * n₁ ^ 2 := by ring
        _ ≤ 4 * a ^ 2 * ((∫ x, (if ‖x - z₀‖ < r then w x else 0) * ‖x - z‖ ^ (2 * a) ∂M ω) *
            n₂) :=
            mul_le_mul_of_nonneg_left hCS (by positivity)
        _ ≤ 4 * a ^ 2 * (bpzSoftMassReal a ε w (M ω) z * n₂) := by gcongr
        _ = bpzSoftMassReal a ε w (M ω) z * (4 * a ^ 2 * n₂) := by ring
    have h := bpz_mom2_sub_le hs hJ hdec hdec2 hDn hDf hut hD2n
    unfold bpzMomField2
    refine h.trans (le_of_eq ?_)
    simp only [hN₁, hN₂, hK₂]
    rw [← hn₁, ← hn₂, show -(s + 1) = -s - 1 by ring]
    field_simp
    ring
  have hGint : Integrable (fun ω => bpzMomField2 a s ε w far (M ω) z) P :=
    Integrable.mono' (hYint.const_mul _) hG.aestronglyMeasurable
      (hpath.mono fun ω h => h.1)
  have hbint : Integrable (fun ω => (4 * a ^ 2 * s * (s + 1) + s * K₂) * N₂ ω +
      16 * a ^ 2 * s * (s + 1) / r * N₁ ω) P :=
    (hB2int.const_mul _).add (hB1int.const_mul _)
  have hDint : Integrable (fun ω => bpzMomField2 a s ε w w (M ω) z -
      bpzMomField2 a s ε w far (M ω) z) P :=
    Integrable.mono' hbint (hF.sub hG).aestronglyMeasurable (hpath.mono fun ω h => h.2)
  have hFint : Integrable (fun ω => bpzMomField2 a s ε w w (M ω) z) P := by
    refine Integrable.mono' (hbint.add (hYint.const_mul
      (s * (s + 1) * (4 * a / r) ^ 2 + s * (4 * K₂ / r ^ 2)))) hF.aestronglyMeasurable ?_
    filter_upwards [hpath] with ω h
    calc ‖bpzMomField2 a s ε w w (M ω) z‖ = ‖(bpzMomField2 a s ε w w (M ω) z -
          bpzMomField2 a s ε w far (M ω) z) + bpzMomField2 a s ε w far (M ω) z‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h.2 h.1
  refine ⟨hFint, hGint, ?_, hpath.mono fun ω h => h.1⟩
  have hc1 : 0 ≤ 4 * a ^ 2 * s * (s + 1) + s * K₂ := by positivity
  have hc2 : 0 ≤ 16 * a ^ 2 * s * (s + 1) / r := by positivity
  calc ∫ ω, ‖bpzMomField2 a s ε w w (M ω) z - bpzMomField2 a s ε w far (M ω) z‖ ∂P
      ≤ ∫ ω, ((4 * a ^ 2 * s * (s + 1) + s * K₂) * N₂ ω +
          16 * a ^ 2 * s * (s + 1) / r * N₁ ω) ∂P :=
        integral_mono_ae hDint.norm hbint (hpath.mono fun ω h => h.2)
    _ = (4 * a ^ 2 * s * (s + 1) + s * K₂) * ∫ ω, N₂ ω ∂P +
          16 * a ^ 2 * s * (s + 1) / r * ∫ ω, N₁ ω ∂P := by
        rw [integral_add (hB2int.const_mul _) (hB1int.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ (4 * a ^ 2 * s * (s + 1) + s * K₂) * B₂ + 16 * a ^ 2 * s * (s + 1) / r * B₁ := by
        gcongr

end DOZZ.Proofs
