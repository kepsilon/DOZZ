/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.SmallPower

/-! A vanishing small-power error for adding a subcritical mass. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Extended-real version of the fixed-order positive/inverse moment error bound. -/
theorem lastone_ennreal_add_rpow_le (a b : ℝ≥0∞) (p q : ℝ)
    (ha0 : a ≠ 0) (haT : a ≠ ⊤) (hbT : b ≠ ⊤)
    (hp : 0 < p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    (a + b) ^ p ≤ a ^ p + ENNReal.ofReal (p / q) *
      (1 + 2 * b ^ (2 * q) + a ^ (-2 * q)) := by
  have hq : 0 < q := hp.trans_le hpq
  have hAp : a ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le haT
  have hBp : b ^ (2 * q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hbT
  have hAi : a ^ (-2 * q) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero ha0 haT
  have h2B : (2 : ℝ≥0∞) * b ^ (2 * q) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hBp
  have hK : 1 + 2 * b ^ (2 * q) + a ^ (-2 * q) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, h2B⟩, hAi⟩
  have hE : ENNReal.ofReal (p / q) * (1 + 2 * b ^ (2 * q) + a ^ (-2 * q)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  have hsum := ENNReal.add_ne_top.mpr ⟨haT, hbT⟩
  apply (ENNReal.toReal_le_toReal (ENNReal.rpow_ne_top_of_nonneg hp.le hsum)
    (ENNReal.add_ne_top.mpr ⟨hAp, hE⟩)).mp
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_add haT hbT,
    ENNReal.toReal_add hAp hE, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_pos hp hq).le,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, h2B⟩) hAi,
    ENNReal.toReal_add ENNReal.one_ne_top h2B]
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ← ENNReal.toReal_rpow]
  have h := lastone_rpow_add_increment_le_moments a.toReal b.toReal p q
    (ENNReal.toReal_pos ha0 haT) ENNReal.toReal_nonneg hp hpq hq1
  linarith

/-- Adding a mass with a fixed positive moment preserves a critical small-power limit when
the retained mass has a fixed inverse moment. The error is `O(e)`, rather than order one. -/
theorem lastone_addition_smallPower_limit
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → ℝ≥0∞) (l : Filter ι) (e : ι → ℝ)
    (q L : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (Ca Cb : ℝ≥0∞) (hCa : Ca < ⊤) (hCb : Cb < ⊤)
    (he : Tendsto e l (𝓝 0)) (hepos : ∀ᶠ i in l, 0 < e i)
    (hA : ∀ᶠ i in l, AEMeasurable (A i) P)
    (hB : ∀ᶠ i in l, AEMeasurable (B i) P)
    (hfinite : ∀ᶠ i in l, ∀ᵐ ω ∂P, A i ω ≠ 0 ∧ A i ω ≠ ⊤ ∧ B i ω ≠ ⊤)
    (hAmoment : ∀ᶠ i in l, (∫⁻ ω, A i ω ^ e i ∂P) < ⊤)
    (haBound : ∀ᶠ i in l, ∫⁻ ω, A i ω ^ (-2 * q) ∂P ≤ Ca)
    (hbBound : ∀ᶠ i in l, ∫⁻ ω, B i ω ^ (2 * q) ∂P ≤ Cb)
    (hlim : Tendsto (fun i => (∫⁻ ω, A i ω ^ e i ∂P).toReal) l (𝓝 L)) :
    Tendsto (fun i => (∫⁻ ω, (A i ω + B i ω) ^ e i ∂P).toReal) l (𝓝 L) := by
  let K : ℝ≥0∞ := 1 + 2 * Cb + Ca
  have hK : K ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (by norm_num) hCb.ne⟩, hCa.ne⟩
  have hsmall := he.eventually (eventually_le_nhds hq)
  have hbounds : ∀ᶠ i in l,
      (∫⁻ ω, A i ω ^ e i ∂P).toReal ≤ (∫⁻ ω, (A i ω + B i ω) ^ e i ∂P).toReal ∧
      (∫⁻ ω, (A i ω + B i ω) ^ e i ∂P).toReal ≤
        (∫⁻ ω, A i ω ^ e i ∂P).toReal + e i / q * K.toReal := by
    filter_upwards [hepos, hsmall, hA, hB, hfinite, hAmoment, haBound, hbBound]
      with i hpi hpq hAi hBi hfi hmi hai hbi
    have hpowA (p : ℝ) : AEMeasurable (fun ω => A i ω ^ p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hAi
    have hpowB (p : ℝ) : AEMeasurable (fun ω => B i ω ^ p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hBi
    have hcombined : AEMeasurable (fun ω => 1 + 2 * B i ω ^ (2 * q)) P :=
      aemeasurable_const.add ((hpowB (2 * q)).const_mul 2)
    have hupp : (∫⁻ ω, (A i ω + B i ω) ^ e i ∂P) ≤
        (∫⁻ ω, A i ω ^ e i ∂P) + ENNReal.ofReal (e i / q) * K := by
      calc
        _ ≤ ∫⁻ ω, A i ω ^ e i + ENNReal.ofReal (e i / q) *
            (1 + 2 * B i ω ^ (2 * q) + A i ω ^ (-2 * q)) ∂P :=
          lintegral_mono_ae (hfi.mono fun ω hω => lastone_ennreal_add_rpow_le _ _ _ _
            hω.1 hω.2.1 hω.2.2 hpi hpq hq1)
        _ = (∫⁻ ω, A i ω ^ e i ∂P) + ENNReal.ofReal (e i / q) *
            (1 + 2 * (∫⁻ ω, B i ω ^ (2 * q) ∂P) + ∫⁻ ω, A i ω ^ (-2 * q) ∂P) := by
          rw [lintegral_add_left' (hpowA (e i)), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left' hcombined,
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul'' _ (hpowB (2 * q))]
        _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
          (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hbi)) hai))
    have hEt : ENNReal.ofReal (e i / q) * K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
    have hRt := ENNReal.add_ne_top.mpr ⟨hmi.ne, hEt⟩
    have hSt := ne_top_of_le_ne_top hRt hupp
    have hlow := ENNReal.toReal_mono hSt (lintegral_mono fun ω =>
      ENNReal.rpow_le_rpow (le_add_right le_rfl) hpi.le)
    have huppR := ENNReal.toReal_mono hRt hupp
    rw [ENNReal.toReal_add hmi.ne hEt, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_pos hpi hq).le] at huppR
    exact ⟨hlow, huppR⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim
    (h := fun i => (∫⁻ ω, A i ω ^ e i ∂P).toReal + e i / q * K.toReal)
  · simpa using hlim.add ((he.div_const q).mul_const K.toReal)
  · exact hbounds.mono fun i hi => hi.1
  · exact hbounds.mono fun i hi => hi.2

end DOZZ.Proofs
