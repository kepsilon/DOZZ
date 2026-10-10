/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.CriticalMoments
public import DOZZ.ShiftEquations.Strip.Remainder

/-! Integrating the critical-mass comparison with a subcritical remainder. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A sum retains finite small moments when one summand has those moments and the other has
one fixed positive moment. -/
theorem lastone_addition_smallPower_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ≥0∞) (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (p t : ℝ) (hp : 0 < p) (hpt : p ≤ t)
    (hAp : ∫⁻ ω, A ω ^ p ∂P < ⊤) (hBt : ∫⁻ ω, B ω ^ t ∂P < ⊤) :
    ∫⁻ ω, (A ω + B ω) ^ p ∂P < ⊤ := by
  have hBp : ∫⁻ ω, B ω ^ p ∂P < ⊤ := by
    calc
      _ ≤ ∫⁻ ω, (1 + B ω ^ t) ∂P :=
        lintegral_mono fun ω => weightedGrid_ennreal_rpow_le_one_add_rpow _ hp hpt
      _ = 1 + ∫⁻ ω, B ω ^ t ∂P := by simp [lintegral_add_left measurable_const]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨by norm_num, hBt⟩
  calc
    _ ≤ ∫⁻ ω, ENNReal.LpAddConst (ENNReal.ofReal p)⁻¹ * (A ω ^ p + B ω ^ p) ∂P :=
      lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ hp.le
    _ = ENNReal.LpAddConst (ENNReal.ofReal p)⁻¹ *
        ((∫⁻ ω, A ω ^ p ∂P) + ∫⁻ ω, B ω ^ p ∂P) := by
      have hsum : AEMeasurable (fun ω => A ω ^ p + B ω ^ p) P :=
        (hA.pow_const p).add (hB.pow_const p)
      rw [lintegral_const_mul'' _ hsum,
        lintegral_add_left' (hA.pow_const p)]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top _)
      (ENNReal.add_lt_top.mpr ⟨hAp, hBp⟩)

/-- A mass squeezed between two constant multiples of a critical mass, up to a fixed
subcritical remainder, has the same critical small-power limit. -/
theorem lastone_mass_comparison_limit
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R C : ι → Ω → ℝ≥0∞) (U : Ω → ℝ≥0∞)
    (hR : ∀ i, AEMeasurable (R i) P) (hU : AEMeasurable U P)
    (l : Filter ι) (e : ι → ℝ) (he : Tendsto e l (𝓝 0))
    (hepos : ∀ᶠ i in l, 0 < e i)
    (k₁ k₂ k₃ : ℝ≥0∞) (hk₁0 : k₁ ≠ 0) (hk₁T : k₁ ≠ ⊤)
    (hk₂0 : k₂ ≠ 0) (hk₂T : k₂ ≠ ⊤) (hk₃T : k₃ ≠ ⊤)
    (q L : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (D : ℝ≥0∞) (hD : D < ⊤)
    (hRi : ∀ᶠ i in l, ∫⁻ ω, R i ω ^ (-2 * q) ∂P ≤ D)
    (hUp : ∫⁻ ω, U ω ^ (2 * q) ∂P < ⊤)
    (hRp : ∀ᶠ i in l, ∫⁻ ω, R i ω ^ e i ∂P < ⊤)
    (hbounds : ∀ᶠ i in l, ∀ᵐ ω ∂P,
      k₁ * R i ω ≤ C i ω ∧ C i ω ≤ k₂ * R i ω + k₃ * U ω)
    (hlim : Tendsto (fun i => (∫⁻ ω, R i ω ^ e i ∂P).toReal) l (𝓝 L)) :
    Tendsto (fun i => (∫⁻ ω, C i ω ^ e i ∂P).toReal) l (𝓝 L) := by
  let A : ι → Ω → ℝ≥0∞ := fun i ω => k₂ * R i ω
  let B : ι → Ω → ℝ≥0∞ := fun _ ω => k₃ * U ω
  have hA (i) : AEMeasurable (A i) P := aemeasurable_const.mul (hR i)
  have hB (i) : AEMeasurable (B i) P := aemeasurable_const.mul hU
  have hAi : ∀ᶠ i in l, ∫⁻ ω, A i ω ^ (-2 * q) ∂P ≤ k₂ ^ (-2 * q) * D := by
    filter_upwards [hRi] with i hi
    have hmul : ∀ ω, A i ω ^ (-2 * q) = k₂ ^ (-2 * q) * R i ω ^ (-2 * q) := by
      intro ω
      simp only [A, ENNReal.mul_rpow_eq_ite, hk₂0, hk₂T, false_and, false_or, ite_false]
    rw [lintegral_congr hmul, lintegral_const_mul'' _ ((hR i).pow_const _)]
    exact mul_le_mul' le_rfl hi
  have hAit : k₂ ^ (-2 * q) * D < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_ne_top_of_ne_zero hk₂0 hk₂T).lt_top hD
  have hBp (i) : ∫⁻ ω, B i ω ^ (2 * q) ∂P < ⊤ :=
    lintegral_const_mul_rpow_lt_top hU hk₃T (by positivity) hUp
  have hAp : ∀ᶠ i in l, ∫⁻ ω, A i ω ^ e i ∂P < ⊤ := by
    filter_upwards [hRp, hepos] with i hi hp
    exact lintegral_const_mul_rpow_lt_top (hR i) hk₂T hp hi
  have hfinite : ∀ᶠ i in l, ∀ᵐ ω ∂P,
      A i ω ≠ 0 ∧ A i ω ≠ ⊤ ∧ B i ω ≠ ⊤ := by
    filter_upwards [hAi, hAp, hepos] with i hi hp hep
    have hai := ae_lt_top' ((hA i).pow_const _) (hi.trans_lt hAit).ne
    have hap := ae_lt_top' ((hA i).pow_const _) hp.ne
    have hbp := ae_lt_top' ((hB i).pow_const _) (hBp i).ne
    filter_upwards [hai, hap, hbp] with ω hωi hωp hωb
    refine ⟨?_, (ENNReal.rpow_lt_top_iff_of_pos hep).mp hωp |>.ne,
      (ENNReal.rpow_lt_top_iff_of_pos (by positivity : 0 < 2 * q)).mp hωb |>.ne⟩
    intro h0
    rw [h0, ENNReal.zero_rpow_of_neg (by linarith)] at hωi
    exact (lt_irrefl _ hωi)
  have hAlim := lastone_scale_smallPower_limit P R hR l e he k₂ hk₂0 hk₂T L hlim
  have hsumlim := lastone_addition_smallPower_limit P A B l e q L hq hq1
    (k₂ ^ (-2 * q) * D) (∫⁻ ω, (k₃ * U ω) ^ (2 * q) ∂P)
    hAit (lintegral_const_mul_rpow_lt_top hU hk₃T (by positivity) hUp) he hepos (Eventually.of_forall hA) (Eventually.of_forall hB)
    hfinite hAp hAi (Eventually.of_forall fun _ => le_rfl) hAlim
  have hlowlim := lastone_scale_smallPower_limit P R hR l e he k₁ hk₁0 hk₁T L hlim
  have hsmall := he.eventually (eventually_le_nhds (by positivity : 0 < 2 * q))
  have hrealbounds : ∀ᶠ i in l,
      (∫⁻ ω, (k₁ * R i ω) ^ e i ∂P).toReal ≤ (∫⁻ ω, C i ω ^ e i ∂P).toReal ∧
      (∫⁻ ω, C i ω ^ e i ∂P).toReal ≤ (∫⁻ ω, (A i ω + B i ω) ^ e i ∂P).toReal := by
    filter_upwards [hbounds, hAp, hepos, hsmall] with i hi hp hep hpeq
    have hsumfin := lastone_addition_smallPower_finite P (A i) (B i) (hA i) (hB i)
      (e i) (2 * q) hep hpeq hp (hBp i)
    have hupper := lintegral_mono_ae (hi.mono fun ω hω => ENNReal.rpow_le_rpow hω.2 hep.le)
    have hCfin := hupper.trans_lt hsumfin
    exact ⟨ENNReal.toReal_mono hCfin.ne (lintegral_mono_ae
      (hi.mono fun ω hω => ENNReal.rpow_le_rpow hω.1 hep.le)),
      ENNReal.toReal_mono hsumfin.ne hupper⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim hsumlim
    (hrealbounds.mono fun _ hi => hi.1) (hrealbounds.mono fun _ hi => hi.2)

end DOZZ.Proofs
