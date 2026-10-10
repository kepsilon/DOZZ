/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingMassPieces
public import DOZZ.FourPoint.Fusion.ProbabilitySplit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Convergence in probability of the moving rooted mass -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Moving rooted masses converge in probability along every sequence approaching zero. -/
theorem fusionMovingMass_tendstoInMeasure_seq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - (α₁ + γ / 2))))
    (y : ℂ) (hy : y ≠ 0) (z : ℕ → ℂ) (hz : Tendsto z atTop (nhds 0)) :
    TendstoInMeasure P (fun n ω => (fusionMovingMass γ α₁ α₂ α₃ y (z n) (M ω)).toReal)
      atTop (fun ω => (fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω)).toReal) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ξ := γ * (Q γ - (α₁ + γ / 2)) * p - γ ^ 2 * p ^ 2 / 2
  obtain ⟨hξ, Cy, hCy, hmy⟩ := fusion_rootedKernel_smallBall_moment
    P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hα hp hp1 hpRange y hy
  obtain ⟨_, C0, hC0, hm0⟩ := fusion_rootedKernel_smallBall_moment
    P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hα hp hp1 hpRange 1 (by norm_num)
  have hf0 : ∀ᵐ ω ∂P, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) < ⊤ := by
    simpa only [fusionMovingMass, fusionMovingKernel, mul_zero] using
      fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃
  apply tendstoInMeasure_of_ne_top
  intro ε hε hεtop
  let e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  have hεe : ENNReal.ofReal e ≤ ε := by rw [ENNReal.ofReal_toReal hεtop]
  let a := ENNReal.ofReal (e / 3)
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hap : a ^ p ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ha0) hat).ne'
  have hsmall : Tendsto (fun δ : ℝ => (Cy + C0) * ENNReal.ofReal (δ ^ ξ) / a ^ p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hr : Tendsto (fun δ : ℝ => δ ^ ξ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h : Tendsto (fun δ : ℝ => δ ^ ξ) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0 : ℝ) ^ ξ)) :=
        (Real.continuousAt_rpow_const 0 ξ (Or.inr hξ.le)).tendsto.mono_left nhdsWithin_le_nhds
      have hzpow : (0 : ℝ) ^ ξ = 0 := Real.zero_rpow (show ξ ≠ 0 from hξ.ne')
      rw [hzpow] at h
      exact h
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
    have h' := ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.add_ne_top.mpr ⟨hCy.ne, hC0.ne⟩))
    have h'' := ENNReal.Tendsto.mul_const h' (Or.inr (ENNReal.inv_ne_top.mpr hap))
    simpa only [ENNReal.ofReal_zero, mul_zero, zero_mul, div_eq_mul_inv, Function.comp_def] using h''
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  by_cases hηtop : η = ⊤
  · exact ⟨0, fun _ _ => by rw [hηtop]; exact le_top⟩
  let u := η.toReal
  have hu : 0 < u := ENNReal.toReal_pos hη.ne' hηtop
  have hηu : ENNReal.ofReal u = η := ENNReal.ofReal_toReal hηtop
  have hδchoice := (hsmall.eventually_lt_const (ENNReal.ofReal_pos.mpr (half_pos hu))).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 16 by norm_num))
  obtain ⟨δ, hδsmall, hδpos, hδ16⟩ := hδchoice.exists
  let B : ℂ → Ω → ℝ≥0∞ := fun w ω => fusionMovingBadMass γ α₁ α₂ α₃ y w δ (M ω)
  let G : ℂ → Ω → ℝ≥0∞ := fun w ω => fusionMovingGoodMass γ α₁ α₂ α₃ y w δ (M ω)
  have hB0 : ∫⁻ ω, B 0 ω ^ p ∂P ≤ C0 * ENNReal.ofReal (δ ^ ξ) := by
    simpa only [B, fusionMovingBadMass, fusionMovingKernel, mul_zero] using
      hm0 δ hδpos hδ16.le 0 (by simp; exact hδpos.le)
  have hB0fin : ∀ᵐ ω ∂P, B 0 ω ≠ ⊤ :=
    fusion_mass_finite_of_moment (fusionMovingBadMass_aemeasurable P X hX γ hγ hγ2 M hM
      α₁ α₂ α₃ y 0 δ) hp (lt_of_le_of_lt hB0 (ENNReal.mul_lt_top hC0 ENNReal.ofReal_lt_top))
  have hG0fin : ∀ᵐ ω ∂P, G 0 ω ≠ ⊤ := by
    filter_upwards [hf0] with ω hω
    exact (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hω).ne
  have hga : ∀ᵐ ω ∂P, Tendsto (fun n => (G (z n) ω).toReal) atTop (nhds (G 0 ω).toReal) := by
    filter_upwards [fusion_movingRoot_exterior_real_tendsto_ae P X hX γ hγ hγ2 M hM
      α₁ α₂ α₃ hα₁ hα₂ hα₃ y δ hδpos] with ω hω
    simpa only [G, fusionMovingGoodMass, fusionMovingKernel, mul_zero, Function.comp_def] using hω.comp hz
  have hgm : ∀ n, AEStronglyMeasurable (fun ω => (G (z n) ω).toReal) P := fun n =>
    (ENNReal.measurable_toReal.comp_aemeasurable (fusionMovingGoodMass_aemeasurable
      P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y (z n) δ)).aestronglyMeasurable
  have hgp := tendstoInMeasure_of_tendsto_ae hgm hga a (ENNReal.ofReal_pos.mpr (by positivity))
  have hge : ∀ᶠ n in atTop,
      P {ω | a ≤ ENNReal.ofReal |(G (z n) ω).toReal - (G 0 ω).toReal|} ≤ ENNReal.ofReal (u / 2) := by
    simpa only [edist_dist, Real.dist_eq] using
      (hgp.eventually_lt_const (ENNReal.ofReal_pos.mpr (half_pos hu))).mono fun _ h => h.le
  have hzn : Tendsto (fun n => ‖z n‖) atTop (nhds 0) := by
    simpa only [norm_zero, Function.comp_def] using continuous_norm.continuousAt.tendsto.comp hz
  have hyn : Tendsto (fun n => ‖y * z n‖) atTop (nhds 0) := by
    have hc : Continuous (fun w : ℂ => ‖y * w‖) := by fun_prop
    simpa only [mul_zero, norm_zero, Function.comp_def] using (hc.continuousAt (x := 0)).tendsto.comp hz
  have hnear := (hzn.eventually_lt_const hδpos).and
    ((hyn.eventually_lt_const (half_pos hδpos)).and (hyn.eventually_lt_const zero_lt_one))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hge.and hnear)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hgoodprob, hznδ, hynδ, hyn1⟩ := hN n hn
  have hBn : ∫⁻ ω, B (z n) ω ^ p ∂P ≤ Cy * ENNReal.ofReal (δ ^ ξ) :=
    hmy δ hδpos hδ16.le (z n) (by linarith)
  have hBnfin : ∀ᵐ ω ∂P, B (z n) ω ≠ ⊤ :=
    fusion_mass_finite_of_moment (fusionMovingBadMass_aemeasurable P X hX γ hγ hγ2 M hM
      α₁ α₂ α₃ y (z n) δ) hp (lt_of_le_of_lt hBn (ENNReal.mul_lt_top hCy ENNReal.ofReal_lt_top))
  have hGnfin : ∀ᵐ ω ∂P, G (z n) ω ≠ ⊤ := by
    filter_upwards [hG0fin] with ω hω
    exact (lt_of_le_of_lt (fusionMovingGoodMass_le γ α₁ α₂ α₃ y (z n) δ hδpos hznδ.le
      hynδ.le hyn1.le (M ω)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω.lt_top)).ne
  have hBnm := fusionMovingBadMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y (z n) δ
  have hB0m := fusionMovingBadMass_aemeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y 0 δ
  have hsplit := fusion_probability_split_bound P
    (fun ω => fusionMovingMass γ α₁ α₂ α₃ y (z n) (M ω))
    (fun ω => fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω)) (B (z n)) (B 0) (G (z n)) (G 0)
    (Eventually.of_forall fun ω => fusionMovingMass_split _ _ _ _ _ _ _ _)
    (Eventually.of_forall fun ω => fusionMovingMass_split _ _ _ _ _ _ _ _)
    hBnfin hB0fin hGnfin hG0fin he hεe
  have hpn := (meas_ge_le_lintegral_rpow_div hBnm ha0 hat hp).trans
    (ENNReal.div_le_div_right hBn _)
  have hp0 := (meas_ge_le_lintegral_rpow_div hB0m ha0 hat hp).trans
    (ENNReal.div_le_div_right hB0 _)
  calc
    _ ≤ P {ω | a ≤ B (z n) ω} + P {ω | a ≤ B 0 ω} +
        P {ω | a ≤ ENNReal.ofReal |(G (z n) ω).toReal - (G 0 ω).toReal|} := hsplit
    _ ≤ (Cy * ENNReal.ofReal (δ ^ ξ) / a ^ p + C0 * ENNReal.ofReal (δ ^ ξ) / a ^ p) +
        ENNReal.ofReal (u / 2) := add_le_add (add_le_add hpn hp0) hgoodprob
    _ = ((Cy + C0) * ENNReal.ofReal (δ ^ ξ) / a ^ p) + ENNReal.ofReal (u / 2) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ ENNReal.ofReal (u / 2) + ENNReal.ofReal (u / 2) := add_le_add hδsmall.le le_rfl
    _ = η := by rw [← ENNReal.ofReal_add (half_pos hu).le (half_pos hu).le, add_halves, hηu]

end DOZZ.Proofs
