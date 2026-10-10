/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.ArbitraryCenter
public import DOZZ.GMC.SharpMoments.MomentConvergence
public import DOZZ.GMC.Annulus.BallCover

/-! # Location transfer of small-disk moments for limiting chaos

Cutoff masses of bounded sets converge in probability, and small disks have cutoff-uniform moments
beyond every subcritical order, so moments of small-disk masses converge along the cutoffs. The
finite-cutoff location transfer therefore passes to every `IsGMCOf` limit: every subcritical moment
of a small disk at one center is bounded by an explicit constant times the same moment at another
center. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Cutoff masses of a bounded measurable set converge in probability along the integer
cutoffs. -/
theorem regularizedGMC_mass_toReal_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ) (hAR : A ⊆ Metric.closedBall (0 : ℂ) R) :
    TendstoInMeasure P (fun (n : ℕ) ω => (regularizedGMC P Xc γ n ω A).toReal) atTop
      (fun ω => (M ω A).toReal) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hL1 := equatorGFF_GMC_bounded_mass_l1_of_uniform_L1 P X hX γ hγ hγ2 M hM Xc hXc A hA R hAR
  set f : ℕ → Ω → ℝ := fun n ω => (regularizedGMC P Xc γ n ω A).toReal with hf
  set g : Ω → ℝ := fun ω => (M ω A).toReal with hg
  have hfmeas : ∀ n, Measurable (f n) := fun n =>
    measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ n A hA
  have hgmeas : AEMeasurable g P :=
    ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM A hA)
  have hL1nat : Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂P) atTop (𝓝 0) :=
    hL1.comp tendsto_natCast_atTop_atTop
  intro ε hε
  by_cases hεtop : ε = ⊤
  · have hzero : ∀ n, P {ω | ε ≤ edist (f n ω) (g ω)} = 0 := by
      intro n
      rw [hεtop]
      have hset : {ω | (⊤ : ℝ≥0∞) ≤ edist (f n ω) (g ω)} = ∅ := by
        ext ω
        simp [edist_ne_top]
      rw [hset, measure_empty]
    simp [hzero]
  · have hmarkov : ∀ n, P {ω | ε ≤ edist (f n ω) (g ω)} ≤
        (∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂P) / ε := by
      intro n
      have hm : AEMeasurable (fun ω => ENNReal.ofReal |f n ω - g ω|) P :=
        ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
          ((hfmeas n).aemeasurable.sub hgmeas))
      refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div hm hε.ne' hεtop)
      intro ω hω
      change ε ≤ edist (f n ω) (g ω) at hω
      change ε ≤ ENNReal.ofReal |f n ω - g ω|
      rwa [edist_dist, Real.dist_eq] at hω
    have hdiv : Tendsto (fun n : ℕ => (∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂P) / ε)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.div_const hL1nat (Or.inr hε.ne')
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun _ => zero_le) hmarkov

theorem ball_subset_closedBall_norm_add (z : ℂ) (ρ : ℝ) :
    Metric.ball z ρ ⊆ Metric.closedBall 0 (‖z‖ + ρ) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ρ := by linarith

/-- Moments of every subcritical order of a small disk converge along the integer cutoffs. -/
theorem gmc_ball_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (p : ℝ) (hp : p < 4 / γ ^ 2) :
    Tendsto (fun n : ℕ => gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball c ρ) p) atTop
      (𝓝 (gmcMassMoment P M (Metric.ball c ρ) p)) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hball : MeasurableSet (Metric.ball c ρ) := Metric.isOpen_ball.measurableSet
  rcases lt_trichotomy p 0 with hpneg | hp0 | hppos
  · obtain ⟨K, hK, hKb⟩ := regularizedGMC_ball_moment_uniform_any_center P X hX Xc hXc γ hγ hγ2
      c ρ hρ hρ8 (p - 1) (by linarith)
    exact lintegral_rpow_tendsto_of_uniform_moment P
      (fun (n : ℕ) ω => regularizedGMC P Xc γ n ω (Metric.ball c ρ))
      (fun ω => M ω (Metric.ball c ρ))
      (fun n => ((Measure.measurable_coe hball).comp
        (regularizedGMC_measurable P X hX Xc hXc γ n)).aemeasurable)
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _ hball)
      (fun n => by
        filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hω
        exact measure_ne_top _ _)
      (Eventually.of_forall fun ω => by
        have := hM.1 ω
        exact measure_ne_top _ _)
      (regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc _ hball _
        (ball_subset_closedBall_norm_add c ρ))
      p (p - 1) (Or.inr ⟨by linarith, hpneg⟩) K hK.ne (fun n => hKb n (Nat.cast_nonneg n))
  · subst hp0
    have h0 : ∀ x : ℝ≥0∞, ENNReal.rpow x 0 = 1 := fun x => ENNReal.rpow_zero
    simp only [gmcMassMoment, h0, lintegral_const, measure_univ, mul_one]
    exact tendsto_const_nhds
  · set p' : ℝ := (p + 4 / γ ^ 2) / 2 with hp'
    obtain ⟨K, hK, hKb⟩ := regularizedGMC_ball_moment_uniform_any_center P X hX Xc hXc γ hγ hγ2
      c ρ hρ hρ8 p' (by rw [hp']; linarith)
    exact lintegral_rpow_tendsto_of_uniform_moment P
      (fun (n : ℕ) ω => regularizedGMC P Xc γ n ω (Metric.ball c ρ))
      (fun ω => M ω (Metric.ball c ρ))
      (fun n => ((Measure.measurable_coe hball).comp
        (regularizedGMC_measurable P X hX Xc hXc γ n)).aemeasurable)
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _ hball)
      (fun n => by
        filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hω
        exact measure_ne_top _ _)
      (Eventually.of_forall fun ω => by
        have := hM.1 ω
        exact measure_ne_top _ _)
      (regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc _ hball _
        (ball_subset_closedBall_norm_add c ρ))
      p p' (Or.inl ⟨hppos, by rw [hp']; linarith⟩) K hK.ne (fun n => hKb n (Nat.cast_nonneg n))

/-- The location transfer of every subcritical moment of a small disk, for `IsGMCOf` limits. -/
theorem gmc_ball_moment_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z z₀ : ℂ) (ρ R : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hR : 0 ≤ R) (hzR : ‖z‖ + ρ ≤ R)
    (hz₀R : ‖z₀‖ + ρ ≤ R) (p : ℝ) (hp : p < 4 / γ ^ 2) :
    gmcMassMoment P M (Metric.ball z ρ) p ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
          |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
        gmcMassMoment P M (Metric.ball z₀ ρ) p := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) /
      2 * |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| with hT
  have hTtop : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top)
  have hcut : ∀ n : ℕ, gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball z ρ) p ≤
      T * gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball z₀ ρ) p := by
    intro n
    have htr := cutoff_translate_moment_le P X hX Xc hXc γ n (Nat.cast_nonneg n) z z₀ ρ R hR hzR
      hz₀R (fun _ => 1) measurable_const 1 (fun _ => le_rfl) p
    have hone : ∀ (c : ℂ) (ω : Ω), (∫⁻ x in Metric.ball c ρ, ((fun _ : ℂ => (1 : ℝ≥0)) (x - c) :
        ℝ≥0∞) ∂regularizedGMC P Xc γ n ω) = regularizedGMC P Xc γ n ω (Metric.ball c ρ) := by
      intro c ω
      simp
    simp only [hone] at htr
    exact htr
  have h1 := gmc_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc z ρ hρ hρ8 p hp
  have h2 := ENNReal.Tendsto.const_mul
    (gmc_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc z₀ ρ hρ hρ8 p hp) (Or.inr hTtop)
  exact le_of_tendsto_of_tendsto' h1 h2 hcut

/-- Sharp upper bound for subcritical moments of small disks at a fixed center:
`E M(B(z,ρ))^p ≤ C ρ^{ξ(p)}` for all `0 < ρ ≤ 1/8`. -/
theorem gmc_ball_moment_sharp_upper_center
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (p : ℝ) (hp : p < 4 / γ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 8 →
      gmcMassMoment P M (Metric.ball z ρ) p ≤
        ENNReal.ofReal (C * ρ ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
  set ξ : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 with hξ
  set R : ℝ := ‖z‖ + 1 / 8 with hRdef
  have hR : 0 ≤ R := by positivity
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) /
      2 * |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| with hT
  have hTtop : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top)
  set m₀ : ℝ≥0∞ := gmcMassMoment P M (Metric.ball 0 (1 / 8)) p with hm₀
  have hm₀top : m₀ ≠ ⊤ := (gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM 0 (1 / 8)
    (by norm_num) le_rfl p hp).ne
  set C : ℝ := T.toReal * m₀.toReal * 8 ^ ξ + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ T.toReal * m₀.toReal * 8 ^ ξ := by positivity
    linarith
  refine ⟨C, hC0, fun ρ hρ hρ8 => ?_⟩
  have htr := gmc_ball_moment_transfer P X hX γ hγ hγ2 M hM z 0 ρ R hρ hρ8 hR
    (by rw [hRdef]; linarith) (by rw [norm_zero, zero_add, hRdef]; linarith [norm_nonneg z]) p hp
  have hscale := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM (a := 0) (c := 8 * ρ)
    (R := 1 / 8) (by positivity) (by linarith) (by norm_num) (by norm_num) (by simp; linarith) p
  have hrad : 8 * ρ * (1 / 8) = ρ := by ring
  rw [hrad] at hscale
  calc gmcMassMoment P M (Metric.ball z ρ) p
      ≤ T * gmcMassMoment P M (Metric.ball 0 ρ) p := htr
    _ = T * (ENNReal.ofReal ((8 * ρ) ^ ξ) * m₀) := by rw [hscale]
    _ = ENNReal.ofReal (T.toReal * m₀.toReal * 8 ^ ξ * ρ ^ ξ) := by
        rw [← ENNReal.ofReal_toReal hTtop, ← ENNReal.ofReal_toReal hm₀top,
          Real.mul_rpow (by norm_num) hρ.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
          ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (C * ρ ^ ξ) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hρ.le _)
        rw [hC]
        linarith

end DOZZ.Proofs
