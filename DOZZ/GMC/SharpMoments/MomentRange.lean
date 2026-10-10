/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.BallScaling
public import DOZZ.Statements.GMC.GmcMassMoment

/-! # The sharp unweighted moment range

On every bounded nonempty open set the moment of the limiting chaos mass is finite exactly below
`4/γ²`, including all negative orders. Finiteness below the threshold comes from inverse moments
of an inscribed disk and from a finite cover by small disks; divergence at and above the
threshold comes from the critical endpoint on the logarithmic chart. At an arbitrary center the
divergence is transported by the location transfer at subcritical orders `p' ↑ 4/γ²`, whose
constants stay bounded, and Fatou. See [KRV, (condmom)]. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Powers of a fixed extended real are continuous in a positive exponent. -/
theorem ennreal_rpow_tendsto_of_exponent_tendsto (x : ℝ≥0∞) (y : ℕ → ℝ) (y₀ : ℝ)
    (hy : Tendsto y atTop (𝓝 y₀)) (hy0 : 0 < y₀) (hypos : ∀ n, 0 < y n) :
    Tendsto (fun n => x ^ y n) atTop (𝓝 (x ^ y₀)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [ENNReal.zero_rpow_of_pos (hypos _), ENNReal.zero_rpow_of_pos hy0]
    exact tendsto_const_nhds
  rcases eq_or_ne x ⊤ with rfl | hxtop
  · simp only [ENNReal.top_rpow_of_pos (hypos _), ENNReal.top_rpow_of_pos hy0]
    exact tendsto_const_nhds
  have hxpos : 0 < x.toReal := ENNReal.toReal_pos hx0 hxtop
  have hrepr : ∀ t : ℝ, x ^ t = ENNReal.ofReal (x.toReal ^ t) := by
    intro t
    rw [← ENNReal.ofReal_rpow_of_pos hxpos, ENNReal.ofReal_toReal hxtop]
  simp only [hrepr]
  apply (ENNReal.continuous_ofReal.tendsto _).comp
  exact ((Real.continuousAt_const_rpow hxpos.ne').tendsto).comp hy

theorem gmcOpenSquare_subset_ball (ρ : ℝ) :
    gmcOpenSquare (ρ / 2) ⊆ Metric.ball 0 ρ := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im x
  linarith [hx.1, hx.2]

/-- At and above `4/γ²` every disk has infinite moment. -/
theorem gmc_ball_moment_eq_top_of_critical_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (p : ℝ) (hp : 4 / γ ^ 2 ≤ p) :
    gmcMassMoment P M (Metric.ball z ρ) p = ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  set pc : ℝ := 4 / γ ^ 2 with hpcdef
  have hpc1 : 1 < pc := by
    rw [hpcdef, lt_div_iff₀ (by positivity)]
    linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
  have hp0 : 0 < p := by linarith
  set ρ' : ℝ := min ρ (1 / 8) with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'8 : ρ' ≤ 1 / 8 := min_le_right _ _
  -- it suffices to treat the smaller disk and the critical order
  have hmono : gmcMassMoment P M (Metric.ball z ρ') p ≤ gmcMassMoment P M (Metric.ball z ρ) p := by
    apply lintegral_mono
    intro ω
    exact ENNReal.rpow_le_rpow (measure_mono (Metric.ball_subset_ball (min_le_left _ _))) hp0.le
  suffices hcrit : gmcMassMoment P M (Metric.ball z ρ') pc = ⊤ by
    apply top_unique
    refine le_trans ?_ hmono
    -- `x^pc ≤ 1 + x^p`, so a finite `p`-th moment would make the critical moment finite
    by_contra hlt
    push Not at hlt
    have hpoint : ∀ ω, M ω (Metric.ball z ρ') ^ pc ≤ 1 + M ω (Metric.ball z ρ') ^ p := by
      intro ω
      rcases le_or_gt (M ω (Metric.ball z ρ')) 1 with h1 | h1
      · calc M ω (Metric.ball z ρ') ^ pc ≤ 1 := ENNReal.rpow_le_one h1 (by linarith)
          _ ≤ 1 + M ω (Metric.ball z ρ') ^ p := le_self_add
      · calc M ω (Metric.ball z ρ') ^ pc ≤ M ω (Metric.ball z ρ') ^ p :=
            ENNReal.rpow_le_rpow_of_exponent_le h1.le hp
          _ ≤ 1 + M ω (Metric.ball z ρ') ^ p := le_add_self
    have hfin : gmcMassMoment P M (Metric.ball z ρ') pc < ⊤ := by
      calc gmcMassMoment P M (Metric.ball z ρ') pc
          ≤ ∫⁻ ω, (1 + M ω (Metric.ball z ρ') ^ p) ∂P := lintegral_mono hpoint
        _ = 1 + gmcMassMoment P M (Metric.ball z ρ') p := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
            rfl
        _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hlt⟩
    rw [hcrit] at hfin
    exact lt_irrefl _ hfin
  -- the reference disk at the origin has infinite critical moment
  have href : gmcMassMoment P M (Metric.ball 0 ρ') pc = ⊤ := by
    have hsq := gmc_openSquare_critical_moment_eq_top_of_chart P X hX γ hγ hγ2 M hM (ρ' / 2)
      (by positivity) (by linarith)
    apply top_unique
    rw [← hsq]
    apply lintegral_mono
    intro ω
    exact ENNReal.rpow_le_rpow (measure_mono (gmcOpenSquare_subset_ball ρ')) (by linarith)
  by_contra hne
  have hA : gmcMassMoment P M (Metric.ball z ρ') pc < ⊤ := lt_top_iff_ne_top.mpr hne
  -- subcritical orders increasing to `pc`
  set y : ℕ → ℝ := fun n => pc - (pc - 1) / ((n : ℝ) + 2) with hydef
  have hy1 : ∀ n, 1 ≤ y n := by
    intro n
    have hpos : 0 < (n : ℝ) + 2 := by positivity
    have : (pc - 1) / ((n : ℝ) + 2) ≤ pc - 1 := by
      rw [div_le_iff₀ hpos]
      linarith only [mul_nonneg (sub_nonneg.2 hpc1.le) (by positivity : (0 : ℝ) ≤ n + 1)]
    rw [hydef]
    linarith
  have hylt : ∀ n, y n < pc := by
    intro n
    have : 0 < (pc - 1) / ((n : ℝ) + 2) := by
      apply div_pos (by linarith) (by positivity)
    rw [hydef]
    linarith
  have hylim : Tendsto y atTop (𝓝 pc) := by
    have h : Tendsto (fun n : ℕ => (pc - 1) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      exact (tendsto_const_nhds (x := pc - 1)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    have := (tendsto_const_nhds (x := pc)).sub h
    simpa [hydef] using this
  -- uniform transfer constant on `[1, pc]`
  set R : ℝ := ‖z‖ + ρ' with hRdef
  have hR : 0 ≤ R := by positivity
  set Tstar : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) /
      2 * (pc ^ 2 + pc))) * ENNReal.ofReal ((1 + R) ^ 4) ^ pc with hTstar
  have hTstartop : Tstar ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
  have hbound : ∀ n, gmcMassMoment P M (Metric.ball 0 ρ') (y n) ≤
      Tstar * (1 + gmcMassMoment P M (Metric.ball z ρ') pc) := by
    intro n
    have htr := gmc_ball_moment_transfer P X hX γ hγ hγ2 M hM 0 z ρ' R hρ' hρ'8 hR
      (by simp [hRdef]) le_rfl (y n) (hylt n)
    have hyn0 : 0 ≤ y n := le_trans zero_le_one (hy1 n)
    have hfac : ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
        |y n ^ 2 - y n|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |y n| ≤ Tstar := by
      have habs1 : |y n ^ 2 - y n| ≤ pc ^ 2 + pc := by
        rw [abs_of_nonneg (by linarith only [mul_nonneg hyn0 (sub_nonneg.2 (hy1 n))])]
        linarith only [pow_le_pow_left₀ hyn0 (hylt n).le 2, hyn0, hpc1]
      have habs2 : |y n| ≤ pc := by rw [abs_of_nonneg hyn0]; exact (hylt n).le
      have hC : 0 ≤ γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 := by
        have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        have h1 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
        positivity
      have hbase : 1 ≤ ENNReal.ofReal ((1 + R) ^ 4) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))
      rw [hTstar]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left habs1 hC))) (ENNReal.rpow_le_rpow_of_exponent_le hbase habs2)
    have hmom : gmcMassMoment P M (Metric.ball z ρ') (y n) ≤
        1 + gmcMassMoment P M (Metric.ball z ρ') pc := by
      have hpoint : ∀ ω, M ω (Metric.ball z ρ') ^ y n ≤ 1 + M ω (Metric.ball z ρ') ^ pc := by
        intro ω
        rcases le_or_gt (M ω (Metric.ball z ρ')) 1 with h1 | h1
        · calc M ω (Metric.ball z ρ') ^ y n ≤ 1 := ENNReal.rpow_le_one h1 hyn0
            _ ≤ 1 + M ω (Metric.ball z ρ') ^ pc := le_self_add
        · calc M ω (Metric.ball z ρ') ^ y n ≤ M ω (Metric.ball z ρ') ^ pc :=
              ENNReal.rpow_le_rpow_of_exponent_le h1.le (hylt n).le
            _ ≤ 1 + M ω (Metric.ball z ρ') ^ pc := le_add_self
      calc gmcMassMoment P M (Metric.ball z ρ') (y n)
          ≤ ∫⁻ ω, (1 + M ω (Metric.ball z ρ') ^ pc) ∂P := lintegral_mono hpoint
        _ = 1 + gmcMassMoment P M (Metric.ball z ρ') pc := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
            rfl
    calc gmcMassMoment P M (Metric.ball 0 ρ') (y n)
        ≤ _ := htr
      _ ≤ Tstar * (1 + gmcMassMoment P M (Metric.ball z ρ') pc) := by
          gcongr
  -- Fatou along the exponents
  have hfatou : gmcMassMoment P M (Metric.ball 0 ρ') pc ≤
      Tstar * (1 + gmcMassMoment P M (Metric.ball z ρ') pc) := by
    have hlim : ∀ ω, Tendsto (fun n => M ω (Metric.ball 0 ρ') ^ y n) atTop
        (𝓝 (M ω (Metric.ball 0 ρ') ^ pc)) := fun ω =>
      ennreal_rpow_tendsto_of_exponent_tendsto _ y pc hylim (by linarith)
        (fun n => lt_of_lt_of_le zero_lt_one (hy1 n))
    have hmeas : ∀ n, AEMeasurable (fun ω => M ω (Metric.ball 0 ρ') ^ y n) P := fun n =>
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
        Metric.isOpen_ball.measurableSet).pow_const _
    calc gmcMassMoment P M (Metric.ball 0 ρ') pc
        = ∫⁻ ω, liminf (fun n => M ω (Metric.ball 0 ρ') ^ y n) atTop ∂P := by
          apply lintegral_congr
          intro ω
          exact ((hlim ω).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, M ω (Metric.ball 0 ρ') ^ y n ∂P) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ Tstar * (1 + gmcMassMoment P M (Metric.ball z ρ') pc) :=
          liminf_le_of_le (by isBoundedDefault) (fun b hb => by
            obtain ⟨n, hn⟩ := hb.exists
            exact hn.trans (hbound n))
  rw [href] at hfatou
  exact (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hTstartop)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hA⟩)).not_ge hfatou

/-- On each bounded nonempty open set the moment is finite exactly for `p < 4/γ²`, including all
negative `p`; at and above the endpoint it diverges. See [KRV, (condmom)]. -/
theorem equatorGFF_GMC_moment_range
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (O : Set ℂ)
    (hOopen : IsOpen O) (hObounded : Bornology.IsBounded O) (hOne : O.Nonempty)
    (p : ℝ) :
    (gmcMassMoment P M O p < ⊤) ↔ p < 4 / γ ^ 2 := by
  obtain ⟨z, hz⟩ := hOne
  obtain ⟨ρ₀, hρ₀, hballO⟩ := Metric.isOpen_iff.mp hOopen z hz
  constructor
  · intro hfin
    by_contra hge
    push Not at hge
    have htop := gmc_ball_moment_eq_top_of_critical_le P X hX γ hγ hγ2 M hM z ρ₀ hρ₀ p hge
    have hp0 : 0 ≤ p := le_trans (by positivity) hge
    have hle : gmcMassMoment P M (Metric.ball z ρ₀) p ≤ gmcMassMoment P M O p := by
      apply lintegral_mono
      intro ω
      exact ENNReal.rpow_le_rpow (measure_mono hballO) hp0
    rw [htop] at hle
    exact (lt_irrefl _ (hfin.trans_le' hle))
  · intro hp
    rcases le_or_gt 0 p with hp0 | hpneg
    · exact gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM O hObounded p hp0 hp
    · set ρ : ℝ := min ρ₀ (1 / 8) with hρdef
      have hρ : 0 < ρ := lt_min hρ₀ (by norm_num)
      have hsub : Metric.ball z ρ ⊆ O :=
        (Metric.ball_subset_ball (min_le_left _ _)).trans hballO
      have hfin := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM z ρ hρ
        (min_le_right _ _) p hp
      refine lt_of_le_of_lt ?_ hfin
      apply lintegral_mono
      intro ω
      exact ennreal_rpow_antitone_of_nonpos (measure_mono hsub) hpneg.le

end DOZZ.Proofs
