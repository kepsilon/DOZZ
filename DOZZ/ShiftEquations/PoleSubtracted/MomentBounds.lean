/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.MassBounds
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.GMC.SharpMoments.SeibergMoment
import DOZZ.GMC.SharpMoments.MomentRange
import DOZZ.GMC.BallAnnulus.Ball
import DOZZ.ShiftEquations.Mobius.InversionMoment
import DOZZ.GMC.Annulus.BallCover

/-!
# Moments of the pole-subtracted masses

The probabilistic inputs of [KRV, §10.2] for the limit chaos `M`:

* the total mass has moments of every order below `4/γ²`, and the total mass at zero charge has
  moments of every order below the pole threshold `p = 1 - 2η/γ` ([DKRV] moment bounds);
* the local mass has negative moments of all orders (it dominates a fixed disk mass);
* the mass of `B(0, e^{-n})` has `r`-th moment `O(e^{-n ζ(r)})`, `ζ(r) = γ Q r - γ² r²/2`;
* Hölder's inequality with conjugate exponents `r`, `r/(r-1)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Hölder -/

/-- Hölder's inequality with conjugate exponents `r` and `r/(r-1)`. -/
theorem lintegral_mul_le_holder {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U V : Ω → ℝ≥0∞} (hU : AEMeasurable U P) (hV : AEMeasurable V P) {r : ℝ} (hr : 1 < r) :
    ∫⁻ ω, U ω * V ω ∂P ≤
      (∫⁻ ω, U ω ^ r ∂P) ^ (1 / r) * (∫⁻ ω, V ω ^ (r / (r - 1)) ∂P) ^ (1 / (r / (r - 1))) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq P ((Real.holderConjugate_iff_eq_conjExponent hr).2 rfl)
    hU hV

/-- Finite moments of conjugate orders give a finite mixed moment. -/
theorem lintegral_mul_lt_top_of_holder {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U V : Ω → ℝ≥0∞} (hU : AEMeasurable U P) (hV : AEMeasurable V P) {r : ℝ} (hr : 1 < r)
    (hUr : ∫⁻ ω, U ω ^ r ∂P < ⊤) (hVr : ∫⁻ ω, V ω ^ (r / (r - 1)) ∂P < ⊤) :
    ∫⁻ ω, U ω * V ω ∂P < ⊤ := by
  refine (lintegral_mul_le_holder hU hV hr).trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hUr.ne
  · have : 0 < r / (r - 1) := div_pos (by linarith) (by linarith)
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hVr.ne

/-- For `0 ≤ c < p (1 - 1/κ)` and `1 < κ` there is a Hölder exponent `1 < r < κ` with
`c r/(r-1) < p`. -/
theorem exists_holder_exponent {p c κ : ℝ} (hc : 0 ≤ c) (hκ : 1 < κ)
    (hcp : c < p * (1 - 1 / κ)) : ∃ r : ℝ, 1 < r ∧ r < κ ∧ c * (r / (r - 1)) < p := by
  have hp : 0 < p := by
    by_contra h
    push Not at h
    have : 0 < 1 - 1 / κ := by
      have : 1 / κ < 1 := by rw [div_lt_one (by linarith)]; exact hκ
      linarith
    nlinarith
  have hpc : 0 < p - c := by
    have : p * (1 - 1 / κ) ≤ p := by
      have : 0 ≤ 1 / κ := by positivity
      nlinarith
    linarith
  set r₀ : ℝ := p / (p - c) with hr₀
  have hr₀1 : 1 ≤ r₀ := by rw [hr₀, le_div_iff₀ hpc]; linarith
  have hr₀κ : r₀ < κ := by
    rw [hr₀, div_lt_iff₀ hpc]
    have : κ * (1 - 1 / κ) = κ - 1 := by field_simp
    nlinarith
  refine ⟨(r₀ + κ) / 2, by linarith, by linarith, ?_⟩
  set r : ℝ := (r₀ + κ) / 2 with hr
  have hr1 : 0 < r - 1 := by linarith
  rw [mul_div_assoc', div_lt_iff₀ hr1]
  have hrr₀ : r₀ < r := by linarith
  have : p < r * (p - c) := by
    rw [hr₀, div_lt_iff₀ hpc] at hrr₀
    linarith
  linarith

/-! ### Moments of the masses -/

/-- The total mass has moments of every positive order below `4/γ²`. -/
theorem lintegral_mass_univ_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {t : ℝ} (ht : 0 < t) (ht4 : t < 4 / γ ^ 2) :
    ∫⁻ ω, M ω univ ^ t ∂P < ⊤ := by
  have hQ : t < 2 / γ * (Q γ - 0) := by
    have : 2 / γ * (Q γ - 0) = 4 / γ ^ 2 + 1 := by
      rw [sub_zero, Q]
      field_simp
      ring
    linarith
  have h := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM (![] : Fin 0 → ℂ)
    (Function.injective_of_subsingleton _) (![] : Fin 0 → ℝ) 0 t ht ht4 (fun k => k.elim0) hQ
  simp_rw [measure_univ_eq_coulombMass γ]
  simpa only [ENNReal.rpow_eq_pow] using h

/-- The two poles are distinct. -/
theorem injective_twoPoles : Function.Injective (![2, -2] : Fin 2 → ℂ) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h

/-- The total mass at zero charge has moments of every positive order below `1 - 2η/γ`. -/
theorem lintegral_totalMass_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η : ℝ} (hη : 0 ≤ η) {t : ℝ} (ht : 0 < t)
    (htp : t < 1 - 2 * η / γ) :
    ∫⁻ ω, poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ t ∂P < ⊤ := by
  have hηγ : 0 ≤ 2 * η / γ := div_nonneg (by linarith) hγ.le
  have h4 : t < 4 / γ ^ 2 := by
    have : 1 < 4 / γ ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hk : ∀ k, t < 2 / γ * (Q γ - (![2 / γ + η, 2 / γ - η] : Fin 2 → ℝ) k) := by
    intro k
    fin_cases k
    · have : 2 / γ * (Q γ - (2 / γ + η)) = 1 - 2 * η / γ := by
        rw [Q]
        field_simp
        ring
      simpa [this] using htp
    · have : 2 / γ * (Q γ - (2 / γ - η)) = 1 + 2 * η / γ := by
        rw [Q]
        field_simp
        ring
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [this]
      linarith
  have hinf : t < 2 / γ * (Q γ - 0) := by
    have : 2 / γ * (Q γ - 0) = 4 / γ ^ 2 + 1 := by
      rw [sub_zero, Q]
      field_simp
      ring
    linarith
  have h := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM ![2, -2] injective_twoPoles
    ![2 / γ + η, 2 / γ - η] 0 t ht h4 hk hinf
  have hae : ∀ᵐ ω ∂P, poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ t =
      ENNReal.rpow (coulombMass γ (M ω) ![2 / γ + η, 2 / γ - η] ![2, -2] 0) t := by
    filter_upwards [gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 2,
      gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM (-2)] with ω h2 h2'
    rw [totalMass_zero_eq_coulombMass γ η (M ω) h2 h2', ENNReal.rpow_eq_pow]
  rw [lintegral_congr_ae hae]
  exact h

/-- The local mass has negative moments of all orders. -/
theorem lintegral_localMass_rpow_neg_lt_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η : ℝ} (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ)
    {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-q) ∂P < ⊤ := by
  have hball : gmcMassMoment P M (Metric.ball 2 (1 / 2)) (-q) < ⊤ :=
    (equatorGFF_GMC_moment_range P X hX γ hγ hγ2 M hM (Metric.ball 2 (1 / 2))
      Metric.isOpen_ball Metric.isBounded_ball (Metric.nonempty_ball.2 (by norm_num)) (-q)).2
      (by have : 0 < 4 / γ ^ 2 := by positivity
          linarith)
  have hpt : ∀ ω, poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-q) ≤
      9 ^ q * ENNReal.rpow (M ω (Metric.ball 2 (1 / 2))) (-q) := by
    intro ω
    have _ := hM.1 ω
    have hle := ball_le_localMass hγ hη hηγ (M ω)
    have hm : M ω (Metric.ball 2 (1 / 2)) ≠ ⊤ := measure_ne_top _ _
    calc poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-q)
        ≤ ((1 / 9 : ℝ≥0∞) * M ω (Metric.ball 2 (1 / 2))) ^ (-q) := by
          rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
          exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hle hq.le)
      _ = 9 ^ q * ENNReal.rpow (M ω (Metric.ball 2 (1 / 2))) (-q) := by
          rw [ENNReal.mul_rpow_of_ne_top (by simp) hm, ENNReal.rpow_eq_pow,
            one_div, ENNReal.inv_rpow, ← ENNReal.rpow_neg, neg_neg]
  calc ∫⁻ ω, poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-q) ∂P
      ≤ ∫⁻ ω, 9 ^ q * ENNReal.rpow (M ω (Metric.ball 2 (1 / 2))) (-q) ∂P := lintegral_mono hpt
    _ = 9 ^ q * gmcMassMoment P M (Metric.ball 2 (1 / 2)) (-q) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le (by simp))]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le (by simp)) hball

/-- The mass of `B(0, e^{-n})` has `r`-th moment `O(e^{-n ζ(r)})`. -/
theorem exists_lintegral_ball_rpow_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {r : ℝ} (hr : r < 4 / γ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ ω, M ω (Metric.ball 0 (Real.exp (-(n : ℝ)))) ^ r ∂P ≤
        ENNReal.ofReal (C * Real.exp (-(n : ℝ) * (γ * Q γ * r - γ ^ 2 * r ^ 2 / 2))) := by
  obtain ⟨C, hC, hb⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM r hr {0}
    isCompact_singleton
  refine ⟨C, hC, fun n => ?_⟩
  have h := (hb 0 rfl (Real.exp (-(n : ℝ))) (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (by simp))).2
  simp only [gmcMassMoment, ENNReal.rpow_eq_pow] at h
  have hrp : Real.rpow (Real.exp (-(n : ℝ))) (γ * Q γ * r - γ ^ 2 * r ^ 2 / 2) =
      Real.exp (-(n : ℝ) * (γ * Q γ * r - γ ^ 2 * r ^ 2 / 2)) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rwa [hrp] at h

/-! ### Almost-sure facts -/

theorem aemeasurable_measure_functional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {β : Type*} [MeasurableSpace β]
    {H : Measure ℂ → β} (hH : Measurable H) : AEMeasurable (fun ω => H (M ω)) P :=
  hH.comp_aemeasurable (gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM)

/-- The local mass is almost surely positive. -/
theorem ae_localMass_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η : ℝ} (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ) :
    ∀ᵐ ω ∂P, 0 < poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) := by
  have hint := lintegral_localMass_rpow_neg_lt_top P X hX γ hγ hγ2 M hM hη hηγ one_pos
  have hmeas : AEMeasurable (fun ω =>
      poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-(1 : ℝ))) P :=
    (aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
      (measurable_poleLocalMass γ η)).pow_const _
  filter_upwards [ae_lt_top' hmeas hint.ne] with ω hω
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0, ENNReal.zero_rpow_of_neg (by norm_num)] at hω
  exact lt_irrefl _ hω

/-- The total mass at zero charge is almost surely finite. -/
theorem ae_totalMass_lt_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η : ℝ} (hη : 0 ≤ η) (hηγ : η < γ / 2) :
    ∀ᵐ ω ∂P, poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) < ⊤ := by
  have hp : 0 < 1 - 2 * η / γ := by
    have : 2 * η / γ < 1 := by
      rw [div_lt_one hγ]
      linarith
    linarith
  have hint := lintegral_totalMass_rpow_lt_top P X hX γ hγ hγ2 M hM hη (half_pos hp)
    (half_lt_self hp)
  have hmeas : AEMeasurable (fun ω =>
      poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ ((1 - 2 * η / γ) / 2)) P :=
    (aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
      (measurable_poleTotalMass γ η 0)).pow_const _
  filter_upwards [ae_lt_top' hmeas hint.ne] with ω hω
  rw [lt_top_iff_ne_top]
  intro htop
  rw [htop, ENNReal.top_rpow_of_pos (half_pos hp)] at hω
  exact lt_irrefl _ hω

end DOZZ.Proofs

end
