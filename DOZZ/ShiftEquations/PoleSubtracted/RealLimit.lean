/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.CutoffCauchy
public import DOZZ.Statements.GMC.WeightedGmcBallMass
import DOZZ.GMC.SharpMoments.WeightedLocalRange
import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency

/-!
# The real limit of the cutoff family is the pole-subtracted observable

At a real charge `x ∈ (-2η - δ, 1/γ)`, `F_n(x) = E[T_{x,n}^{1-x/γ} - R₁^{1-x/γ}]`. The masses
`T_{x,n}` increase to the total mass `Z_ℂ(x)`, which is almost surely finite (it is at most the
weighted mass of the unit disk plus `Z_ℂ(0)`), so the integrands converge monotonically. If the
`F_n(x)` converge, monotone convergence identifies the limit with the pole-subtracted observable
`E[Z_ℂ(x)^{1-x/γ} - R₁^{1-x/γ}]` and proves its integrability ([KRV, §10.2]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Monotone convergence with convergent integrals -/

/-- If integrable `φ_n` increase a.e. to `f` and `∫ φ_n → e`, then `f` is integrable with
integral `e`. -/
theorem integrable_integral_eq_of_monotone {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {φ : ℕ → Ω → ℝ} {f : Ω → ℝ} {e : ℝ} (hint : ∀ n, Integrable (φ n) P)
    (hmono : ∀ᵐ ω ∂P, Monotone fun n => φ n ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => φ n ω) atTop (𝓝 (f ω)))
    (hE : Tendsto (fun n => ∫ ω, φ n ω ∂P) atTop (𝓝 e)) :
    Integrable f P ∧ ∫ ω, f ω ∂P = e := by
  set ψ : ℕ → Ω → ℝ := fun n ω => φ n ω - φ 0 ω with hψ
  have hψint : ∀ n, Integrable (ψ n) P := fun n => (hint n).sub (hint 0)
  have hψnn : ∀ n, 0 ≤ᵐ[P] ψ n := fun n => by
    filter_upwards [hmono] with ω hω
    exact sub_nonneg.2 (hω (Nat.zero_le n))
  have hglim : ∀ᵐ ω ∂P, Tendsto (fun n => ψ n ω) atTop (𝓝 (f ω - φ 0 ω)) := by
    filter_upwards [hlim] with ω hω
    exact hω.sub_const _
  have hgmeas : AEStronglyMeasurable (fun ω => f ω - φ 0 ω) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hψint n).aestronglyMeasurable) hglim
  have hgnn : 0 ≤ᵐ[P] fun ω => f ω - φ 0 ω := by
    filter_upwards [hglim, hmono] with ω hω hm
    exact ge_of_tendsto' hω fun n => sub_nonneg.2 (hm (Nat.zero_le n))
  have hmct : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (ψ n ω) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (f ω - φ 0 ω) ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hψint n).aemeasurable) ?_ ?_
    · filter_upwards [hmono] with ω hω
      exact fun i j hij => ENNReal.ofReal_le_ofReal (sub_le_sub_right (hω hij) _)
    · filter_upwards [hglim] with ω hω
      exact (ENNReal.continuous_ofReal.tendsto _).comp hω
  have hval : ∀ n, ∫⁻ ω, ENNReal.ofReal (ψ n ω) ∂P =
      ENNReal.ofReal ((∫ ω, φ n ω ∂P) - ∫ ω, φ 0 ω ∂P) := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hψint n) (hψnn n),
      integral_sub (hint n) (hint 0)]
  have hlim2 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (ψ n ω) ∂P) atTop
      (𝓝 (ENNReal.ofReal (e - ∫ ω, φ 0 ω ∂P))) := by
    simp_rw [hval]
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hE.sub_const _)
  have heq := tendsto_nhds_unique hmct hlim2
  have hgint : Integrable (fun ω => f ω - φ 0 ω) P :=
    ⟨hgmeas, (hasFiniteIntegral_iff_ofReal hgnn).2 (by rw [heq]; exact ENNReal.ofReal_lt_top)⟩
  have hfint : Integrable f P := by
    refine (hgint.add (hint 0)).congr (Eventually.of_forall fun ω => ?_)
    simp
  refine ⟨hfint, ?_⟩
  have hE0 : 0 ≤ e - ∫ ω, φ 0 ω ∂P := by
    refine sub_nonneg.2 (ge_of_tendsto' hE fun n => ?_)
    exact integral_mono_ae (hint 0) (hint n) (by
      filter_upwards [hmono] with ω hω
      exact hω (Nat.zero_le n))
  have hg : ∫ ω, (f ω - φ 0 ω) ∂P = e - ∫ ω, φ 0 ω ∂P := by
    rw [integral_eq_lintegral_of_nonneg_ae hgnn hgmeas, heq, ENNReal.toReal_ofReal hE0]
  rw [integral_sub hfint (hint 0)] at hg
  linarith

/-- The antitone version. -/
theorem integrable_integral_eq_of_antitone {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {φ : ℕ → Ω → ℝ} {f : Ω → ℝ} {e : ℝ} (hint : ∀ n, Integrable (φ n) P)
    (hanti : ∀ᵐ ω ∂P, Antitone fun n => φ n ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => φ n ω) atTop (𝓝 (f ω)))
    (hE : Tendsto (fun n => ∫ ω, φ n ω ∂P) atTop (𝓝 e)) :
    Integrable f P ∧ ∫ ω, f ω ∂P = e := by
  have h := integrable_integral_eq_of_monotone (φ := fun n ω => -φ n ω) (f := fun ω => -f ω)
    (e := -e) (fun n => (hint n).neg)
    (by filter_upwards [hanti] with ω hω; exact fun i j hij => neg_le_neg (hω hij))
    (by filter_upwards [hlim] with ω hω; exact hω.neg)
    (by simpa only [integral_neg] using hE.neg)
  refine ⟨by simpa using h.1.neg, ?_⟩
  have := h.2
  rw [integral_neg] at this
  linarith

/-! ### Finiteness of the total mass at charge `a < Q` -/

theorem totalMass_le_weighted_add {γ η : ℝ} (a : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η)
    (hηγ : η ≤ 2 / γ) (μ : Measure ℂ) :
    poleTotalMass γ a (2 / γ + η) (2 / γ - η) μ ≤
      weightedGmcBallMass γ μ a 0 1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ := by
  rw [poleTotalMass_eq, poleTotalMass_eq,
    ← lintegral_add_compl _ (Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1)).measurableSet]
  refine add_le_add ?_ ?_
  · unfold weightedGmcBallMass
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun y hy => ?_
    have hy1 : ‖y‖ < 1 := by simpa using hy
    rw [zeroTilt_of_norm_lt_one γ a hy1, sub_zero]
    exact mul_le_of_le_one_right zero_le
      (poleWeight_le_one_of_norm_le_one hγ hη hηγ hy1.le)
  · refine (setLIntegral_mono' Metric.isOpen_ball.measurableSet.compl fun y hy => ?_).trans
      (setLIntegral_le_lintegral _ _)
    · have hy1 : 1 ≤ ‖y‖ := by simpa using hy
      rw [zeroTilt_of_one_le_norm γ a hy1, zeroTilt_zero]

/-- The total mass at a charge `a < Q` is almost surely finite. -/
theorem ae_totalMass_lt_top_of_lt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    {a : ℝ} (ha : a < Q γ) :
    ∀ᵐ ω ∂P, poleTotalMass γ a (2 / γ + η) (2 / γ - η) (M ω) < ⊤ := by
  have hη := (window_eta_pos hW).le
  have hηγ := window_eta_le_two_div hγ hγ2 hW
  have hη2 : η < γ / 2 := by linarith [window_eta_lt_quarter hW]
  set p : ℝ := min (4 / γ ^ 2) (2 / γ * (Q γ - a)) / 2 with hp
  have hp0 : 0 < p := by
    rw [hp]
    have : 0 < 2 / γ * (Q γ - a) := mul_pos (by positivity) (by linarith)
    have : 0 < min (4 / γ ^ 2) (2 / γ * (Q γ - a)) := lt_min (by positivity) this
    linarith
  have hplt : p < min (4 / γ ^ 2) (2 / γ * (Q γ - a)) := by
    rw [hp]
    linarith
  have hmom := (equatorGFF_GMC_weighted_local_moment_range P X hX γ hγ hγ2 M hM a ha p hp0 0 1
    one_pos).2 hplt
  have hmeas : AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) a 0 1 ^ p) P :=
    (gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM a 0 1).pow_const _
  have hwfin : ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) a 0 1 < ⊤ := by
    have hint : ∫⁻ ω, weightedGmcBallMass γ (M ω) a 0 1 ^ p ∂P ≠ ⊤ := by
      simpa only [weightedGmcBallMoment, ENNReal.rpow_eq_pow] using hmom.ne
    filter_upwards [ae_lt_top' hmeas hint] with ω hω
    rw [lt_top_iff_ne_top]
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos hp0] at hω
    exact lt_irrefl _ hω
  filter_upwards [hwfin, ae_totalMass_lt_top P X hX γ hγ hγ2 M hM hη hη2] with ω h1 h2
  exact (totalMass_le_weighted_add a hγ hη hηγ (M ω)).trans_lt (ENNReal.add_lt_top.2 ⟨h1, h2⟩)

/-! ### Identification of the real limit -/

/-- **The real limit of the cutoff family is the pole-subtracted observable.** -/
theorem cutoff_real_limit_eq_observable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) {η δ : ℝ} (hW : TwoPoleWindow γ η δ) {x : ℝ}
    (hx₁ : -2 * η - δ < x) (hx₂ : x < 1 / γ) {e : ℂ}
    (hlim : Tendsto (fun n : ℕ => poleSubtractedCutoff P Xc M γ η n (x : ℂ)) atTop (𝓝 e)) :
    e = (poleSubtractedObservable P M γ η x : ℂ) := by
  set w : ℝ := 1 - x / γ with hw
  set E : ℕ → ℝ := fun n => ∫ ω, ((cutoffTiltedMass γ η x n (M ω)).toReal ^ w -
    (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w) ∂P with hEdef
  have hF : ∀ n : ℕ, poleSubtractedCutoff P Xc M γ η n (x : ℂ) = (E n : ℂ) := fun n => by
    rw [poleSubtractedCutoff_eq_cutoffFamily,
      cutoffFamily_ofReal P X hX γ hγ hγ2 M hM Xc hXc hW (le_refl n) hx₁]
  simp_rw [hF] at hlim
  have hE : Tendsto E atTop (𝓝 e.re) := by
    have h := (Complex.continuous_re.tendsto e).comp hlim
    simpa [Function.comp_def] using h
  have him : e.im = 0 := by
    have h := (Complex.continuous_im.tendsto e).comp hlim
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hxQ : x < Q γ := by
    have : 1 / γ < Q γ := by
      rw [Q]
      have : 1 / γ < 2 / γ := by
        rw [div_lt_div_iff_of_pos_right hγ]
        norm_num
      linarith [half_pos hγ]
    linarith
  have hgood := ae_cutoffGood P X hX γ hγ hγ2 M hM hW
  have hfin := ae_totalMass_lt_top_of_lt P X hX γ hγ hγ2 M hM hW hxQ
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => (cutoffTiltedMass γ η x n (M ω)).toReal ^ w -
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w) atTop
      (𝓝 ((poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w -
        (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w)) := by
    filter_upwards [hgood, hfin] with ω hω hT
    have h1 := tendsto_cutoffTiltedMass γ η x (M ω) hω.2.2
    have h2 := (ENNReal.tendsto_toReal hT.ne).comp h1
    have hLT : poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ≤
        poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) :=
      (localMass_le_cutoffTiltedMass γ η x 0 (M ω)).trans
        (cutoffTiltedMass_le_totalMass γ η x 0 (M ω))
    have hpos : 0 < (poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω)).toReal :=
      ENNReal.toReal_pos (hω.1.trans_le hLT).ne' hT.ne
    exact (h2.rpow_const (Or.inl hpos.ne')).sub_const _
  have hint : ∀ n, Integrable (fun ω => (cutoffTiltedMass γ η x n (M ω)).toReal ^ w -
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w) P :=
    fun n => integrable_tiltedCutoff P X hX γ hγ hγ2 M hM Xc hXc hW n hx₁
  have hmonoT : ∀ᵐ ω ∂P, ∀ i j : ℕ, i ≤ j →
      0 < (cutoffTiltedMass γ η x i (M ω)).toReal ∧
        (cutoffTiltedMass γ η x i (M ω)).toReal ≤ (cutoffTiltedMass γ η x j (M ω)).toReal := by
    filter_upwards [hgood] with ω hω i j hij
    refine ⟨ENNReal.toReal_pos (hω.1.trans_le (localMass_le_cutoffTiltedMass γ η x i (M ω))).ne'
      (hω.cutoffTiltedMass_lt_top hγ x i).ne, ?_⟩
    exact ENNReal.toReal_mono (hω.cutoffTiltedMass_lt_top hγ x j).ne
      (monotone_cutoffTiltedMass γ η x (M ω) hij)
  have hval : ∫ ω, ((poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w -
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ w) ∂P = e.re := by
    rcases le_or_gt 0 w with hw0 | hw0
    · refine (integrable_integral_eq_of_monotone hint ?_ hconv hE).2
      filter_upwards [hmonoT] with ω hω i j hij
      exact sub_le_sub_right (Real.rpow_le_rpow (hω i j hij).1.le (hω i j hij).2 hw0) _
    · refine (integrable_integral_eq_of_antitone hint ?_ hconv hE).2
      filter_upwards [hmonoT] with ω hω i j hij
      exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (hω i j hij).1 (hω i j hij).2
        hw0.le) _
  apply Complex.ext
  · rw [Complex.ofReal_re, poleSubtractedObservable, ← hval]
  · rw [Complex.ofReal_im, him]

end DOZZ.Proofs

end
