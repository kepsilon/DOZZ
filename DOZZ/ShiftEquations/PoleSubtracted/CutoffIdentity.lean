/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.CutoffHolomorphic
import DOZZ.GMC.Annulus.BallCover

/-!
# The martingale identity of the cutoff family

At a real point `x` of the half-plane the cutoff integrand is real, and the Cameron–Martin tilt by
`x X_m(0)` turns `G_{m,n}(x)` into `E[T_{x,n}^{1-x/γ} - R₁^{1-x/γ}]` for every `m ≥ n`: the tilt by
`X_m(0)` and by `X_n(0)` agree on `C_n`, and both leave the two unit balls unchanged. Hence
`G_{n+1,n} = G_{n,n}` on the real ray, and by the identity theorem on the whole half-plane. This is
the cancellation of `Z_{C_t}(0)` and `R₁` in `F_{t+1} - F_t` ([KRV, §10.2]), proved by real tilting
and holomorphy instead of independence.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_withDensity_measure {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable fun μ : Measure ℂ => μ.withDensity ρ := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hρ.indicator hs)

/-- The tilt identity for the `ofReal` of a real functional. -/
theorem lintegral_ofReal_circleTilt (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (a : ℝ) (m : ℕ)
    {Φ : Measure ℂ → ℝ} (hΦ : Measurable Φ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) * Φ (M ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Φ ((M ω).withDensity (circleTiltDensity γ a m))) ∂P := by
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact lintegral_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a m _
    (ENNReal.measurable_ofReal.comp hΦ)

/-- The tilt preserves integrability. -/
theorem integrable_circleTilt (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (a : ℝ) (m : ℕ)
    {Ψ : Measure ℂ → ℝ} (hΨ : Measurable Ψ)
    (hint : Integrable (fun ω => Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) * Ψ (M ω)) P) :
    Integrable (fun ω => Ψ ((M ω).withDensity (circleTiltDensity γ a m))) P := by
  have hM' : AEMeasurable (fun ω => (M ω).withDensity (circleTiltDensity γ a m)) P :=
    (measurable_withDensity_measure (measurable_circleTiltDensity γ a m)).comp_aemeasurable
      (gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM)
  refine ⟨(hΨ.comp_aemeasurable hM').aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [← lintegral_ofReal_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a m hΨ.norm]
  have h2 := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at h2
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  congr 1
  funext ω
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **The real Cameron–Martin tilt** by the circle average at the origin. -/
theorem integral_circleTilt (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (a : ℝ) (m : ℕ)
    {Ψ : Measure ℂ → ℝ} (hΨ : Measurable Ψ)
    (hint : Integrable (fun ω => Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) * Ψ (M ω)) P) :
    ∫ ω, Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) * Ψ (M ω) ∂P =
      ∫ ω, Ψ ((M ω).withDensity (circleTiltDensity γ a m)) ∂P := by
  have htilt : ∀ Φ : Measure ℂ → ℝ, Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) * Φ (M ω)) ∂P =
        ∫⁻ ω, ENNReal.ofReal (Φ ((M ω).withDensity (circleTiltDensity γ a m))) ∂P :=
    fun Φ hΦ => lintegral_ofReal_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a m hΦ
  have hint' := integrable_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a m hΨ hint
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint', htilt Ψ hΨ]
  congr 2
  have h := htilt (fun μ => -Ψ μ) hΨ.neg
  simp only [mul_neg] at h
  exact h

/-- The cutoff integrand at a real point is real. -/
theorem cutoffIntegrand_ofReal (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (γ η : ℝ) (m n : ℕ)
    (x : ℝ) (ω : Ω) :
    cutoffIntegrand Xc M γ η m n (x : ℂ) ω =
      ((Real.exp (x * Xc ω 0 m - m * x ^ 2 / 2) *
        (baseMassReal M γ η n ω ^ (1 - x / γ) - localMassReal M γ η ω ^ (1 - x / γ)) : ℝ) :
          ℂ) := by
  have hB : 0 ≤ baseMassReal M γ η n ω := ENNReal.toReal_nonneg
  have hL : 0 ≤ localMassReal M γ η ω := ENNReal.toReal_nonneg
  have hw : (1 - (x : ℂ) / γ) = ((1 - x / γ : ℝ) : ℂ) := by push_cast; ring
  unfold cutoffIntegrand
  rw [hw, ← Complex.ofReal_cpow hB, ← Complex.ofReal_cpow hL]
  push_cast
  ring_nf

/-- The real cutoff functional `T_{0,n}^{1-x/γ} - R₁^{1-x/γ}` of a measure. -/
noncomputable def realCutoffFunctional (γ η x : ℝ) (n : ℕ) (μ : Measure ℂ) : ℝ :=
  (cutoffTiltedMass γ η 0 n μ).toReal ^ (1 - x / γ) -
    (poleLocalMass γ (2 / γ + η) (2 / γ - η) μ).toReal ^ (1 - x / γ)

theorem measurable_realCutoffFunctional (γ η x : ℝ) (n : ℕ) :
    Measurable (realCutoffFunctional γ η x n) :=
  ((measurable_cutoffTiltedMass γ η 0 n).ennreal_toReal.pow_const _).sub
    ((measurable_poleLocalMass γ η).ennreal_toReal.pow_const _)

/-- The tilted real cutoff functional is the cutoff observable at charge `x`. -/
theorem realCutoffFunctional_withDensity (γ η x : ℝ) {m n : ℕ} (hnm : n ≤ m) (μ : Measure ℂ) :
    realCutoffFunctional γ η x n (μ.withDensity (circleTiltDensity γ x m)) =
      (cutoffTiltedMass γ η x n μ).toReal ^ (1 - x / γ) -
        (poleLocalMass γ (2 / γ + η) (2 / γ - η) μ).toReal ^ (1 - x / γ) := by
  rw [realCutoffFunctional, cutoffTiltedMass_withDensity γ η x hnm,
    poleLocalMass_withDensity]

/-- At a real point the cutoff integrand is the tilt weight times the real functional. -/
theorem cutoffIntegrand_ofReal_eq (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (γ η : ℝ)
    (m n : ℕ) (x : ℝ) (ω : Ω) :
    cutoffIntegrand Xc M γ η m n (x : ℂ) ω =
      ((Real.exp (x * Xc ω 0 m - m * x ^ 2 / 2) * realCutoffFunctional γ η x n (M ω) : ℝ) :
        ℂ) := by
  rw [cutoffIntegrand_ofReal, realCutoffFunctional, ← baseMassReal_eq]
  rfl

/-- The real cutoff integrand is integrable at real points of the half-plane. -/
theorem integrable_cutoffReal (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) {m n : ℕ} (hnm : n ≤ m) {x : ℝ} (hx : -2 * η - δ < x) :
    Integrable (fun ω => Real.exp (x * Xc ω 0 m - m * x ^ 2 / 2) *
      realCutoffFunctional γ η x n (M ω)) P := by
  have hc := (differentiableOn_cutoffFamily P X hX γ hγ hγ2 M hM Xc hXc hW hnm).2 (x : ℂ) hx
  have hre : Integrable (fun ω => (cutoffIntegrand Xc M γ η m n (x : ℂ) ω).re) P := hc.re
  refine hre.congr (Eventually.of_forall fun ω => ?_)
  simp only
  rw [cutoffIntegrand_ofReal_eq, Complex.ofReal_re]

/-- **Real values of the cutoff family**: for real `x > -2η - δ` and `n ≤ m`,
`G_{m,n}(x) = E[T_{x,n}^{1-x/γ} - R₁^{1-x/γ}]`. -/
theorem cutoffFamily_ofReal (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) {m n : ℕ} (hnm : n ≤ m) {x : ℝ} (hx : -2 * η - δ < x) :
    cutoffFamily P Xc M γ η m n (x : ℂ) =
      ((∫ ω, ((cutoffTiltedMass γ η x n (M ω)).toReal ^ (1 - x / γ) -
        (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ (1 - x / γ)) ∂P : ℝ) :
          ℂ) := by
  unfold cutoffFamily
  simp_rw [cutoffIntegrand_ofReal_eq]
  rw [integral_complex_ofReal, integral_circleTilt P X hX γ hγ hγ2 M hM Xc hXc x m
    (measurable_realCutoffFunctional γ η x n)
    (integrable_cutoffReal P X hX γ hγ hγ2 M hM Xc hXc hW hnm hx)]
  congr 2
  funext ω
  exact realCutoffFunctional_withDensity γ η x hnm (M ω)

/-- The cutoff observable at charge `x` is integrable. -/
theorem integrable_tiltedCutoff (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) (n : ℕ) {x : ℝ} (hx : -2 * η - δ < x) :
    Integrable (fun ω => (cutoffTiltedMass γ η x n (M ω)).toReal ^ (1 - x / γ) -
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ (1 - x / γ)) P := by
  have h := integrable_circleTilt P X hX γ hγ hγ2 M hM Xc hXc x n
    (measurable_realCutoffFunctional γ η x n)
    (integrable_cutoffReal P X hX γ hγ hγ2 M hM Xc hXc hW (le_refl n) hx)
  refine h.congr (Eventually.of_forall fun ω => ?_)
  exact realCutoffFunctional_withDensity γ η x (le_refl n) (M ω)

/-- **The martingale identity**: `G_{n+1,n} = G_{n,n}` on the half-plane. -/
theorem cutoffFamily_succ_eqOn (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) (n : ℕ) :
    EqOn (cutoffFamily P Xc M γ η (n + 1) n) (cutoffFamily P Xc M γ η n n)
      (cutoffHalfPlane η δ) := by
  have hf := ((differentiableOn_cutoffFamily P X hX γ hγ hγ2 M hM Xc hXc hW
    (Nat.le_succ n)).1).analyticOnNhd (isOpen_cutoffHalfPlane η δ)
  have hg := ((differentiableOn_cutoffFamily P X hX γ hγ hγ2 M hM Xc hXc hW
    (le_refl n)).1).analyticOnNhd (isOpen_cutoffHalfPlane η δ)
  set x₀ : ℝ := -2 * η - δ + 1 with hx₀
  have hx₀H : ((x₀ : ℝ) : ℂ) ∈ cutoffHalfPlane η δ := by
    change -2 * η - δ < ((x₀ : ℝ) : ℂ).re
    rw [Complex.ofReal_re, hx₀]
    linarith
  have hreal : ∀ x : ℝ, -2 * η - δ < x →
      cutoffFamily P Xc M γ η (n + 1) n (x : ℂ) = cutoffFamily P Xc M γ η n n (x : ℂ) :=
    fun x hx => by
      rw [cutoffFamily_ofReal P X hX γ hγ hγ2 M hM Xc hXc hW (Nat.le_succ n) hx,
        cutoffFamily_ofReal P X hX γ hγ hγ2 M hM Xc hXc hW (le_refl n) hx]
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀,
      cutoffFamily P Xc M γ η (n + 1) n (t : ℂ) = cutoffFamily P Xc M γ η n n (t : ℂ) :=
    eventually_nhdsWithin_of_eventually_nhds
      ((lt_mem_nhds (show -2 * η - δ < x₀ by rw [hx₀]; linarith)).mono fun t ht => hreal t ht)
  have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x₀) (𝓝[≠] ((x₀ : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => by
        simpa [Complex.ofReal_inj] using ht)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (isPreconnected_cutoffHalfPlane η δ) hx₀H
    (htend.frequently hev.frequently)

end DOZZ.Proofs

end
