/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.CutoffIntegrand
public import DOZZ.ShiftEquations.PoleSubtracted.CutoffIncrements
public import DOZZ.ShiftEquations.PoleSubtracted.Tilt
import DOZZ.ShiftEquations.Mobius.InversionMoment

/-!
# The good event and the tilted domination

Almost surely the local mass is positive, the total mass at zero charge is finite and the chaos
has no atom at `0`. On this event `0 < R₁ ≤ T_{a,n} < ∞` for every charge and cutoff, so the real
masses of the cutoff integrand are those of the tilted masses. The Cameron–Martin tilt by
`a X_m(0)`, `m ≥ n`, then turns the domination of the cutoff integrand into the tilted moment
`E[(T_{a,n} - R₁)(T_{a,n}^{-a/γ} + R₁^{-a/γ})]`, finite for `a > -2η - δ`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The good event of the cutoff analysis. -/
def CutoffGood (M : Ω → Measure ℂ) (γ η : ℝ) (ω : Ω) : Prop :=
  0 < poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ∧
    poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) < ⊤ ∧ M ω {0} = 0

/-- The good event has full measure. -/
theorem ae_cutoffGood (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) : ∀ᵐ ω ∂P, CutoffGood M γ η ω := by
  have hη := (window_eta_pos hW).le
  have hηγ := window_eta_le_two_div hγ hγ2 hW
  have hη2 : η < γ / 2 := by linarith [window_eta_lt_quarter hW]
  filter_upwards [ae_localMass_pos P X hX γ hγ hγ2 M hM hη hηγ,
    ae_totalMass_lt_top P X hX γ hγ hγ2 M hM hη hη2,
    gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem baseMassReal_eq (M : Ω → Measure ℂ) (γ η : ℝ) (n : ℕ) (ω : Ω) :
    baseMassReal M γ η n ω = (cutoffTiltedMass γ η 0 n (M ω)).toReal := by
  rw [baseMassReal, poleCutoffBaseMass_eq]

namespace CutoffGood

variable {M : Ω → Measure ℂ} {γ η : ℝ} {ω : Ω}

omit [MeasurableSpace Ω] in
theorem cutoffTiltedMass_lt_top (h : CutoffGood M γ η ω) (hγ : 0 < γ) (a : ℝ) (n : ℕ) :
    cutoffTiltedMass γ η a n (M ω) < ⊤ :=
  (cutoffTiltedMass_le_exp_mul_totalMass_zero a hγ n (M ω)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.2.1)

omit [MeasurableSpace Ω] in
theorem localMass_lt_top (h : CutoffGood M γ η ω) :
    poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) < ⊤ :=
  (localMass_le_totalMass γ η (M ω)).trans_lt h.2.1

omit [MeasurableSpace Ω] in
theorem localMassReal_pos (h : CutoffGood M γ η ω) : 0 < localMassReal M γ η ω :=
  ENNReal.toReal_pos h.1.ne' h.localMass_lt_top.ne

theorem localMassReal_le (h : CutoffGood M γ η ω) (hγ : 0 < γ) (n : ℕ) :
    localMassReal M γ η ω ≤ baseMassReal M γ η n ω := by
  rw [baseMassReal_eq]
  exact ENNReal.toReal_mono (h.cutoffTiltedMass_lt_top hγ 0 n).ne
    (localMass_le_cutoffTiltedMass γ η 0 n (M ω))

theorem baseMassReal_le_succ (h : CutoffGood M γ η ω) (hγ : 0 < γ) (n : ℕ) :
    baseMassReal M γ η n ω ≤ baseMassReal M γ η (n + 1) ω := by
  rw [baseMassReal_eq, baseMassReal_eq]
  exact ENNReal.toReal_mono (h.cutoffTiltedMass_lt_top hγ 0 (n + 1)).ne
    (monotone_cutoffTiltedMass γ η 0 (M ω) (Nat.le_succ n))

end CutoffGood

/-- The real form of `(T - L)(T^s + L^s)`. -/
theorem ofReal_sub_mul_rpow_add_rpow {T L : ℝ≥0∞} (hL : 0 < L) (hLT : L ≤ T) (hT : T ≠ ⊤)
    (s : ℝ) :
    ENNReal.ofReal ((T.toReal - L.toReal) * (T.toReal ^ s + L.toReal ^ s)) =
      (T - L) * (T ^ s + L ^ s) := by
  have hL' : L ≠ ⊤ := ne_top_of_le_ne_top hT hLT
  have hLr : 0 < L.toReal := ENNReal.toReal_pos hL.ne' hL'
  have hTr : 0 < T.toReal := ENNReal.toReal_pos (hL.trans_le hLT).ne' hT
  rw [ENNReal.ofReal_mul (sub_nonneg.2 (ENNReal.toReal_mono hT hLT)),
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT,
    ENNReal.ofReal_toReal hL', ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_rpow_of_pos hTr, ← ENNReal.ofReal_rpow_of_pos hLr,
    ENNReal.ofReal_toReal hT, ENNReal.ofReal_toReal hL']

/-! ### Measurability -/

theorem measurable_circleAverage_origin {P : Measure Ω} {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hXc : IsCircleAverage P X Xc) (m : ℕ) : Measurable fun ω => Xc ω 0 m :=
  (hXc.1 m).comp (measurable_id.prodMk measurable_const)

theorem aemeasurable_baseMassReal (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (η : ℝ)
    (n : ℕ) : AEMeasurable (baseMassReal M γ η n) P := by
  have h : AEMeasurable (fun ω => (cutoffTiltedMass γ η 0 n (M ω)).toReal) P :=
    (aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
      (measurable_cutoffTiltedMass γ η 0 n)).ennreal_toReal
  exact h.congr (Eventually.of_forall fun ω => (baseMassReal_eq M γ η n ω).symm)

theorem aemeasurable_localMassReal (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (η : ℝ) :
    AEMeasurable (localMassReal M γ η) P :=
  (aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
    (measurable_poleLocalMass γ η)).ennreal_toReal

/-! ### The tilted domination -/

/-- The functional `(T_{0,n} - R₁)(T_{0,n}^s + R₁^s)` of a measure, in real form. -/
noncomputable def dominationFunctional (γ η s : ℝ) (n : ℕ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((cutoffTiltedMass γ η 0 n μ).toReal -
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) μ).toReal) *
    ((cutoffTiltedMass γ η 0 n μ).toReal ^ s +
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) μ).toReal ^ s))

theorem measurable_dominationFunctional (γ η s : ℝ) (n : ℕ) :
    Measurable (dominationFunctional γ η s n) := by
  have hT := (measurable_cutoffTiltedMass γ η 0 n).ennreal_toReal
  have hL := (measurable_poleLocalMass γ η).ennreal_toReal
  exact ENNReal.measurable_ofReal.comp
    ((hT.sub hL).mul ((hT.pow_const s).add (hL.pow_const s)))

/-- **Integrability of the cutoff domination**: for `a > -2η - δ` and `n ≤ m`. -/
theorem integrable_cutoffDomination (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) {a : ℝ} (ha : -2 * η - δ < a) {m n : ℕ} (hnm : n ≤ m) :
    Integrable (fun ω => (baseMassReal M γ η n ω - localMassReal M γ η ω) *
      cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a) P := by
  have hB := aemeasurable_baseMassReal P X hX γ hγ hγ2 M hM η n
  have hL := aemeasurable_localMassReal P X hX γ hγ hγ2 M hM η
  have hXm : AEMeasurable (fun ω => Xc ω 0 m) P :=
    (measurable_circleAverage_origin hXc m).aemeasurable
  have hmeas : AEMeasurable (fun ω => (baseMassReal M γ η n ω - localMassReal M γ η ω) *
      cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a) P := by
    unfold cutoffWeight
    exact (hB.sub hL).mul ((Real.measurable_exp.comp_aemeasurable (hXm.const_mul a)).mul
      ((hB.pow_const _).add (hL.pow_const _)))
  have hgood := ae_cutoffGood P X hX γ hγ hγ2 M hM hW
  have hnonneg : 0 ≤ᵐ[P] fun ω => (baseMassReal M γ η n ω - localMassReal M γ η ω) *
      cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a := by
    filter_upwards [hgood] with ω hω
    have hLr := hω.localMassReal_pos
    have hBr := hLr.trans_le (hω.localMassReal_le hγ n)
    exact mul_nonneg (sub_nonneg.2 (hω.localMassReal_le hγ n))
      (mul_nonneg (Real.exp_pos _).le (by positivity))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  -- the tilt
  have hfac : ∀ ω, ENNReal.ofReal ((baseMassReal M γ η n ω - localMassReal M γ η ω) *
      cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a) =
      ENNReal.ofReal (Real.exp (m * a ^ 2 / 2)) *
        (ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) *
          dominationFunctional γ η (-a / γ) n (M ω)) := by
    intro ω
    rw [dominationFunctional, ← baseMassReal_eq, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    unfold cutoffWeight localMassReal
    have he : Real.exp (a * Xc ω 0 m) =
        Real.exp (m * a ^ 2 / 2) * Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  simp_rw [hfac]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a m _
      (measurable_dominationFunctional γ η (-a / γ) n)]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hae : ∀ᵐ ω ∂P, dominationFunctional γ η (-a / γ) n
      ((M ω).withDensity (circleTiltDensity γ a m)) =
      (cutoffTiltedMass γ η a n (M ω) - poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)) *
        (cutoffTiltedMass γ η a n (M ω) ^ (-a / γ) +
          poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-a / γ)) := by
    filter_upwards [hgood] with ω hω
    rw [dominationFunctional, cutoffTiltedMass_withDensity γ η a hnm,
      poleLocalMass_withDensity]
    exact ofReal_sub_mul_rpow_add_rpow hω.1 (localMass_le_cutoffTiltedMass γ η a n (M ω))
      (hω.cutoffTiltedMass_lt_top hγ a n).ne _
  rw [lintegral_congr_ae hae]
  exact lintegral_cutoffDomination_lt_top P X hX γ hγ hγ2 M hM hW ha n

end DOZZ.Proofs

end
