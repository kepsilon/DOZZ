/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.MomentBounds
public import DOZZ.ShiftEquations.PoleSubtracted.Window
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The cutoff moment estimates

The two estimates behind the argument of [KRV, §10.2], after the Cameron–Martin tilt by `a X_m(0)`
has turned the base mass `B_n` into the tilted mass `T_{a,n}`:

* **domination** ([KRV, (interpol2)]): for `a > -2η - δ` and fixed `n`,
  `E[(T_{a,n} - R₁)(T_{a,n}^{-a/γ} + R₁^{-a/γ})] < ∞`. For `a ≤ 0` the regular part is at most
  `81 M(ℂ)` and both powers are at most `Z_ℂ(0)^{-a/γ}`; Hölder with `M(ℂ) ∈ L^r`, `r < 4/γ²`, and
  `Z_ℂ(0)^{-a/γ} ∈ L^{r/(r-1)}` needs `-a/γ < p(1 - γ²/4)`, which is the window room
  (`window_holder_room`, without shrinking the window). For `a > 0` the powers are at most
  `R₁^{-a/γ}`, which has all moments.
* **increments** ([KRV, (estF)]): uniformly for `a` in a compact subinterval,
  `E[(T_{a,n+1} - T_{a,n})(T_{a,n+1}^{-a/γ} + T_{a,n}^{-a/γ})] = O(e^{-κ n})`, since the annular
  increment is at most `e^{γ a⁺ (n+1)} M(B(0, e^{-n}))` and `E[M(B(0,e^{-n}))^r] = O(e^{-n ζ(r)})`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Power comparisons in `ℝ≥0∞` -/

theorem ennrpow_le_one_add_rpow {x : ℝ≥0∞} {s c : ℝ} (hs : 0 ≤ s) (hsc : s ≤ c) :
    x ^ s ≤ 1 + x ^ c := by
  rcases le_or_gt x 1 with hx | hx
  · exact (ENNReal.rpow_le_one hx hs).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le hx.le hsc).trans le_add_self

theorem ennrpow_le_one_add_rpow_neg {x : ℝ≥0∞} {s c : ℝ} (hs : s ≤ 0) (hcs : -c ≤ s) :
    x ^ s ≤ 1 + x ^ (-c) := by
  rcases le_or_gt 1 x with hx | hx
  · calc x ^ s ≤ x ^ (0 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hx hs
      _ = 1 := ENNReal.rpow_zero
      _ ≤ 1 + x ^ (-c) := le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_ge hx.le hcs).trans le_add_self

theorem ennrpow_le_of_le_of_nonpos {x y : ℝ≥0∞} (hxy : x ≤ y) {s : ℝ} (hs : s ≤ 0) :
    y ^ s ≤ x ^ s := by
  have h := ENNReal.rpow_le_rpow hxy (neg_nonneg.2 hs)
  rw [← neg_neg s, ENNReal.rpow_neg y, ENNReal.rpow_neg x]
  exact ENNReal.inv_le_inv.2 h

/-- `(1 + x)^q ≤ 2^q (1 + x^q)` for `q ≥ 1`. -/
theorem one_add_rpow_le {x : ℝ≥0∞} {q : ℝ} (hq : 1 ≤ q) :
    (1 + x) ^ q ≤ 2 ^ q * (1 + x ^ q) := by
  calc (1 + x) ^ q ≤ 2 ^ (q - 1) * (1 ^ q + x ^ q) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow 1 x hq
    _ ≤ 2 ^ q * (1 + x ^ q) := by
        rw [ENNReal.one_rpow]
        exact mul_le_mul_left (ENNReal.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) _

/-! ### A Hölder step with decay -/

/-- Hölder with a decaying `r`-th moment and a fixed finite conjugate moment. -/
theorem holder_decay {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Ω → ℝ≥0∞}
    {V : Ω → ℝ≥0∞} (hU : ∀ n, AEMeasurable (U n) P) (hV : AEMeasurable V P) {r : ℝ}
    (hr : 1 < r) {C ζ : ℝ}
    (hUr : ∀ n : ℕ, ∫⁻ ω, U n ω ^ r ∂P ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * ζ)))
    (hVr : ∫⁻ ω, V ω ^ (r / (r - 1)) ∂P < ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ∫⁻ ω, U n ω * V ω ∂P ≤ ENNReal.ofReal (K * Real.exp (-(ζ / r) * n)) := by
  set q : ℝ := r / (r - 1) with hqdef
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := div_pos hr0 (by linarith)
  set I : ℝ := (∫⁻ ω, V ω ^ q ∂P).toReal with hI
  refine ⟨max C 0 ^ (1 / r) * I ^ (1 / q), by positivity, fun n => ?_⟩
  have hH := lintegral_mul_le_holder (hU n) hV hr
  refine hH.trans ?_
  have h1 : (∫⁻ ω, U n ω ^ r ∂P) ^ (1 / r) ≤
      ENNReal.ofReal ((max C 0 * Real.exp (-(n : ℝ) * ζ)) ^ (1 / r)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.rpow_le_rpow ((hUr n).trans (ENNReal.ofReal_le_ofReal ?_)) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have h2 : (∫⁻ ω, V ω ^ q ∂P) ^ (1 / q) = ENNReal.ofReal (I ^ (1 / q)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hVr.ne]
  rw [h2]
  calc (∫⁻ ω, U n ω ^ r ∂P) ^ (1 / r) * ENNReal.ofReal (I ^ (1 / q))
      ≤ ENNReal.ofReal ((max C 0 * Real.exp (-(n : ℝ) * ζ)) ^ (1 / r)) *
          ENNReal.ofReal (I ^ (1 / q)) := mul_le_mul_left h1 _
    _ = ENNReal.ofReal (max C 0 ^ (1 / r) * I ^ (1 / q) * Real.exp (-(ζ / r) * n)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow (le_max_right _ _) (Real.exp_pos _).le, ← Real.exp_mul]
        have : -(n : ℝ) * ζ * (1 / r) = -(ζ / r) * n := by ring
        rw [this]
        ring

/-! ### Fixed-cutoff domination -/

/-- **Domination of the cutoff integrand** after the tilt (`interpol2`). -/
theorem lintegral_cutoffDomination_lt_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    {a : ℝ} (ha : -2 * η - δ < a) (n : ℕ) :
    ∫⁻ ω, (cutoffTiltedMass γ η a n (M ω) -
        poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)) *
      (cutoffTiltedMass γ η a n (M ω) ^ (-a / γ) +
        poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-a / γ)) ∂P < ⊤ := by
  have _ := hX.1
  have hη := (window_eta_pos hW).le
  have hηγ := window_eta_le_two_div hγ hγ2 hW
  have hp := window_threshold_pos hγ hW
  have hroom := window_holder_room hγ hγ2 hW
  have hκ : 1 < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hUmeas : AEMeasurable (fun ω => M ω univ) P :=
    aemeasurable_measure_functional P X hX γ hγ hγ2 M hM (Measure.measurable_coe MeasurableSet.univ)
  have hreg : ∀ ω, cutoffTiltedMass γ η a n (M ω) -
      poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ≤
      81 * ENNReal.ofReal (Real.exp (γ * max a 0 * n)) * M ω univ := by
    intro ω
    rw [tsub_le_iff_left, cutoffTiltedMass_eq_localMass_add γ η a n (M ω)]
    exact add_le_add le_rfl (regularMass_le a hγ hη hηγ n (M ω))
  rcases le_or_gt a 0 with ha0 | ha0
  · -- a nonpositive charge: positive powers of the total mass at zero charge
    set s : ℝ := -a / γ with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hγ.le
    have hsp : s < (1 - 2 * η / γ) * (1 - 1 / (4 / γ ^ 2)) := by
      have : 1 / (4 / γ ^ 2) = γ ^ 2 / 4 := by field_simp
      rw [this]
      refine lt_of_le_of_lt ?_ hroom
      rw [hs, div_le_div_iff_of_pos_right hγ]
      linarith
    obtain ⟨r, hr1, hr4, hrs⟩ := exists_holder_exponent hs0 hκ hsp
    have hpt : ∀ ω, (cutoffTiltedMass γ η a n (M ω) -
          poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)) *
        (cutoffTiltedMass γ η a n (M ω) ^ s +
          poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s) ≤
        162 * (M ω univ * poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s) := by
      intro ω
      have hmax : max a 0 = 0 := max_eq_right ha0
      have h1 : cutoffTiltedMass γ η a n (M ω) ^ s ≤
          poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s :=
        ENNReal.rpow_le_rpow (cutoffTiltedMass_le_totalMass_zero hγ ha0 n (M ω)) hs0
      have h2 : poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s ≤
          poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s :=
        ENNReal.rpow_le_rpow (localMass_le_totalMass γ η (M ω)) hs0
      have h3 := hreg ω
      rw [hmax, mul_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one] at h3
      calc _ ≤ (81 * M ω univ) * (poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s +
            poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s) :=
            mul_le_mul' h3 (add_le_add h1 h2)
        _ = 162 * (M ω univ * poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s) := by
            rw [← two_mul]
            ring
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_const_mul' _ _ (by simp)]
    refine ENNReal.mul_lt_top (by simp) ?_
    have hVmeas : AEMeasurable (fun ω =>
        poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ s) P :=
      (aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
        (measurable_poleTotalMass γ η 0)).pow_const _
    refine lintegral_mul_lt_top_of_holder hUmeas hVmeas hr1
      (lintegral_mass_univ_rpow_lt_top P X hX γ hγ hγ2 M hM (by linarith) hr4) ?_
    simp_rw [← ENNReal.rpow_mul]
    rcases eq_or_lt_of_le hs0 with hs00 | hs00
    · rw [← hs00, zero_mul]
      simp
    · exact lintegral_totalMass_rpow_lt_top P X hX γ hγ hγ2 M hM hη
        (mul_pos hs00 (div_pos (by linarith) (by linarith))) hrs
  · -- a positive charge: negative powers of the local mass
    set s : ℝ := -a / γ with hs
    have hs0 : s < 0 := div_neg_of_neg_of_pos (by linarith) hγ
    set r : ℝ := (1 + 4 / γ ^ 2) / 2 with hrdef
    have hr1 : 1 < r := by rw [hrdef]; linarith
    have hr4 : r < 4 / γ ^ 2 := by rw [hrdef]; linarith
    have hpt : ∀ ω, (cutoffTiltedMass γ η a n (M ω) -
          poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)) *
        (cutoffTiltedMass γ η a n (M ω) ^ s +
          poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s) ≤
        (162 * ENNReal.ofReal (Real.exp (γ * max a 0 * n))) *
          (M ω univ * poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s) := by
      intro ω
      have h1 : cutoffTiltedMass γ η a n (M ω) ^ s ≤
          poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s :=
        ennrpow_le_of_le_of_nonpos (localMass_le_cutoffTiltedMass γ η a n (M ω)) hs0.le
      calc _ ≤ (81 * ENNReal.ofReal (Real.exp (γ * max a 0 * n)) * M ω univ) *
            (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s +
              poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s) :=
            mul_le_mul' (hreg ω) (add_le_add h1 le_rfl)
        _ = _ := by
            rw [← two_mul]
            ring
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top) ?_
    have hVmeas : AEMeasurable (fun ω =>
        poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ s) P :=
      (aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
        (measurable_poleLocalMass γ η)).pow_const _
    refine lintegral_mul_lt_top_of_holder hUmeas hVmeas hr1
      (lintegral_mass_univ_rpow_lt_top P X hX γ hγ hγ2 M hM (by linarith) hr4) ?_
    simp_rw [← ENNReal.rpow_mul]
    have hq : 0 < -(s * (r / (r - 1))) := by
      have : 0 < r / (r - 1) := div_pos (by linarith) (by linarith)
      nlinarith
    have h := lintegral_localMass_rpow_neg_lt_top P X hX γ hγ hγ2 M hM hη hηγ hq
    rwa [neg_neg] at h

end DOZZ.Proofs

end
