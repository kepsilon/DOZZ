/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ReflectionLastCutShift
import Mathlib.Analysis.MeanInequalitiesPow

/-! Small-power estimates for the retained mass in the lastone limit. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A fixed subunit moment controls the increment at a smaller exponent, with a coefficient
that vanishes with that exponent. This controls the complementary-mass error term in the proof of
[KRV, Lemma 10.6]. -/
theorem lastone_rpow_add_increment_le (a b p q : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hp : 0 < p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    (a + b) ^ p - a ^ p ≤ (p / q) * b ^ q * a ^ (p - q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hpow : (a + b) ^ p ≤ (a ^ q + b ^ q) ^ (p / q) := by
    calc
      (a + b) ^ p = ((a + b) ^ q) ^ (p / q) := by
        rw [← Real.rpow_mul (by positivity), mul_div_cancel₀ _ hq.ne']
      _ ≤ (a ^ q + b ^ q) ^ (p / q) :=
        Real.rpow_le_rpow (by positivity)
          (Real.rpow_add_le_add_rpow ha.le hb hq.le hq1) (div_pos hp hq).le
  have hinc := real_rpow_add_increment_le_subunit (a ^ q) (b ^ q) (p / q)
    (Real.rpow_pos_of_pos ha q) (Real.rpow_nonneg hb q) (div_pos hp hq)
    ((div_le_one hq).mpr hpq)
  have hexp : (a ^ q) ^ (p / q - 1) = a ^ (p - q) := by
    rw [← Real.rpow_mul ha.le]
    congr 1
    field_simp
  rw [hexp, ← Real.rpow_mul ha.le, mul_div_cancel₀ _ hq.ne'] at hinc
  exact (sub_le_sub_right hpow _).trans hinc

/-- A positive moment bounds a small power with an error proportional to its order. -/
theorem lastone_rpow_le_one_add (x p u : ℝ)
    (hx : 0 ≤ x) (hp : 0 < p) (hpu : p ≤ u) :
    x ^ p ≤ 1 + (p / u) * x ^ u := by
  have hu : 0 < u := hp.trans_le hpu
  have h := rpow_one_add_le_one_add_mul_self
    (s := x ^ u - 1) (p := p / u) (by linarith [Real.rpow_nonneg hx u])
    (div_pos hp hu).le ((div_le_one hu).mpr hpu)
  rw [add_sub_cancel, ← Real.rpow_mul hx, mul_div_cancel₀ _ hu.ne'] at h
  have hpu0 : 0 ≤ p / u := (div_pos hp hu).le
  calc x ^ p ≤ 1 + (p / u) * (x ^ u - 1) := h
       _ ≤ 1 + (p / u) * x ^ u := by linarith

/-- An inverse moment bounds the deficit of a small positive power. -/
theorem lastone_one_le_rpow_add (x p v : ℝ)
    (hx : 0 < x) (hp : 0 ≤ p) (hv : 0 < v) :
    1 ≤ x ^ p + (p / v) * x ^ (-v) := by
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-v))
  rw [Real.log_rpow hx] at hlog
  have hexp := Real.add_one_le_exp (Real.log x * p)
  rw [← Real.rpow_def_of_pos hx] at hexp
  have hmul := mul_le_mul_of_nonneg_left hlog (div_nonneg hp hv.le)
  have hcancel : (p / v) * (-v * Real.log x) = -(Real.log x * p) := by
    field_simp
  rw [hcancel] at hmul
  have hcoef : 0 ≤ p / v := div_nonneg hp hv.le
  linarith

/-- Positive and inverse moments of fixed order dominate the complementary-mass error
with a coefficient proportional to the vanishing exponent. -/
theorem lastone_rpow_add_increment_le_moments (a b p q : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hp : 0 < p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    (a + b) ^ p - a ^ p ≤ (p / q) * (1 + 2 * b ^ (2 * q) + a ^ (-2 * q)) := by
  have hweight : a ^ (p - q) ≤ 1 + a ^ (-q) := by
    by_cases ha1 : 1 ≤ a
    · exact (Real.rpow_le_one_of_one_le_of_nonpos ha1 (sub_nonpos.mpr hpq)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg ha.le (-q)))
    · exact (Real.rpow_le_rpow_of_exponent_ge ha (le_of_not_ge ha1)
        (by linarith : -q ≤ p - q)).trans
        (le_add_of_nonneg_left (by norm_num))
  have hbq := Real.rpow_nonneg hb q
  have haq := Real.rpow_nonneg ha.le (-q)
  have hbSq : (b ^ q) ^ (2 : ℕ) = b ^ (2 * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    congr 1
    ring
  have haSq : (a ^ (-q)) ^ (2 : ℕ) = a ^ (-2 * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    ring
  have hdom : b ^ q * a ^ (p - q) ≤ 1 + 2 * b ^ (2 * q) + a ^ (-2 * q) := by
    have hmul := mul_le_mul_of_nonneg_left hweight hbq
    have hs1 := sq_nonneg (b ^ q - 1)
    have hs2 := sq_nonneg (b ^ q - a ^ (-q))
    rw [← hbSq, ← haSq]
    nlinarith
  have hcoef : 0 ≤ p / q := (div_pos hp (hp.trans_le hpq)).le
  exact (lastone_rpow_add_increment_le a b p q ha hb hp hpq hq1).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdom hcoef)

/-- Uniform positive and inverse moments force every varying small positive moment to tend
to one. No convergence of the underlying random variables is required. -/
theorem lastone_smallPower_moment_tendsto_one
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ι → Ω → ℝ≥0∞) (l : Filter ι) (e : ι → ℝ)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (Cu Cv : ℝ≥0∞) (hCu : Cu < ⊤) (hCv : Cv < ⊤)
    (he : Tendsto e l (𝓝 0)) (hepos : ∀ᶠ i in l, 0 < e i)
    (hf : ∀ᶠ i in l, AEMeasurable (f i) P)
    (hfin : ∀ᶠ i in l, ∀ᵐ ω ∂P, 0 < f i ω ∧ f i ω < ⊤)
    (huBound : ∀ᶠ i in l, ∫⁻ ω, f i ω ^ u ∂P ≤ Cu)
    (hvBound : ∀ᶠ i in l, ∫⁻ ω, f i ω ^ (-v) ∂P ≤ Cv) :
    Tendsto (fun i => (∫⁻ ω, f i ω ^ e i ∂P).toReal) l (𝓝 1) := by
  have hsmall : ∀ᶠ i in l, e i ≤ u := he.eventually (eventually_le_nhds hu)
  have hbounds : ∀ᶠ i in l,
      1 - e i / v * Cv.toReal ≤ (∫⁻ ω, f i ω ^ e i ∂P).toReal ∧
      (∫⁻ ω, f i ω ^ e i ∂P).toReal ≤ 1 + e i / u * Cu.toReal := by
    filter_upwards [hepos, hsmall, hf, hfin, huBound, hvBound]
      with i hpi hpu hfi hfinite hUi hVi
    have hpow (p : ℝ) : AEMeasurable (fun ω => f i ω ^ p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfi
    have hpoint (ω : Ω) (hω : 0 < f i ω ∧ f i ω < ⊤) :
        f i ω ^ e i ≤ 1 + ENNReal.ofReal (e i / u) * f i ω ^ u ∧
        1 ≤ f i ω ^ e i + ENNReal.ofReal (e i / v) * f i ω ^ (-v) := by
      have hx : 0 < (f i ω).toReal := ENNReal.toReal_pos hω.1.ne' hω.2.ne
      have hrep (p : ℝ) : ENNReal.ofReal ((f i ω).toReal ^ p) = f i ω ^ p := by
        rw [← ENNReal.ofReal_rpow_of_pos hx, ENNReal.ofReal_toReal hω.2.ne]
      constructor
      · have h := ENNReal.ofReal_le_ofReal (lastone_rpow_le_one_add
          (f i ω).toReal (e i) u hx.le hpi hpu)
        rw [hrep, ENNReal.ofReal_add (by norm_num) (by positivity),
          ENNReal.ofReal_one, ENNReal.ofReal_mul (by positivity), hrep] at h
        exact h
      · have h := ENNReal.ofReal_le_ofReal (lastone_one_le_rpow_add
          (f i ω).toReal (e i) v hx hpi.le hv)
        rw [ENNReal.ofReal_one, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), hrep, hrep] at h
        exact h
    have hupper : (∫⁻ ω, f i ω ^ e i ∂P) ≤ 1 + ENNReal.ofReal (e i / u) * Cu := by
      calc
        _ ≤ ∫⁻ ω, 1 + ENNReal.ofReal (e i / u) * f i ω ^ u ∂P :=
          lintegral_mono_ae (hfinite.mono fun ω hω => (hpoint ω hω).1)
        _ = 1 + ENNReal.ofReal (e i / u) * ∫⁻ ω, f i ω ^ u ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            measure_univ, mul_one, lintegral_const_mul'' _ (hpow u)]
        _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl hUi)
    have htop : 1 + ENNReal.ofReal (e i / u) * Cu ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCu).ne⟩
    have hItop := ne_top_of_le_ne_top htop hupper
    have hlower : 1 ≤ (∫⁻ ω, f i ω ^ e i ∂P) + ENNReal.ofReal (e i / v) * Cv := by
      calc
        1 = ∫⁻ _ : Ω, 1 ∂P := by simp
        _ ≤ ∫⁻ ω, f i ω ^ e i + ENNReal.ofReal (e i / v) * f i ω ^ (-v) ∂P :=
          lintegral_mono_ae (hfinite.mono fun ω hω => (hpoint ω hω).2)
        _ = (∫⁻ ω, f i ω ^ e i ∂P) +
            ENNReal.ofReal (e i / v) * ∫⁻ ω, f i ω ^ (-v) ∂P := by
          rw [lintegral_add_left' (hpow (e i)), lintegral_const_mul'' _ (hpow (-v))]
        _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl hVi)
    have hupperR := ENNReal.toReal_mono htop hupper
    have hlowerTop : (∫⁻ ω, f i ω ^ e i ∂P) + ENNReal.ofReal (e i / v) * Cv ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hItop,
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCv).ne⟩
    have hlowerR := ENNReal.toReal_mono hlowerTop hlower
    rw [ENNReal.toReal_add ENNReal.one_ne_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCu).ne,
      ENNReal.toReal_one, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hpi.le hu.le)] at hupperR
    rw [ENNReal.toReal_one, ENNReal.toReal_add hItop
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCv).ne, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hpi.le hv.le)] at hlowerR
    exact ⟨by linarith, hupperR⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun i => 1 - e i / v * Cv.toReal)
    (h := fun i => 1 + e i / u * Cu.toReal)
  · simpa using tendsto_const_nhds.sub ((he.div_const v).mul_const Cv.toReal)
  · simpa using tendsto_const_nhds.add ((he.div_const u).mul_const Cu.toReal)
  · exact hbounds.mono fun i hi => hi.1
  · exact hbounds.mono fun i hi => hi.2

end DOZZ.Proofs
