/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.EntranceLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded measurable tests for the entrance density limit

The finite Doob densities converge pointwise to the entrance density and both have unit mass.
Their overlap therefore tends to one, which upgrades pointwise convergence to convergence against
every bounded measurable test. This includes arbitrary Borel cylinder events, without a boundary
regularity restriction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Probability densities converging pointwise transport every bounded measurable test. -/
theorem tendsto_lintegral_probabilityDensity_test
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (f : ℕ → E → ℝ≥0∞) (g : E → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfm : ∀ n, (∫⁻ x, f n x ∂μ) = 1) (hgm : (∫⁻ x, g x ∂μ) = 1)
    (hfg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (F : E → ℝ≥0∞) (hF : Measurable F)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ x, F x ≤ K) :
    Tendsto (fun n => ∫⁻ x, f n x * F x ∂μ) atTop
      (𝓝 (∫⁻ x, g x * F x ∂μ)) := by
  let A : ℕ → E → ℝ≥0∞ := fun n x => min (f n x) (g x)
  have hA (n : ℕ) : Measurable (A n) := (hf n).min hg
  have hAm (n : ℕ) : (∫⁻ x, A n x ∂μ) ≠ ∞ := ne_top_of_le_ne_top
    (hgm ▸ ENNReal.one_ne_top) (lintegral_mono (fun x => min_le_right _ _))
  have hAlim (x : E) : Tendsto (fun n => A n x) atTop (𝓝 (g x)) := by
    simpa only [min_self] using (hfg x).min (tendsto_const_nhds (x := g x))
  have hJ : Tendsto (fun n => ∫⁻ x, A n x ∂μ) atTop (𝓝 1) := by
    rw [← hgm]
    exact tendsto_lintegral_of_dominated_convergence g hA
      (fun n => ae_of_all _ (fun x => min_le_right _ _))
      (hgm ▸ ENNReal.one_ne_top) (ae_of_all _ hAlim)
  have hKg : Measurable (fun x => K * g x) := measurable_const.mul hg
  have hKgfin : (∫⁻ x, K * g x ∂μ) ≠ ∞ := by
    rw [lintegral_const_mul K hg, hgm, mul_one]
    exact hK
  have hAP (n : ℕ) : Measurable (fun x => A n x * F x) := (hA n).mul hF
  have hT : Tendsto (fun n => ∫⁻ x, A n x * F x ∂μ) atTop
      (𝓝 (∫⁻ x, g x * F x ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun x => K * g x) hAP ?_
      hKgfin ?_
    · intro n
      exact ae_of_all _ (fun x =>
        (mul_le_mul' (min_le_right _ _) (hbound x)).trans_eq (mul_comm _ _))
    · filter_upwards [ae_lt_top hg (hgm ▸ ENNReal.one_ne_top)] with x hx
      exact ENNReal.Tendsto.mul (hAlim x)
        (Or.inr (ne_top_of_le_ne_top hK (hbound x)))
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => F x) atTop (𝓝 (F x)))
        (Or.inr hx.ne)
  have hres : Tendsto (fun n => K * (1 - ∫⁻ x, A n x ∂μ)) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hJ
        (Or.inl ENNReal.one_ne_top)) (Or.inr hK)
    simpa only [tsub_self, mul_zero] using hh
  have hupper (n : ℕ) : (∫⁻ x, f n x * F x ∂μ) ≤
      (∫⁻ x, A n x * F x ∂μ) + K * (1 - ∫⁻ x, A n x ∂μ) := by
    have hdecomp : (fun x => f n x * F x) =
        (fun x => A n x * F x + (f n x - A n x) * F x) := by
      funext x
      rw [← add_mul, add_tsub_cancel_of_le (min_le_left _ _)]
    rw [hdecomp, lintegral_add_left (hAP n)]
    apply add_le_add le_rfl
    calc
      _ ≤ ∫⁻ x, K * (f n x - A n x) ∂μ :=
        lintegral_mono (fun x =>
          (mul_le_mul' le_rfl (hbound x)).trans_eq (mul_comm _ _))
      _ = K * (1 - ∫⁻ x, A n x ∂μ) := by
        have hm : Measurable (fun x => f n x - A n x) := (hf n).sub (hA n)
        rw [lintegral_const_mul K hm,
          lintegral_sub (hA n) (hAm n)
            (ae_of_all _ (fun x => min_le_left _ _)), hfm n]
  have hI : (∫⁻ x, g x * F x ∂μ) ≤ K := by
    calc
      _ ≤ ∫⁻ x, K * g x ∂μ := lintegral_mono (fun x =>
        (mul_le_mul' le_rfl (hbound x)).trans_eq (mul_comm _ _))
      _ = K := by rw [lintegral_const_mul K hg, hgm, mul_one]
  have htop : Tendsto
      (fun n => (∫⁻ x, A n x * F x ∂μ) + K * (1 - ∫⁻ x, A n x ∂μ))
      atTop (𝓝 (∫⁻ x, g x * F x ∂μ)) := by
    simpa only [add_zero] using hT.add hres
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hT htop
    (fun n => lintegral_mono (fun x =>
      mul_le_mul' (min_le_left _ _) le_rfl)) hupper

/-- The finite Doob density converges to the entrance density against any bounded measurable
test along positive starting states tending to zero. -/
theorem brownianDoobFinitePDF_lintegral_tendsto_entrance_test
    (P Q : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ ys, F ys ≤ K) :
    Tendsto
      (fun k => ∫⁻ ys, brownianDoobFinitePDF ν n ds (xs k) ys * F ys
        ∂(volume : Measure (Fin n → ℝ)))
      atTop
      (𝓝 (∫⁻ ys, brownianEntranceFinitePDF ν n ds ys * F ys
        ∂(volume : Measure (Fin n → ℝ)))) := by
  have hwithin : Tendsto xs atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hxlim, Filter.Eventually.of_forall hxs⟩
  exact tendsto_lintegral_probabilityDensity_test
    (volume : Measure (Fin n → ℝ))
    (fun k ys => brownianDoobFinitePDF ν n ds (xs k) ys)
    (brownianEntranceFinitePDF ν n ds)
    (fun k => measurable_brownianDoobFinitePDF ν hν n ds hds (xs k) (hxs k))
    (measurable_brownianEntranceFinitePDF ν hν n ds hds)
    (fun k => lintegral_brownianDoobFinitePDF_one P hB ν hν n ds hds
      (xs k) (hxs k))
    (lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds)
    (fun ys => (brownianDoobFinitePDF_tendsto_entrance ν hν n ds hds ys).comp hwithin)
    F hF K hK hbound

/-- The finite Doob probability measures converge on every measurable set to the entrance
finite-dimensional law. -/
theorem brownianDoobFinitePDF_measure_tendsto_entrance_event
    (P Q : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    Tendsto
      (fun k => (volume.withDensity (brownianDoobFinitePDF ν n ds (xs k))) A)
      atTop
      (𝓝 ((volume.withDensity (brownianEntranceFinitePDF ν n ds)) A)) := by
  have htest := brownianDoobFinitePDF_lintegral_tendsto_entrance_test
    P Q hB ν hν hQ n ds hds xs hxs hxlim
    (A.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hA) 1 ENNReal.one_ne_top
    (fun ys => by
      by_cases hy : ys ∈ A <;> simp [hy])
  have hleft (k : ℕ) :
      (volume.withDensity (brownianDoobFinitePDF ν n ds (xs k))) A =
        ∫⁻ ys, brownianDoobFinitePDF ν n ds (xs k) ys *
          A.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)) ys ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr
    intro ys
    by_cases hy : ys ∈ A <;> simp [hy]
  have hright :
      (volume.withDensity (brownianEntranceFinitePDF ν n ds)) A =
        ∫⁻ ys, brownianEntranceFinitePDF ν n ds ys *
          A.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)) ys ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr
    intro ys
    by_cases hy : ys ∈ A <;> simp [hy]
  simpa only [hleft, hright] using htest

end DOZZ.Proofs

end
