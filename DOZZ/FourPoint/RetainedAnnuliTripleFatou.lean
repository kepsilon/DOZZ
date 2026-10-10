/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliFatou

/-! Fatou for two retained annuli and a separated fixed disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Three cutoff masses converging in measure admit a common almost sure subsequence. -/
theorem three_mass_fatou
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f₀ f₁ f₂ : ℕ → Ω → ℝ) (g₀ g₁ g₂ : Ω → ℝ) (p q v : ℝ)
    (hf₀ : TendstoInMeasure P f₀ atTop g₀) (hf₁ : TendstoInMeasure P f₁ atTop g₁)
    (hf₂ : TendstoInMeasure P f₂ atTop g₂)
    (hmeas : ∀ n, AEMeasurable (fun ω =>
      (ENNReal.ofReal (f₀ n ω)) ^ p * (ENNReal.ofReal (f₁ n ω)) ^ q *
        (ENNReal.ofReal (f₂ n ω)) ^ v) P)
    (hg₀ : ∀ᵐ ω ∂P, 0 < g₀ ω) (hg₁ : ∀ᵐ ω ∂P, 0 < g₁ ω) (hg₂ : ∀ᵐ ω ∂P, 0 < g₂ ω)
    (R : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (hR : Tendsto R atTop (nhds C))
    (hbound : ∀ n, (∫⁻ ω, (ENNReal.ofReal (f₀ n ω)) ^ p * (ENNReal.ofReal (f₁ n ω)) ^ q *
      (ENNReal.ofReal (f₂ n ω)) ^ v ∂P) ≤ R n) :
    (∫⁻ ω, (ENNReal.ofReal (g₀ ω)) ^ p * (ENNReal.ofReal (g₁ ω)) ^ q *
      (ENNReal.ofReal (g₂ ω)) ^ v ∂P) ≤ C := by
  obtain ⟨s, hs, hsub₀⟩ := hf₀.exists_seq_tendsto_ae
  obtain ⟨t, ht, hsub₁⟩ := (hf₁.comp hs.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨u, hu, hsub₂⟩ :=
    (hf₂.comp (hs.tendsto_atTop.comp ht.tendsto_atTop)).exists_seq_tendsto_ae
  let ns : ℕ → ℕ := fun n => s (t (u n))
  have hns : Tendsto ns atTop atTop :=
    hs.tendsto_atTop.comp (ht.tendsto_atTop.comp hu.tendsto_atTop)
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    (ENNReal.ofReal (f₀ (ns n) ω)) ^ p * (ENNReal.ofReal (f₁ (ns n) ω)) ^ q *
      (ENNReal.ofReal (f₂ (ns n) ω)) ^ v
  have hlim : ∀ᵐ ω ∂P, liminf (fun n => F n ω) atTop =
      (ENNReal.ofReal (g₀ ω)) ^ p * (ENNReal.ofReal (g₁ ω)) ^ q * (ENNReal.ofReal (g₂ ω)) ^ v := by
    filter_upwards [hsub₀, hsub₁, hsub₂, hg₀, hg₁, hg₂] with ω h₀ h₁ h₂ hg₀ hg₁ hg₂
    have he₀ : Tendsto (fun n => (ENNReal.ofReal (f₀ (ns n) ω)) ^ p) atTop
        (nhds ((ENNReal.ofReal (g₀ ω)) ^ p)) := ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (h₀.comp (ht.tendsto_atTop.comp hu.tendsto_atTop)))
    have he₁ : Tendsto (fun n => (ENNReal.ofReal (f₁ (ns n) ω)) ^ q) atTop
        (nhds ((ENNReal.ofReal (g₁ ω)) ^ q)) := ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (h₁.comp hu.tendsto_atTop))
    have he₂ : Tendsto (fun n => (ENNReal.ofReal (f₂ (ns n) ω)) ^ v) atTop
        (nhds ((ENNReal.ofReal (g₂ ω)) ^ v)) := ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp h₂)
    have hn₀ : (ENNReal.ofReal (g₀ ω)) ^ p ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hg₀).ne' ENNReal.ofReal_ne_top
    have hn₁ : (ENNReal.ofReal (g₁ ω)) ^ q ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hg₁).ne' ENNReal.ofReal_ne_top
    have hn₂ : (ENNReal.ofReal (g₂ ω)) ^ v ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hg₂).ne' ENNReal.ofReal_ne_top
    have he₀₁ := ENNReal.Tendsto.mul he₀ (Or.inr hn₁) he₁ (Or.inr hn₀)
    exact (ENNReal.Tendsto.mul he₀₁ (Or.inr hn₂) he₂
      (Or.inr (ENNReal.mul_ne_top hn₀ hn₁))).liminf_eq
  calc
    _ = ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P :=
      lintegral_congr_ae (hlim.mono fun _ h => h.symm)
    _ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop :=
      lintegral_liminf_le' (fun n => hmeas (ns n))
    _ ≤ liminf (fun n => R (ns n)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall fun n => hbound (ns n))
    _ = C := (hR.comp hns).liminf_eq

end DOZZ.Proofs
