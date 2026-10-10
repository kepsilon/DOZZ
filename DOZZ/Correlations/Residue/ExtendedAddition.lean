/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ExtendedMoment

/-! Uniform higher moments justify the complete extended-real addition step. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Adding a uniformly higher-integrable extended mass preserves the moment
residue. All real/extended conversions and finiteness conditions are proved explicitly. -/
theorem residue_extended_addition_preserves_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A R : ℝ → Ω → ℝ≥0∞) (β γ d₀ r L : ℝ) (K : ℝ≥0∞)
    (hβ : 0 < β) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdβ : d₀ ≤ γ * β)
    (hβr : β < r) (hK : K < ⊤)
    (hA : ∀ d, 0 < d → d < d₀ → AEMeasurable (A d) P)
    (hR : ∀ d, 0 < d → d < d₀ → AEMeasurable (R d) P)
    (hAfin : ∀ d, 0 < d → d < d₀ → ∀ᵐ ω ∂P, A d ω ≠ ⊤)
    (hiA : ∀ d, 0 < d → d < d₀ → Integrable (fun ω => (A d ω).toReal ^ (β - d / γ)) P)
    (hRbound : ∀ d, 0 < d → d < d₀ → ∫⁻ ω, ENNReal.rpow (R d ω) r ∂P ≤ K)
    (hlim : Tendsto (fun d => d * ∫ ω, (A d ω).toReal ^ (β - d / γ) ∂P)
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun d => d * (∫⁻ ω, ENNReal.rpow (A d ω + R d ω) (β - d / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 L) := by
  have hr : 0 < r := hβ.trans hβr
  have hq (d : ℝ) (hd : 0 < d) (hd' : d < d₀) : 0 < β - d / γ ∧ β - d / γ < β := by
    have hh : d / γ < β := (div_lt_iff₀ hγ).mpr (by simpa only [mul_comm] using hd'.trans_le hdβ)
    exact ⟨sub_pos.mpr hh, sub_lt_self _ (div_pos hd hγ)⟩
  have hRp (d : ℝ) (hd : 0 < d) (hd' : d < d₀) :=
    residue_real_moment_of_extended_bound P (R d) (hR d hd hd') r hr
      ((hRbound d hd hd').trans_lt hK).ne
  have hRlower (d : ℝ) (hd : 0 < d) (hd' : d < d₀) :
      Integrable (fun ω => (R d ω).toReal ^ (β - d / γ)) P ∧
        (∫ ω, (R d ω).toReal ^ (β - d / γ) ∂P) ≤ 1 + K.toReal := by
    have hh := residue_integral_lower_power_le P (fun ω => (R d ω).toReal)
      (ENNReal.measurable_toReal.comp_aemeasurable (hR d hd hd'))
      (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
      (β - d / γ) r (hq d hd hd').1.le ((hq d hd hd').2.trans hβr).le (hRp d hd hd').2.1
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [(hRp d hd hd').2.2]
    exact add_le_add le_rfl (ENNReal.toReal_mono hK.ne (hRbound d hd hd'))
  have hadd := residue_addition_preserves_limit P (fun d ω => (A d ω).toReal)
    (fun d ω => (R d ω).toReal) (fun d => β - d / γ) β d₀ (1 + K.toReal) L hd₀
    (fun d hd hd' => ENNReal.measurable_toReal.comp_aemeasurable (hA d hd hd'))
    (fun d hd hd' => ENNReal.measurable_toReal.comp_aemeasurable (hR d hd hd'))
    (fun _ _ _ => ae_of_all _ fun _ => ENNReal.toReal_nonneg)
    (fun _ _ _ => ae_of_all _ fun _ => ENNReal.toReal_nonneg)
    (fun d hd hd' => ⟨(hq d hd hd').1.le, (hq d hd hd').2.le⟩)
    hiA (fun d hd hd' => (hRlower d hd hd').1) (fun d hd hd' => (hRlower d hd hd').2) hlim
  have hnear : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < d₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.eventually_of_mem (Iio_mem_nhds hd₀) (fun _ h => h)).filter_mono nhdsWithin_le_nhds]
      with d hd hd'
    exact ⟨hd, hd'⟩
  apply hadd.congr'
  filter_upwards [hnear] with d hd
  congr 1
  have hfin : ∀ᵐ ω ∂P, A d ω + R d ω ≠ ⊤ :=
    (hAfin d hd.1 hd.2).and (hRp d hd.1 hd.2).1 |>.mono (fun _ hh => ENNReal.add_ne_top.mpr hh)
  rw [← residue_integral_toReal_rpow P (fun ω => A d ω + R d ω)
    ((hA d hd.1 hd.2).add (hR d hd.1 hd.2)) hfin (β - d / γ) (hq d hd.1 hd.2).1.le]
  apply integral_congr_ae
  filter_upwards [hAfin d hd.1 hd.2, (hRp d hd.1 hd.2).1] with ω ha hr
  rw [ENNReal.toReal_add ha hr]

end DOZZ.Proofs
