/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.L1CauchyMeasureLimit

/-! Uniform Fatou passage from cutoff-to-cutoff L¹ Cauchy bounds to a specified limit. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- A family of cutoff observables that is uniformly Cauchy in L¹ and converges in measure
coordinatewise converges uniformly in L¹ to those specified limits. -/
theorem tendsto_iSup_lintegral_abs_sub_of_uniform_l1_cauchy
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : ℝ → ι → Ω → ℝ) (G : ι → Ω → ℝ)
    (hFmeas : ∀ r i, Measurable (F r i))
    (hFG : ∀ i, TendstoInMeasure P (fun r => F r i) atTop (G i))
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ r ≥ R, ∀ s ≥ R, ∀ i,
      ∫⁻ ω, ENNReal.ofReal |F r i ω - F s i ω| ∂P < ENNReal.ofReal ε) :
    Tendsto (fun r : ℝ => ⨆ i,
      ∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro δ hδ
  let η : ℝ≥0∞ := min δ 1
  have hηpos : 0 < η := lt_min hδ one_pos
  have hηtop : η ≠ ∞ := ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
  have hηeq : ENNReal.ofReal η.toReal = η := ENNReal.ofReal_toReal hηtop
  have hηrealpos : 0 < η.toReal := ENNReal.toReal_pos hηpos.ne' hηtop
  obtain ⟨R, hR⟩ := hCauchy (η.toReal / 2) (by positivity)
  have hsmall : ENNReal.ofReal (η.toReal / 2) < η := by
    calc
      ENNReal.ofReal (η.toReal / 2) < ENNReal.ofReal η.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hηrealpos).2 (by linarith)
      _ = η := hηeq
  have hEventually : ∀ᶠ r : ℝ in atTop,
      (⨆ i, ∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P) < δ := by
    filter_upwards [eventually_ge_atTop R] with r hr
    have hbound (i : ι) :
        ∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P ≤
          ENNReal.ofReal (η.toReal / 2) := by
      apply lintegral_abs_sub_limit_le_of_uniform_l1_cauchy
        P (fun t ω => F t i ω) (G i) (fun t => hFmeas t i) (hFG i) r R
        (η.toReal / 2)
      intro s hs
      exact (hR r hr s hs i).le
    have hsup : (⨆ i, ∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P) ≤
        ENNReal.ofReal (η.toReal / 2) := iSup_le hbound
    exact lt_of_le_of_lt hsup (lt_of_lt_of_le hsmall (min_le_left _ _))
  filter_upwards [hEventually] with r hr
  exact hr.le

end DOZZ.Proofs
