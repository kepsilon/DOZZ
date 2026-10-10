/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
public import DOZZ.GMC.Moments.SubunitLimit

/-! Subunit moments of arbitrary GMC masses, localized by measure monotonicity. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every measurable or nonmeasurable set mass is bounded in subunit moment by the total mass;
the measure-mono argument is pointwise and does not require measurability of the set evaluation. -/
theorem gmc_mass_subunit_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (O : Set ℂ)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gmcMassMoment P M O p ≤ 1 + gmcReferenceMeasure Set.univ := by
  unfold gmcMassMoment
  calc
    ∫⁻ ω, ENNReal.rpow (M ω O) p ∂P ≤
        ∫⁻ ω, ENNReal.rpow (M ω Set.univ) p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow (measure_mono (Set.subset_univ O)) hp0
    _ ≤ 1 + gmcReferenceMeasure Set.univ :=
      gmc_total_mass_subunit_moment_bound P X hX γ M hM hp0 hp1

/-- The sharp unweighted moment criterion is already exact on its subunit interval: for every
`IsGMCOf` version, all set masses have finite positive moments of order at most one. -/
theorem gmc_mass_moment_finite_iff_on_subunit_interval
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (O : Set ℂ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (gmcMassMoment P M O p < ⊤) ↔ p < 4 / γ ^ 2 := by
  have hthreshold : p < 4 / γ ^ 2 := by
    have hγsq : γ ^ 2 < 4 := by nlinarith
    have hdiv : 1 < 4 / γ ^ 2 := by
      rw [one_lt_div (sq_pos_of_pos hγ)]
      nlinarith
    exact hp1.trans_lt hdiv
  constructor
  · intro _
    exact hthreshold
  · intro _
    have hbound := gmc_mass_subunit_moment_bound P X hX γ M hM O hp0.le hp1
    have href : gmcReferenceMeasure Set.univ < ⊤ :=
      gmcReferenceMeasure_univ_ne_top.lt_top
    have hsum : 1 + gmcReferenceMeasure Set.univ < ⊤ :=
      ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, href⟩
    exact lt_of_le_of_lt hbound hsum

end DOZZ.Proofs
