/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WeakConvMixed
public import DOZZ.FourPoint.BPZ.NoAtoms
public import DOZZ.GMC.SharpMoments.WeightedTransfer

/-! # The cutoff chaos converges weakly in probability

Along integer cutoffs, the circle-average chaos converges to the limit chaos in `L¹` against every
bounded measurable test function with bounded support. Replacing the cutoff chaos by the zero
measure on the null event where its total mass is infinite gives a sequence of finite random
measures converging weakly in probability in the sense of `BPZWeakConv`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cutoff chaos, replaced by the zero measure where its total mass is infinite. -/
noncomputable def bpzCutChaos (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) :
    Measure ℂ :=
  if regularizedGMC P Xc γ r ω Set.univ < ⊤ then regularizedGMC P Xc γ r ω else 0

theorem bpzCutChaos_isFiniteMeasure (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) :
    IsFiniteMeasure (bpzCutChaos P Xc γ r ω) := by
  unfold bpzCutChaos
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

theorem measurable_bpzCutChaos (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) :
    Measurable (bpzCutChaos P Xc γ r) := by
  have hm := regularizedGMC_measurable P X hX Xc hXc γ r
  have hs : MeasurableSet {ω | regularizedGMC P Xc γ r ω Set.univ < ⊤} :=
    measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp hm) measurable_const
  exact Measurable.ite hs hm measurable_const

theorem bpzCutChaos_ae_eq (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) :
    ∀ᵐ ω ∂P, bpzCutChaos P Xc γ r ω = regularizedGMC P Xc γ r ω := by
  filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
  unfold bpzCutChaos
  exact ite_eq_left hω.measure_univ_lt_top

/-- The integer-cutoff chaos converges weakly in probability to the limit chaos. -/
theorem bpzWeakConv_gmc (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMm : Measurable M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    BPZWeakConv P (fun n => bpzCutChaos P Xc γ n) M where
  meas n := measurable_bpzCutChaos P X hX Xc hXc γ n
  meas₀ := hMm
  fin n ω := bpzCutChaos_isFiniteMeasure P Xc γ n ω
  fin₀ := hM.1
  conv f hf C R hfb hfs := by
    have hl1 := regularizedGMC_integral_l1_tendsto P X hX γ hγ hγ2 M hM Xc hXc f hf C hfb R
      (fun x hx => hfs x (by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
        exact hx))
    have hl1n := hl1.comp tendsto_natCast_atTop_atTop
    have hcongr : ∀ n : ℕ, (fun ω => ∫ x, f x ∂bpzCutChaos P Xc γ n ω) =ᵐ[P]
        fun ω => ∫ x, f x ∂regularizedGMC P Xc γ n ω := by
      intro n
      filter_upwards [bpzCutChaos_ae_eq P X hX Xc hXc γ n] with ω hω
      rw [hω]
    refine TendstoInMeasure.congr_left (fun n => (hcongr n).symm) ?_
    exact DOZZ.Assembly.tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P _ _
      (fun n => ((measurable_integral_measure hf).comp
        (regularizedGMC_measurable P X hX Xc hXc γ n)).aestronglyMeasurable)
      ((measurable_integral_measure hf).comp hMm).aestronglyMeasurable hl1n

end DOZZ.Proofs
