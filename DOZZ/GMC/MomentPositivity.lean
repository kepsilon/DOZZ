/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment

/-! A finite negative mass moment rules out zero mass almost surely. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- A finite negative moment and an a.e.-measurable mass imply almost-sure positivity. -/
theorem gmcMass_positive_ae_of_finite_negative_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (A : Set ℂ)
    (hM : AEMeasurable (fun ω => M ω A) P) (q : ℝ) (hq : 0 < q)
    (hfinite : gmcMassMoment P M A (-q) < ⊤) :
    ∀ᵐ ω ∂P, 0 < M ω A := by
  let s : Set Ω := {ω | M ω A = 0}
  have hs_eq : s = (fun ω => M ω A) ⁻¹' ({0} : Set ℝ≥0∞) := by
    ext ω
    simp [s]
  have hs : NullMeasurableSet s P := by
    rw [hs_eq]
    exact hM.nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ≥0∞))
  have hnull : P s = 0 := by
    by_contra hn
    have hpoint (ω : Ω) : s.indicator (fun _ => (⊤ : ℝ≥0∞)) ω ≤
        ENNReal.rpow (M ω A) (-q) := by
      by_cases hω : ω ∈ s
      · have hz : M ω A = 0 := hω
        rw [Set.indicator_of_mem hω, hz]
        change (⊤ : ℝ≥0∞) ≤ (0 : ℝ≥0∞) ^ (-q)
        rw [ENNReal.zero_rpow_of_neg (neg_neg_of_pos hq)]
      · rw [Set.indicator_of_notMem hω]
        exact zero_le
    have hInt := lintegral_mono_ae (μ := P) (Filter.Eventually.of_forall hpoint)
    have htop : (⊤ : ℝ≥0∞) ≤ gmcMassMoment P M A (-q) := by
      rw [gmcMassMoment]
      calc
        ⊤ = (⊤ : ℝ≥0∞) * P s := by simp [hn]
        _ = ∫⁻ ω, s.indicator (fun _ => (⊤ : ℝ≥0∞)) ω ∂P := by
          rw [lintegral_indicator_const₀ hs]
        _ ≤ ∫⁻ ω, ENNReal.rpow (M ω A) (-q) ∂P := hInt
    exact (not_lt_of_ge htop) hfinite
  have hne : ∀ᵐ ω ∂P, M ω A ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 hnull] with ω hω
    simpa only [s, Set.mem_compl_iff, Set.mem_ofPred_eq] using hω
  filter_upwards [hne] with ω hω
  exact lt_of_le_of_ne (show 0 ≤ M ω A from zero_le) (Ne.symm hω)

end DOZZ.Proofs
