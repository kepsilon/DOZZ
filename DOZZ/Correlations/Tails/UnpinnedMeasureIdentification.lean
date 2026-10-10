/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TransferredMeasure
public import DOZZ.GMC.AdmissibleGMCUniqueConcrete

/-! Almost-sure measure identification of the translated unpinned chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Pin removal identifies the whole random measure on one common probability-one event.
Consequently the identity applies simultaneously to singular and random measurable integrands. -/
theorem unpinned_source_measure_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (Metric.ball 0 1) (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ N) :
    ∀ᵐ ω ∂P, N ω = transferredMeasure (M ω) z γ (Xc ω z 0) := by
  let U : Set ℂ := Metric.ball 0 1
  obtain ⟨K, hKcompact, hKU, _, _, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests U Metric.isOpen_ball
  have hEach : ∀ nm : ℕ × ℕ,
      (fun ω => ∫ x, f nm x ∂N ω) =ᵐ[P]
        fun ω => ∫ x, f nm x ∂transferredMeasure (M ω) z γ (Xc ω z 0) := by
    intro nm
    obtain ⟨g, _, hg, he⟩ := unpinned_source_compact_test P X Xc hX hc z hz γ
      M hM N hN (f nm) (hf nm.1 nm.2).1 (hf nm.1 nm.2).2.2
    filter_upwards [he] with ω hω
    exact hω.trans (transferred_measure_test_integral (M ω) z γ (Xc ω z 0)
      (f nm) g (hf nm.1 nm.2).2.2 hg).symm
  filter_upwards [ae_all_iff.mpr hEach] with ω hω
  let : IsFiniteMeasure (M ω) := hM.1 ω
  let : IsFiniteMeasure (transferredMeasure (M ω) z γ (Xc ω z 0)) :=
    transferred_measure_finite (M ω) z γ (Xc ω z 0)
  exact admissible_countable_tests_determine_chart_measures U Metric.isOpen_ball (N ω)
    (transferredMeasure (M ω) z γ (Xc ω z 0))
    (hN.2.1 ω) (transferred_measure_carried (M ω) z γ (Xc ω z 0))
    (fun L hL hLU => hN.2.2.1 ω L hL hLU)
    (fun L _ _ => measure_lt_top _ _)
    K hKcompact hKU hKcofinal f
    (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩)
    hdense (fun n m => hω (n,m))


end DOZZ.Proofs
